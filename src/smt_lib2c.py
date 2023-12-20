# The last part of the example requires a QF_LIA solver to be installed.
#
#
# This example shows how to interact with files in the SMT-LIB
# format. In particular:
#
# 1. How to read a file in SMT-LIB format
# 2. How to write a file in SMT-LIB format
# 3. Formulas and SMT-LIB script
# 4. How to access annotations from SMT-LIB files
#
import re
import time
import typing
from dataclasses import dataclass
from io import StringIO
from typing import Generator, Iterable, Tuple

import pycparser.c_generator
import pysmt.typing
from pycparser import c_ast
from pysmt import environment
from pysmt.fnode import FNode
from pysmt.smtlib import commands
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand

EXIT = SmtLibCommand('exit', [])
node_or_list = typing.TypeVar('node_or_list', c_ast.Node, list[c_ast.Node])


def commands2script(commands: list[SmtLibCommand]) -> SmtLibScript:
    script = SmtLibScript()
    script.commands = commands
    return script


def without_push(scripts: SmtLibScript | Iterable[SmtLibScript]) -> Generator[SmtLibScript, None, None]:
    """
    :param scripts: one or more smt lib scripts
    :return: one script for each program generated by push and pop
    """
    if isinstance(scripts, SmtLibScript):
        scripts = scripts,

    for script in scripts:
        pushes = []
        commands = []
        for command in script:
            if command.name == 'push':
                pushes.append(len(commands))
            elif command.name == 'pop':
                yield commands2script(commands + [EXIT])
                commands = commands[:pushes.pop(-1)]
            else:
                commands.append(command)
        yield commands2script(commands)


def one_check_sat(scripts: SmtLibScript | Iterable[SmtLibScript]) -> Generator[SmtLibScript, None, None]:
    """
    :param scripts: one or more smt lib scripts
    :return: one script for each check-sat in scripts
    """
    if isinstance(scripts, SmtLibScript):
        scripts = scripts,

    for script in scripts:
        pushes = []
        commands = []
        for command in script:
            if command.name == 'check-sat':
                yield commands2script(commands + [command, EXIT])
            elif command.name == 'push':
                pushes.append(len(commands))
            elif command.name == 'pop':
                commands = commands[:pushes.pop(-1)]
            else:
                commands.append(command)


def nested_binary_op(op: str, *args: c_ast.Node):
    """
    Builds any amount of binary operators to accommodate any number of arguments.
    For example nested_binary_op("&&", arg1, arg2, arg3) will result in the AST of (arg1 && (arg2 && arg3)).
    """
    if len(args) <= 0:
        raise ValueError('needs at least one argument')
    if len(args) == 1:
        return args[0]
    return c_ast.BinaryOp(op, args[0], nested_binary_op(op, *args[1:]))


SMT2C_SIZE_NAME_DICT = {
    pysmt.typing.BV8: 'char',
    pysmt.typing.BV16: 'short',
    pysmt.typing.BV32: 'int',
    pysmt.typing.BV64: 'long long'
}


def identifier_c_type(name: str) -> tuple[c_ast.IdentifierType, c_ast.FuncCall]:
    """
    :return: Both the c type for this name and a call to its nondet function
    """
    return (
        c_ast.IdentifierType([name]),
        c_ast.FuncCall(c_ast.ID(f'__VERIFIER_nondet_{name.replace(" ", "")}'), None)
    )


C_BOOL_TYPE = identifier_c_type('char')
C_BOOL_TYPE = C_BOOL_TYPE[0], c_ast.BinaryOp('==', C_BOOL_TYPE[1], c_ast.Constant('char', '1'))
SMT2C_TYPE_DICT = {
    pysmt.typing.BOOL: C_BOOL_TYPE,
    pysmt.typing.BV1: C_BOOL_TYPE
} | {
    smt_type: identifier_c_type(c_type_name) for smt_type, c_type_name in SMT2C_SIZE_NAME_DICT.items()
}


def to_c_declaration(command: SmtLibCommand, new_c_name, allow_exceptions=True) -> c_ast.Decl:
    """
    :return: The C AST for the declaration matching the SmtLib type
    """
    variable = command.args[0]
    name = new_c_name(variable.symbol_name())
    smt_type = variable.symbol_type()
    try:
        c_type, c_init = SMT2C_TYPE_DICT[smt_type]
    except KeyError:
        # TODO: implement cases when we land here
        if allow_exceptions:
            raise ValueError('Unsupported type', smt_type)
        c_type, c_init = identifier_c_type(f'unsupported_type({smt_type})')
    return c_ast.Decl(name, [], [], [], [], c_ast.TypeDecl(name, [], None, c_type), c_init, None)


@dataclass
class Info:
    smt_type: pysmt.typing.PySMTType


BOOL_INFO = Info(pysmt.typing.BV1)


def cast(node: c_ast.Node, info: Info, signed: bool) -> c_ast.Cast:
    if info.smt_type not in [pysmt.typing.BV1, pysmt.typing.BV8, pysmt.typing.BV16,
                             pysmt.typing.BV32, pysmt.typing.BV64, pysmt.typing.BOOL]:
        raise ValueError('Unsupported type', info.smt_type)
    is_bool = info.smt_type in (pysmt.typing.BV1, pysmt.typing.BOOL)
    return c_ast.Cast(c_ast.Typename(None, [], None, c_ast.TypeDecl(None, [], None, c_ast.IdentifierType([
        'signed' if signed else 'unsigned', 'int' if is_bool else SMT2C_SIZE_NAME_DICT[info.smt_type]
    ]))), c_ast.BinaryOp('&&', node, c_ast.Constant('int', '1')) if is_bool else node)


def _division_wrapper(divide_by_zero_value: int, operation_symbol: str):
    def _division(info: Info, children: list[c_ast.Node], un_signed: typing.Callable[[node_or_list], node_or_list],
                  operation: typing.Callable[[c_ast.Node, c_ast.Node], c_ast.Node] = None) -> Tuple[c_ast.TernaryOp, Info]:
        return c_ast.TernaryOp(
            c_ast.BinaryOp('==', children[1], c_ast.Constant('int', '0')),
            constant_value(divide_by_zero_value, info.smt_type),
            operation(*children) if operation else c_ast.BinaryOp(operation_symbol, *un_signed(children))
        ), info
    return _division


divide = _division_wrapper(-1, '/')
remainder = _division_wrapper(0, '%')


def shift(left: c_ast.Node, right: c_ast.Node, info: Info, to_right: bool) -> c_ast.Node:
    """
    :return: the shift implemented in C according to its SmtLib semantics
    """
    return c_ast.TernaryOp(
        c_ast.BinaryOp('>=', right, c_ast.Constant('int', str(info.smt_type.width))),
        c_ast.Constant('int', '0'),
        c_ast.BinaryOp('>>' if to_right else '<<', left, right)
    )


def rotate(left: c_ast.Node, right: int, info: Info, to_right: bool) -> c_ast.Node:
    """
    :param left: parameter to be shifted
    :param right: number of bits to shift by
    :param info: type which is rotated
    :param to_right: whether this is rotation is to the right (if false: to the left)
    :return: the rotated value
    """
    return c_ast.BinaryOp(
        '|',
        c_ast.BinaryOp(
            '>>' if to_right else '<<', left,
            c_ast.Constant('int', str(right % info.smt_type.width))
        ),
        c_ast.BinaryOp(
            '<<' if to_right else '>>', left,
            c_ast.Constant('int', str(info.smt_type.width - (right % info.smt_type.width)))
        )
    )


def neg_rem(left: c_ast.Node, right: c_ast.Node):
    """
    :return: the remainder implemented in C according to the SmtLib semantics
    """
    return c_ast.BinaryOp(
        '-',
        left,
        c_ast.BinaryOp(
            '*',
            c_ast.BinaryOp('/', left, right),
            c_ast.TernaryOp(
                c_ast.BinaryOp('<', right, c_ast.Constant('int', '0')),
                c_ast.Constant('int', '-1'),
                c_ast.Constant('int', '1')
            )
        )
    )


def constant_value(value: int, bv_type: pysmt.typing.BVType) -> c_ast.Cast:
    sign_suffix = 'u' if value >= 2 ** (bv_type.width - 1) else ''
    size_suffix = 'll' if bv_type.width > 32 else ''
    return cast(c_ast.Constant(SMT2C_SIZE_NAME_DICT.get(bv_type, 'int'),
                               f'{value}{sign_suffix}{size_suffix}'),
                Info(bv_type), False)


def to_c(f_node: FNode, to_c_name, allow_exceptions=True, timeout=None) -> Tuple[c_ast.Node, Info]:
    """
    recursively transforms a FNode to a C AST node and its type information
    """
    if timeout and timeout < time.time():
        raise TimeoutError()
    smt_children = [to_c(content, to_c_name, allow_exceptions, timeout) for content in f_node.args()]
    info = smt_children[0][1] if smt_children else None
    children = [node for node, info in smt_children]

    def signed(nodes: node_or_list) -> node_or_list:
        return [cast(node, info, True) for node in nodes] if isinstance(nodes, list) else cast(nodes, info, True)

    def unsigned(nodes: node_or_list) -> node_or_list:
        return [cast(node, info, False) for node in nodes] if isinstance(nodes, list) else cast(nodes, info, False)

    from pysmt import operators as ops
    match f_node.node_type(), len(children):
        # Boolean Logic (0-6)
        # FORALL, EXISTS
        case ops.AND, length if length >= 1: return nested_binary_op('&&', *children), info  # 2
        case ops.OR, length if length >= 1: return nested_binary_op('||', *children), info  # 3
        case ops.NOT, 1: return c_ast.UnaryOp('!', children[0]), info  # 4
        case ops.IMPLIES, 2: return c_ast.BinaryOp('||', c_ast.UnaryOp('!', children[0]), children[1]), info  # 5
        case ops.IFF | ops.EQUALS, 2:
            return c_ast.BinaryOp('==', *signed(children)), info  # 6
        # Symbol (7)
        case ops.SYMBOL, 0: return c_ast.ID(to_c_name(f_node.symbol_name())), Info(f_node.symbol_type())
        # Bool Constant (10)
        case ops.BOOL_CONSTANT, 0:
            return c_ast.Constant('int', '1' if f_node.is_true() else '0'), Info(pysmt.typing.BOOL)
        # Ternary Operator (19)
        case ops.ITE, 3: return c_ast.TernaryOp(*children), smt_children[1][1]
        # BitVectors (21-47)
        case ops.BV_CONSTANT, 0:  # 2
            return constant_value(f_node.constant_value(), f_node.constant_type()), Info(f_node.constant_type())
        case ops.BV_NOT, 1: return c_ast.UnaryOp('~', *children), info  # 22
        case ops.BV_AND, 2: return c_ast.BinaryOp('&', *children), info  # 23
        case ops.BV_OR,  2: return c_ast.BinaryOp('|', *children), info  # 24
        case ops.BV_XOR, 2: return c_ast.BinaryOp('^', *children), info  # 25
        case ops.BV_CONCAT, length if f_node.bv_width() in (8, 16, 32, 64) and info.smt_type.width >= 8:  # 26
            hex_filter = f"0x{'FF' * (info.smt_type.width // 8)}"
            result_info = Info(pysmt.typing.BVType(f_node.bv_width()))
            return (cast(nested_binary_op('|', *[c_ast.BinaryOp(
                        '<<',
                        c_ast.BinaryOp('&', child, c_ast.Constant('long', hex_filter)),
                        c_ast.Constant('int', str(info.smt_type.width * (length - i - 1)))
                    ) for i, child in enumerate(children)]), result_info, False),
                    Info(pysmt.typing.BVType(info.smt_type.width * 2)))
        case ops.BV_EXTRACT, 1 if (f_node.bv_extract_end() - f_node.bv_extract_start() + 1) in (8, 16, 32, 64):  # 27
            result_info = Info(pysmt.typing.BVType(f_node.bv_extract_end() - f_node.bv_extract_start() + 1))
            return cast(c_ast.BinaryOp('>>', *children, c_ast.Constant('int', str(f_node.bv_extract_start()))),
                        result_info, False), result_info
        case ops.BV_EXTRACT, 1 if (f_node.bv_extract_end() - f_node.bv_extract_start() + 1) == 1:  # 27
            return c_ast.Cast(
                c_ast.Typename(None, [], None, c_ast.TypeDecl(None, [], None, c_ast.IdentifierType(['signed', 'int']))),
                c_ast.BinaryOp('>>', *children, c_ast.Constant('int', str(f_node.bv_extract_start())))
            ), Info(pysmt.typing.BOOL)
        case ops.BV_ULT, 2: return c_ast.BinaryOp('<',  *unsigned(children)), BOOL_INFO  # 28
        case ops.BV_ULE, 2: return c_ast.BinaryOp('<=', *unsigned(children)), BOOL_INFO  # 29
        case ops.BV_NEG, 1: return c_ast.UnaryOp('-', *children), info  # 30
        case ops.BV_ADD, 2: return c_ast.BinaryOp('+', *children), info  # 31
        case ops.BV_SUB, 2: return c_ast.BinaryOp('-', *children), info  # 32
        case ops.BV_MUL, 2: return c_ast.BinaryOp('*', *children), info  # 33
        case ops.BV_UDIV, 2: return divide(info, children, unsigned)  # 34
        case ops.BV_UREM, 2: return remainder(info, children, unsigned)  # 35
        case ops.BV_LSHL, 2: return shift(*unsigned(children), info, False), info  # 36
        case ops.BV_LSHR, 2: return shift(*unsigned(children), info, True), info  # 37
        case ops.BV_ROL, 1: return rotate(*unsigned(children), f_node.bv_rotation_step(), info, False), info  # 38
        case ops.BV_ROR, 1: return rotate(*unsigned(children), f_node.bv_rotation_step(), info, True), info  # 39
        case ops.BV_ZEXT, 1 if f_node.bv_width() in (8, 16, 32, 64):  #40
            result_info = Info(pysmt.typing.BVType(f_node.bv_width()))
            return cast(*unsigned(children), result_info, True), result_info
        case ops.BV_SEXT, 1 if f_node.bv_width() in (8, 16, 32, 64):  # 41
            result_info = Info(pysmt.typing.BVType(f_node.bv_width()))
            return cast(*signed(children), result_info, True), result_info
        case ops.BV_SLT, 2: return c_ast.BinaryOp('<',  *signed(children)), BOOL_INFO  # 42
        case ops.BV_SLE, 2: return c_ast.BinaryOp('<=', *signed(children)), BOOL_INFO  # 43
        case ops.BV_COMP, 2:  # 44
            return c_ast.TernaryOp(c_ast.BinaryOp('==', *signed(children)), children[0], c_ast.Constant('int', '0')), info
        case ops.BV_SDIV, 2: return divide(info, children, signed)  # 45
        case ops.BV_SREM, 2: return remainder(info, children, signed, operation=neg_rem)  # 46
        case ops.BV_ASHR, 2:  # 47
            return c_ast.BinaryOp(
                '|',
                c_ast.BinaryOp(
                    '>>',
                    c_ast.TernaryOp(
                        c_ast.BinaryOp('>>', children[0], c_ast.Constant('int', str(info.smt_type.width - 1))),
                        c_ast.Constant(SMT2C_SIZE_NAME_DICT[info.smt_type], f"0x{'FF' * (info.smt_type.width // 8)}"),
                        c_ast.Constant(SMT2C_SIZE_NAME_DICT[f_node.get_type()], '0')
                    ),
                    c_ast.TernaryOp(
                        c_ast.BinaryOp('<', children[1], c_ast.Constant('int', str(info.smt_type.width))),
                        children[1],
                        c_ast.Constant('int', '0')
                    ),
                ),
                shift(*children, info, True)
            ), info
        case _:
            if allow_exceptions:
                raise ValueError('Unsupported FNode', f_node)
            # TODO: implement cases when we land here
            return c_ast.Constant('char[]', f'"Unsupported FNode {f_node}"'), None


# TODO: pycparser deletes ; after extern functions.
DEFAULT_FUNCTIONS_CODE = '''
extern char __VERIFIER_nondet_char();
extern short __VERIFIER_nondet_short();
extern int __VERIFIER_nondet_int();
extern long __VERIFIER_nondet_longlong();
extern void reach_error();
void assert (int assertion) {
    if(!assertion) {
        reach_error();
    }
}
'''
DEFAULT_FUNCTIONS = pycparser.CParser().parse(DEFAULT_FUNCTIONS_CODE)


def to_program(functions: list[c_ast.Node], variables: list[c_ast.Node], code: c_ast.Node):
    return c_ast.FileAST([
        *functions,
        c_ast.FuncDef(
            c_ast.Decl('main', [], [], [], [],
                       c_ast.FuncDecl(None, c_ast.TypeDecl('main', [], None,c_ast.IdentifierType(['int']))),
                       None, None),
            None, c_ast.Compound([*variables, c_ast.FuncCall(c_ast.ID('assert'), c_ast.UnaryOp('!', code))])
        )
    ])


def transform_one_check_script(script: SmtLibScript, allow_exceptions=True, timeout=None
                               ) -> tuple[c_ast.Node, dict[str, str]]:
    """
    transforms a script to a C ast and a dict of the set information in the SmtLib program
    """
    if timeout:
        timeout += time.time()

    declarations = list(script.filter_by_command_name({commands.DECLARE_FUN}))
    variables = [decl for decl in declarations if len(decl.args) == 1]
    variables += list(script.filter_by_command_name({commands.DECLARE_CONST}))
    functions = [decl for decl in declarations if len(decl.args) > 1]

    name_dict = {}

    info = {command.args[0]: command.args[1] for command in script.filter_by_command_name({commands.SET_INFO})}
    info |= {'logic': command.args[0].name for command in script.filter_by_command_name({commands.SET_LOGIC})
             if command.args[0]}

    def name(smtlib_name: str) -> str:
        """
        :return: a valid name in C for the given name in SmtLib
        """
        if smtlib_name in name_dict:
            return name_dict[smtlib_name]
        c_name = re.sub('[^_0-9a-zA-Z]', '_', smtlib_name)
        if c_name in name_dict:
            i = 1
            while (c_name_i := f'{c_name}_{i}') in name_dict:
                i += 1
            c_name = c_name_i
        name_dict[smtlib_name] = c_name
        return c_name

    variable_declarations = [to_c_declaration(node, name, allow_exceptions) for node in variables]
    strict = script.get_strict_formula()
    return to_program([], variable_declarations, to_c(strict, name, allow_exceptions, timeout)[0]), info


def main(reader, allow_exceptions=True, timeout=None, c_generator=pycparser.c_generator.CGenerator()
         ) -> list[str, dict[str, str]]:
    parser = SmtLibParser(environment.Environment())
    asts = [transform_one_check_script(script, allow_exceptions, timeout)
            for script in one_check_sat(parser.get_script(reader))]
    return [(DEFAULT_FUNCTIONS_CODE + c_generator.generic_visit(ast[0]), ast[1]) for ast in asts]


if __name__ == '__main__':
    with open(6 * '..\\' + r'smt-comp\non-incremental\QF_BV\2018-Goel-hwbench\QF_BV_anderson.2.prop1_cc_ref_max.smt2') as r:
        main(r, False, 1.)

