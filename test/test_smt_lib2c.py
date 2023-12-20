import unittest
from io import StringIO
from pycparser.c_parser import CParser
from pycparser.c_generator import CGenerator

import smt_lib2c


class TransformTest(unittest.TestCase):
    def setUp(self) -> None:
        self.c_parser = CParser()
        self.c_generator = CGenerator()
        self.maxDiff = 1000

    def format_c(self, c_code):
        return self.c_generator.generic_visit(self.c_parser.parse(c_code))

    def _test(self, name: str, smtlib: str, expected_c: list[str], allow_exceptions=True):
        with self.subTest(name):
            for expected, (actual, info) in zip([self.format_c(smt_lib2c.DEFAULT_FUNCTIONS_CODE + program)
                                                 for program in expected_c],
                                                smt_lib2c.main(StringIO(smtlib), allow_exceptions)):
                self.assertEqual(expected, self.format_c(actual))

    def test_integer(self):
        self.assertRaises(ValueError, lambda: smt_lib2c.main(StringIO('(declare-fun p () Int)\n(check-sat)')))

    def test_extensions(self):
        for type_name, bigger_type, size in ('char', 'short', 8), ('short', 'int', 16), ('int', 'long long', 32):
            nondet = f'__VERIFIER_nondet_{type_name.replace(" ", "")}'
            bigger_nondet = f'__VERIFIER_nondet_{bigger_type.replace(" ", "")}'
            filter = 'FF' * (size // 8)
            self._test(f'concat_{type_name}', f'''
                (declare-fun p () (_ BitVec {size}))
                (declare-fun q () (_ BitVec {size}))
                (declare-fun r () (_ BitVec {size * 2}))
                (assert (= (concat p q) r))
                (check-sat)
            ''', [
                f'''
                    int main() {{
                        {type_name} p = {nondet}();
                        {type_name} q = {nondet}();
                        {bigger_type} r = {bigger_nondet}();
                        assert(!(
                            ((signed {bigger_type})
                                ((unsigned {bigger_type})
                                    (((p & 0x{filter}) << {size}) | ((q & 0x{filter}) << 0))
                                )
                            ) == ((signed {bigger_type}) r)
                        ));
                    }}
                '''
            ])
            self._test(f'zero_extend_{type_name}', f'''
                (declare-fun p () (_ BitVec {size}))
                (declare-fun q () (_ BitVec {size * 2}))
                (assert (= ((_ zero_extend {size}) p) q))
                (check-sat)
            ''', [
                f'''
                    int main() {{
                        {type_name} p = {nondet}();
                        {bigger_type} q = {bigger_nondet}();
                        assert(!(
                            ((signed {bigger_type})
                                ((signed {bigger_type})
                                    ((unsigned {type_name}) p)
                                )
                            ) == ((signed {bigger_type}) q)
                        ));
                    }}
                '''
            ])
            self._test(f'sign_extend_{type_name}', f'''
                (declare-fun p () (_ BitVec {size}))
                (declare-fun q () (_ BitVec {size * 2}))
                (assert (= ((_ sign_extend {size}) p) q))
                (check-sat)
            ''', [
                f'''
                    int main() {{
                        {type_name} p = {nondet}();
                        {bigger_type} q = {bigger_nondet }();
                        assert(!(
                            ((signed {bigger_type})
                                ((signed {bigger_type})
                                    ((signed {type_name}) p)
                                )
                            ) == ((signed {bigger_type}) q)
                        ));
                    }}
                '''
            ])

    def test_simple_bitvecs(self):
        for type_name, size, postfix in ('char', 8, ''), ('short', 16, ''), ('int', 32, ''), ('long long', 64, 'll'):
            def signed(term):
                return f'((signed {type_name}) {term})'
            sp, sq, sr = map(signed, 'pqr')

            def unsigned(term):
                return f'((unsigned {type_name}) {term})'
            up, uq, ur = map(unsigned, 'pqr')

            nondet = f'__VERIFIER_nondet_{type_name.replace(" ", "")}'

            self._test(f'equals_transitive_{type_name}', f'''
                (declare-fun p () (_ BitVec {size}))
                (declare-fun q () (_ BitVec {size}))
                (declare-fun r () (_ BitVec {size}))
                (assert (= p q))
                (assert (= q r))
                (assert (not (= p r)))
                (check-sat)
            ''', [
                f'''
                    int main() {{
                        {type_name} p = {nondet}();
                        {type_name} q = {nondet}();
                        {type_name} r = {nondet}();
                        assert(!(({sp} == {sq}) && ({sq} == {sr} && !({sp} == {sr}))));
                    }}
                '''
            ])
            for smt_unary_op, c_unary_op, type in (
                    ('bvnot p', '(~p)', type_name),
                    ('(_ extract 7 0) p', '(unsigned char) (p >> 0)', 'char'),
            ):
                self._test(f'{smt_unary_op}_{type_name}', f'''
                    (declare-fun p () (_ BitVec {size}))
                    (declare-fun q () (_ BitVec {size}))
                    (assert (= ({smt_unary_op}) q))
                    (check-sat)
                ''', [
                    f'''
                        int main() {{
                            {type_name} p = {nondet}();
                            {type_name} q = {nondet}();
                            assert(!(((signed {type}) ({c_unary_op})) == ((signed {type}) q)));
                        }}
                    '''
                ])
            for smt_binary_op, c_binary_op in (
                ('bvand p q', 'p & q'), ('bvor p q', 'p | q'), ('bvxor p q', 'p ^ q'),
                ('bvadd p q', 'p + q'), ('bvsub p q', 'p - q'),
                ('bvmul p q', 'p * q'),  # ('bvmul', '((unsigned int) p) * ((unsigned int) q)'),
                ('bvudiv p q', f'(q == 0) ? {unsigned(f"(-1{postfix})")}: ({up} / {uq})'),
                ('bvurem p q', f'(q == 0) ? {unsigned(f"( 0{postfix})")}: ({up} % {uq})'),
                ('bvsdiv p q', f'(q == 0) ? {unsigned(f"(-1{postfix})")}: ({sp} / {sq})'),
                ('bvsrem p q', f'(q == 0) ? {unsigned(f"( 0{postfix})")}: (p - ((p / q) * ((q < 0) ? -1 : 1)))'),
                ('bvshl p q',  f'(((unsigned {type_name}) q) >= {size}) ? (0) :'
                               f'((unsigned {type_name}) p) << ((unsigned {type_name}) q)'),
                ('bvlshr p q', f'(((unsigned {type_name}) q) >= {size}) ? (0) :'
                               f'((unsigned {type_name}) p) >> ((unsigned {type_name}) q)'),
                ('(_ rotate_left 4) p',  f'(((unsigned {type_name}) p) << 4) |'
                                         f'(((unsigned {type_name}) p) >> {size - 4})'),
                ('(_ rotate_right 4) p', f'(((unsigned {type_name}) p) >> 4) |'
                                         f'(((unsigned {type_name}) p) << {size - 4})'),
                ('bvashr p q', f'(((p >> {size - 1}) ? (0x{"FF" * (size // 8)}) : (0)) >>'
                               f'((q < {size}) ? (q) : (0))) | ((q >= {size}) ? (0) : (p >> q))')
            ):
                self._test(f'{smt_binary_op}_{type_name}', f'''
                    (declare-fun p () (_ BitVec {size}))
                    (declare-fun q () (_ BitVec {size}))
                    (declare-fun r () (_ BitVec {size}))
                    (assert (= ({smt_binary_op}) r))
                    (check-sat)
                ''', [
                    f'''
                        int main() {{
                            {type_name} p = {nondet}();
                            {type_name} q = {nondet}();
                            {type_name} r = {nondet}();
                            assert(!({signed(f'({c_binary_op})')} == {sr}));
                        }}
                    '''
                ])
            for sign in ('signed', 'unsigned'):
                for smt_binary_op, first_operand, c_binary_op, second_operand in (
                        (f'bv{sign[0]}lt', 'p', '<', 'q'),
                        (f'bv{sign[0]}le', 'p', '<=', 'q'),
                        (f'bv{sign[0]}gt', 'q', '<', 'p'),
                        (f'bv{sign[0]}ge', 'q', '<=', 'p'),
                ):
                    self._test(f'{sign}_{smt_binary_op}_{type_name}', f'''
                        (declare-fun p () (_ BitVec {size}))
                        (declare-fun q () (_ BitVec {size}))
                        (assert ({smt_binary_op} p q))
                        (check-sat)
                    ''', [
                        f'''
                            int main() {{
                                {type_name} p = {nondet}();
                                {type_name} q = {nondet}();
                                assert(!((({sign} {type_name}) {first_operand}) {c_binary_op}
                                         (({sign} {type_name}) {second_operand})));
                            }}
                        '''
                    ])
