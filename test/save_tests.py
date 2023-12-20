import os
import re

from test_smt_lib2c import TransformTest


path = '../examples/test_sources'


def extract_name(name: str) -> str:
    return re.sub(r' p| q|\(_ |[ 0-9]*\)| ', '', name)


class SaveTest(TransformTest):
    @classmethod
    def setUpClass(cls):
        super(TransformTest, cls).setUpClass()
        if not os.path.exists(path):
            os.makedirs(path)

    def _test(self, name: str, smtlib: str, expected_c: list[str], allow_exceptions=True):
        smtlib = smtlib.replace(smtlib[:smtlib.find('(')], '\n')
        with open(f'{path}/{extract_name(name)}.smt2', 'w+') as w:
            w.write(
                f'(set-info :smt-lib-version 2.6)\n'
                f'(set-logic QF_BV)\n'
                f'(set-info :source |generated from test cases in Smt2C|)\n'
                f'(set-info :license "https://opensource.org/license/mit/")\n'
                f'(set-info :category "crafted")\n'
                f'(set-info :status sat)\n'
                f'{smtlib}'
            )
