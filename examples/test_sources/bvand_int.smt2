(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |generated from test cases in Smt2C|)
(set-info :license "https://opensource.org/license/mit/")
(set-info :category "crafted")
(set-info :status sat)

(declare-fun p () (_ BitVec 32))
(declare-fun q () (_ BitVec 32))
(declare-fun r () (_ BitVec 32))
(assert (= (bvand p q) r))
(check-sat)
                