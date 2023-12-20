(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |generated from test cases in Smt2C|)
(set-info :license "https://opensource.org/license/mit/")
(set-info :category "crafted")
(set-info :status sat)

(declare-fun p () (_ BitVec 8))
(declare-fun q () (_ BitVec 16))
(assert (= ((_ sign_extend 8) p) q))
(check-sat)
            