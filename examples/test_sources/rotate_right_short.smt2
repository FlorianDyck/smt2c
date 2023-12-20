(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |generated from test cases in Smt2C|)
(set-info :license "https://opensource.org/license/mit/")
(set-info :category "crafted")
(set-info :status sat)

(declare-fun p () (_ BitVec 16))
(declare-fun q () (_ BitVec 16))
(declare-fun r () (_ BitVec 16))
(assert (= ((_ rotate_right 4) p) r))
(check-sat)
                