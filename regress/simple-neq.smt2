(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun x () (_ BitVec 32))
(assert (forall ((y (_ BitVec 32))) (distinct x y)))
(check-sat)
(exit)
