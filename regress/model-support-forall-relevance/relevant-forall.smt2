(set-info :status unsat)
(set-logic BV)
(declare-const a (_ BitVec 8))
(assert
  (forall ((x (_ BitVec 8)))
    (= x a)))
(check-sat)
