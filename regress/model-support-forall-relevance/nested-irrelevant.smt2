(set-info :status sat)
(set-logic BV)
(declare-const a (_ BitVec 8))
(assert
  (or (= a (_ bv0 8))
      (forall ((x (_ BitVec 8)))
        (forall ((y (_ BitVec 8)))
          (= x y)))))
(check-sat)
