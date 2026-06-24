(set-info :status sat)
(set-logic BV)
(assert
  (not
    (forall ((x (_ BitVec 8)))
      (forall ((y (_ BitVec 8)))
        (= x y)))))
(check-sat)
