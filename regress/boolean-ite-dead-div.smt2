(set-info :smt-lib-version 2.6)
(set-logic NRA)
(set-info :status sat)
(declare-fun c () Bool)
(assert c)
(assert
  (forall ((x Real))
    (ite c
      (= x x)
      (= (/ 1.0 0.0) 0.0))))
(check-sat)
(exit)
