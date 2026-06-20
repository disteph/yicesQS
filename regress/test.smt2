(set-info :smt-lib-version 2.6)
(set-logic NRA)
(assert
  (forall ((x Real))
    (= (/ x x) 1)))
(check-sat)
(exit)