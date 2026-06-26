(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int))
      (= x p))))
(check-sat)
