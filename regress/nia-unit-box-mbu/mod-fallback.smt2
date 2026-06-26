(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int))
      (= (mod x 2) (mod p 2)))))
(check-sat)
