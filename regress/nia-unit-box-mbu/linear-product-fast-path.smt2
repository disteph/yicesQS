(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int))
      (= (* (+ 1 2) x)
         (* (+ 1 2) p)))))
(check-sat)
