(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int))
      (= (* (- 1) x)
         (* (- 1) p)))))
(check-sat)
