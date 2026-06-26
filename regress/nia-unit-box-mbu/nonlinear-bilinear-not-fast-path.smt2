(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int) (y Int))
      (and (= x p)
           (= y 1)
           (= (* x y) p)))))
(check-sat)
