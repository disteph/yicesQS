(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int))
      (and (<= p x)
           (< (to_real x) (+ (to_real p) 2.5))))))
(check-sat)
