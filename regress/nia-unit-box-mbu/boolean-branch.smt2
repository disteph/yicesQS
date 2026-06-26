(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((b Bool) (x Int))
      (and b
           (<= p x)
           (< x (+ p 2))))))
(check-sat)
