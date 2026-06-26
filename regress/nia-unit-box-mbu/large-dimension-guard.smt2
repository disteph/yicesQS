(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int))
      (and (<= p (+ x1 x2 x3 x4 x5))
           (< (+ x1 x2 x3 x4 x5) (+ p 10))))))
(check-sat)
