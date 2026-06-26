(set-logic NIA)
(assert
  (forall ((p Int))
    (=> (>= p 0)
        (exists ((x Int))
          (and (<= p (* x x))
               (< p (+ (* x x) 20)))))))
(check-sat)
