(set-logic NIA)
(assert
  (forall ((p Int))
    (exists ((x Int))
      (and (= (<= p x)
              (< p (+ x 1)))
           (<= p x)
           (< x (+ p 2))))))
(check-sat)
