(declare-fun x () (_ BitVec 32))
(assert (forall ((y (_ BitVec 32))) (= x y)))
(check-sat)
(exit)
