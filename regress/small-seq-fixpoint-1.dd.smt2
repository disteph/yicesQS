(set-logic BV)
(assert (forall ((Verilog__main.a_64_0 (_ BitVec 101))) (forall ((Verilog__main.b_64_0 (_ BitVec 101))) (forall ((Verilog__main.a_64_1 (_ BitVec 101))) (forall ((Verilog__main.b_64_1 (_ BitVec 101))) (exists ((Verilog__main.a_64_0_39_ (_ BitVec 101))) (exists ((Verilog__main.b_64_0_39_ (_ BitVec 101))) (=> (and (and (= Verilog__main.a_64_0 (_ bv1 101)) (= Verilog__main.b_64_0 (_ bv0 101))) (= Verilog__main.a_64_1 (ite (bvult Verilog__main.a_64_0 (_ bv100 101)) (bvadd Verilog__main.b_64_0 Verilog__main.a_64_0) Verilog__main.a_64_0))) false))))))))
(check-sat)
(exit)
