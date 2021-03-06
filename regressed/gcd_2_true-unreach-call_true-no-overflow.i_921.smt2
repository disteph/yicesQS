(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |
Generated by the tool Ultimate Automizer [1,2] which implements 
an automata theoretic approach [3] to software verification.

This SMT script belongs to a set of SMT scripts that was generated by 
applying Ultimate Automizer to benchmarks [4] from the SV-COMP 2017 [5,6].

This script might _not_ contain all SMT commands that are used by 
Ultimate Automizer. In order to satisfy the restrictions of
the SMT-COMP we have to drop e.g., the commands for getting
values (resp. models), unsatisfiable cores and interpolants.

2017-05-01, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)


[1] https://ultimate.informatik.uni-freiburg.de/automizer/
[2] Matthias Heizmann, Yu-Wen Chen, Daniel Dietsch, Marius Greitschus, 
Alexander Nutz, Betim Musa, Claus Schätzle, Christian Schilling, 
Frank Schüssele, Andreas Podelski:
Ultimate Automizer with an On-Demand Construction of Floyd-Hoare 
Automata - (Competition Contribution). TACAS (2) 2017: 394-398
[3] Matthias Heizmann, Jochen Hoenicke, Andreas Podelski: Software Model 
Checking for People Who Love Automata. CAV 2013:36-52
[4] https://github.com/sosy-lab/sv-benchmarks
[5] Dirk Beyer: Software Verification with Validation of Results - 
(Report on SV-COMP 2017). TACAS (2) 2017: 331-349
[6] https://sv-comp.sosy-lab.org/2017/
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun |c_gcd_test_#in~b| () (_ BitVec 8))
(declare-fun c_gcd_test_~a () (_ BitVec 8))
(declare-fun c_gcd_test_~a_primed () (_ BitVec 8))
(declare-fun c_gcd_test_~b () (_ BitVec 8))
(declare-fun c_gcd_test_~b_primed () (_ BitVec 8))
(declare-fun c_gcd_test_~t~5_primed () (_ BitVec 8))
(assert (and (not (= ((_ sign_extend 24) c_gcd_test_~b) ((_ sign_extend 24) (_ bv0 8)))) (= c_gcd_test_~t~5_primed c_gcd_test_~b) (= c_gcd_test_~b_primed ((_ extract 7 0) (bvsrem ((_ sign_extend 24) c_gcd_test_~a) ((_ sign_extend 24) c_gcd_test_~b)))) (= c_gcd_test_~a_primed c_gcd_test_~t~5_primed)))
(assert (or (not (bvsgt ((_ sign_extend 24) |c_gcd_test_#in~b|) ((_ sign_extend 24) (_ bv0 8)))) (= ((_ sign_extend 24) (_ bv0 8)) ((_ sign_extend 24) c_gcd_test_~b)) (forall ((v_gcd_test_~a_30 (_ BitVec 8))) (or (bvsge ((_ sign_extend 24) |c_gcd_test_#in~b|) ((_ sign_extend 24) v_gcd_test_~a_30)) (not (= ((_ sign_extend 24) (_ bv0 8)) ((_ sign_extend 24) ((_ extract 7 0) (bvsrem ((_ sign_extend 24) c_gcd_test_~b) ((_ sign_extend 24) v_gcd_test_~a_30))))))))))
(assert (not (or (not (bvsgt ((_ sign_extend 24) |c_gcd_test_#in~b|) ((_ sign_extend 24) (_ bv0 8)))) (bvslt ((_ sign_extend 24) c_gcd_test_~b_primed) ((_ sign_extend 24) (_ bv0 8))) (= ((_ sign_extend 24) (_ bv0 8)) ((_ sign_extend 24) c_gcd_test_~b_primed)) (forall ((v_gcd_test_~a_30 (_ BitVec 8))) (or (bvsge ((_ sign_extend 24) |c_gcd_test_#in~b|) ((_ sign_extend 24) v_gcd_test_~a_30)) (not (= ((_ sign_extend 24) (_ bv0 8)) ((_ sign_extend 24) ((_ extract 7 0) (bvsrem ((_ sign_extend 24) c_gcd_test_~b_primed) ((_ sign_extend 24) v_gcd_test_~a_30)))))))))))
(check-sat)
(exit)
