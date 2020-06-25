(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |
   Scholl, Christoph; Disch, Stefan; Pigorsch, Florian and Kupferschmid, 
   Stefan; Using an SMT Solver and Craig Interpolation to Detect and Remove 
   Redundant Linear Constraints in Representations of Non-Convex Polyhedra.
   Proceedings of 6th International Workshop on Satisfiability Modulo
   Theories, Princeton, USA, July 2008.
   <http://abs.informatik.uni-freiburg.de/smtbench/>

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "random")
(set-info :status sat)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x2 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(assert (forall ((?x1 (_ BitVec 32))) (exists ((?x2 (_ BitVec 32))) (forall ((?x3 (_ BitVec 32))) (exists ((?x4 (_ BitVec 32))) (let ((?v_0 (bvmul (_ bv6 32) ?x3)) (?v_1 (bvmul (_ bv17 32) ?x2))) (or (and (or (or (bvsge (bvmul (_ bv12 32) ?x4) (_ bv4 32)) (bvsgt (bvadd (bvadd (bvadd (bvmul (bvneg (_ bv30 32)) ?x1) (bvmul (_ bv64 32) ?x2)) ?v_0) (bvmul (_ bv93 32) ?x4)) (_ bv69 32))) (or (bvsgt (bvadd (bvadd ?v_1 (bvmul (_ bv47 32) ?x3)) (bvmul (_ bv15 32) ?x4)) (_ bv0 32)) (= (bvadd (bvadd (bvmul (bvneg (_ bv29 32)) ?x1) (bvmul (bvneg (_ bv35 32)) ?x3)) (bvmul (_ bv62 32) ?x4)) (_ bv0 32)))) (or (= (bvadd (bvadd (bvmul (bvneg (_ bv28 32)) ?x1) (bvmul (_ bv6 32) ?x2)) ?v_0) (bvneg (_ bv36 32))) (and (bvslt (bvadd (bvadd (bvmul (_ bv49 32) ?x1) (bvmul (bvneg (_ bv71 32)) ?x3)) (bvmul (_ bv46 32) ?x4)) (_ bv0 32)) (bvsgt (bvadd (bvadd (bvadd (bvmul (bvneg (_ bv11 32)) ?x1) (bvmul (bvneg (_ bv67 32)) ?x2)) (bvmul (bvneg (_ bv11 32)) ?x3)) (bvmul (bvneg (_ bv91 32)) ?x4)) (_ bv48 32))))) (or (and (bvsle (bvadd (bvadd (bvmul (_ bv45 32) ?x1) (bvmul (bvneg (_ bv7 32)) ?x3)) (bvmul (_ bv42 32) ?x4)) (_ bv0 32)) (= (bvadd (bvadd (bvadd (bvmul (_ bv42 32) ?x1) (bvmul (_ bv68 32) ?x2)) (bvmul (_ bv20 32) ?x3)) (bvmul (_ bv96 32) ?x4)) (_ bv45 32))) (and (and (bvsge (bvadd (bvmul (bvneg (_ bv21 32)) ?x3) (bvmul (_ bv47 32) ?x4)) (_ bv70 32)) (not (= (bvadd (bvadd (bvadd (bvmul (_ bv1 32) ?x1) ?v_1) (bvmul (bvneg (_ bv97 32)) ?x3)) (bvmul (_ bv94 32) ?x4)) (bvneg (_ bv39 32))))) (and (not (= (bvadd (bvadd (bvmul (_ bv34 32) ?x1) (bvmul (_ bv63 32) ?x3)) (bvmul (bvneg (_ bv23 32)) ?x4)) (_ bv12 32))) (bvsge (bvadd (bvadd (bvmul (_ bv71 32) ?x1) (bvmul (_ bv43 32) ?x2)) (bvmul (bvneg (_ bv22 32)) ?x3)) (bvneg (_ bv80 32)))))))))))))
(check-sat)
(exit)
