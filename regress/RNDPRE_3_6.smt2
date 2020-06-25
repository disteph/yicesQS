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
(assert (exists ((?x1 (_ BitVec 32))) (forall ((?x2 (_ BitVec 32))) (exists ((?x3 (_ BitVec 32))) (or (and (and (and (bvsge (bvadd (bvmul (bvneg (_ bv54 32)) ?x1) (bvmul (_ bv62 32) ?x3)) (_ bv79 32)) (not (= (bvadd (bvadd (bvmul (bvneg (_ bv49 32)) ?x1) (bvmul (_ bv25 32) ?x2)) (bvmul (_ bv51 32) ?x3)) (_ bv12 32)))) (or (bvslt (bvadd (bvadd (bvmul (_ bv5 32) ?x1) (bvmul (_ bv20 32) ?x2)) (bvmul (bvneg (_ bv1 32)) ?x3)) (_ bv0 32)) (not (= (bvadd (bvadd (bvmul (_ bv58 32) ?x1) (bvmul (_ bv61 32) ?x2)) (bvmul (_ bv74 32) ?x3)) (bvneg (_ bv18 32)))))) (or (and (bvsge (bvadd (bvmul (_ bv48 32) ?x1) (bvmul (bvneg (_ bv47 32)) ?x2)) (_ bv61 32)) (bvsge (bvadd (bvadd (bvmul (bvneg (_ bv19 32)) ?x1) (bvmul (bvneg (_ bv80 32)) ?x2)) (bvmul (bvneg (_ bv66 32)) ?x3)) (_ bv25 32))) (and (bvsle (bvadd (bvmul (bvneg (_ bv63 32)) ?x2) (bvmul (bvneg (_ bv98 32)) ?x3)) (bvneg (_ bv28 32))) (not (= (bvadd (bvadd (bvmul (_ bv10 32) ?x1) (bvmul (_ bv47 32) ?x2)) (bvmul (_ bv77 32) ?x3)) (_ bv72 32)))))) (and (or (or (= (bvadd (bvmul (_ bv40 32) ?x1) (bvmul (_ bv16 32) ?x3)) (_ bv0 32)) (not (= (bvadd (bvmul (_ bv94 32) ?x2) (bvmul (bvneg (_ bv32 32)) ?x3)) (bvneg (_ bv6 32))))) (or (not (= (bvadd (bvadd (bvmul (bvneg (_ bv8 32)) ?x1) (bvmul (bvneg (_ bv45 32)) ?x2)) (bvmul (_ bv34 32) ?x3)) (_ bv57 32))) (bvsgt (bvadd (bvmul (bvneg (_ bv7 32)) ?x2) (bvmul (bvneg (_ bv17 32)) ?x3)) (_ bv0 32)))) (and (bvslt (bvadd (bvadd (bvmul (_ bv51 32) ?x1) (bvmul (_ bv5 32) ?x2)) (bvmul (bvneg (_ bv86 32)) ?x3)) (bvneg (_ bv32 32))) (and (bvsge (bvmul (_ bv50 32) ?x1) (_ bv37 32)) (not (= (bvmul (bvneg (_ bv95 32)) ?x2) (bvneg (_ bv24 32))))))))))))
(check-sat)
(exit)
