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
(assert
  (exists ((?x1 (_ BitVec 32)))
    (forall ((?x2 (_ BitVec 32)))
      (exists ((?x3 (_ BitVec 32)))
        (or
          (or
            (bvsge
              (bvadd (bvmul (_ bv56 32) ?x1) (bvmul (bvneg (_ bv96 32)) ?x2))
              (_ bv34 32))
            (bvsgt
              (bvadd (bvadd (bvmul (_ bv26 32) ?x1) (bvmul (_ bv88 32) ?x2)) (bvmul (_ bv24 32) ?x3))
              (_ bv36 32)))
          (and
            (bvsle
              (bvadd
                (bvadd (bvmul (_ bv90 32) ?x1) (bvmul (bvneg (_ bv82 32)) ?x2))
                (bvmul (bvneg (_ bv12 32)) ?x3))
              (bvneg (_ bv31 32)))
            (bvsle
              (bvadd
                (bvadd (bvmul (_ bv29 32) ?x1) (bvmul (bvneg (_ bv3 32)) ?x2))
                (bvmul (_ bv63 32) ?x3))
              (bvneg (_ bv25 32)))))))))
(check-sat)
(exit)
