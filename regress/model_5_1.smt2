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
(set-info :category "industrial")
(set-info :status sat)
(declare-fun lambda () (_ BitVec 32))
(declare-fun lambdaprime () (_ BitVec 32))
(declare-fun x4 () (_ BitVec 32))
(declare-fun x3 () (_ BitVec 32))
(declare-fun bool.b17 () Bool)
(declare-fun bool.b18 () Bool)
(declare-fun bool.b19 () Bool)
(assert (forall ((?lambda (_ BitVec 32))) (or (or (exists ((?lambdaprime (_ BitVec 32))) (let ((?v_0 (bvmul (bvneg (_ bv1 32)) (bvadd x4 (bvmul (_ bv30 32) ?lambdaprime))))) (and (and (bvsle (_ bv0 32) ?lambdaprime) (bvsle ?lambdaprime ?lambda)) (not (and (and (not (and bool.b17 (bvsle ?v_0 (bvneg (_ bv4100 32))))) (not (and bool.b18 (bvsle ?v_0 (bvneg (_ bv4500 32)))))) (not (and bool.b19 (bvsle ?v_0 (bvneg (_ bv4910 32)))))))))) (bvslt ?lambda (_ bv0 32))) (not (and (bvsle (bvmul (_ bv1 32) (bvadd x3 (bvmul (_ bv0 32) ?lambda))) (_ bv0 32)) (not (bvsle (bvmul (_ bv1 32) (bvadd x4 (bvmul (_ bv30 32) ?lambda))) (_ bv4820 32))))))))
(check-sat)
(exit)
