open! Containers

open Ext

open Utils

val generalize_model :
  (* Model-based under-approximation MBU (Def. 4), returning U formulas
     used by OptiQSMA (Alg. 4, line 10). *)
  logic:SolverState.logic
  -> Model.t
  -> true_of_model:TermSet.elt
  -> rigid_vars:TermSet.elt list
  -> newvars:TermSet.elt list
  -> Term.t WithEpsilons.t CLL.t
