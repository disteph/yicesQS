open! Containers

open Yices2.Ext_bindings

open Utils

val generalize_model :
  logic:SolverState.logic
  -> Model.t
  -> true_of_model:TermSet.elt
  -> rigid_vars:TermSet.elt list
  -> newvars:TermSet.elt list
  -> Term.t WithEpsilons.t CLL.t
