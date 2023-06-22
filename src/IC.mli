open! Containers
open Yices2.Ext.WithNoErrorHandling
open Utils

(* elim_existentials vars formula
   Ideally it returns a formula R, possibly with epsilon variables in it,
   such that (∃ vars. formula) <=> R.
   It can fail to eliminate the vars variables,
   in which case some of them may be left in it,
   but we still have (∃ vars. formula) <=> (∃ vars. R) *)
val elim_existentials : Term.t list -> Term.t -> Term.t WithEpsilonsMonad.t
val elim_existentials_init : Term.t list -> Term.t -> Term.t WithEpsilons.t

(* weaken_existentials vars formula
   It returns a formula R, possibly with epsilon variables in it,
   such that (∃ vars. formula) => R.
   It is not an equivalence,
   but on the other hand we are guaranteed that the variables have been eliminated.
   This is typically useful for model interpolation. *)
val weaken_existentials : Term.t list -> Term.t -> Term.t WithEpsilonsMonad.t
val weaken_existentials_init : Term.t list -> Term.t -> Term.t WithEpsilons.t
