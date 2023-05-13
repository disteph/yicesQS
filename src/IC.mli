open! Containers
open Yices2.Ext
open Utils

val solve_all : TermSet.elt list -> TermSet.elt -> TermSet.elt WithEpsilons.t
