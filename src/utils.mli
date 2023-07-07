open Containers

open Yices2.Ext.WithNoErrorHandling

val get_disjuncts : Term.t -> Term.t list
val get_conjuncts : Term.t -> Term.t list

val print : int -> ('b, Format.formatter, unit) format -> 'b
val pp_space : unit Format.printer

module type Monad = sig
  type 'a t
  val return : 'a -> 'a t
  val bind   : 'a t -> ('a -> 'b t) -> 'b t
  val (let+) : 'a t -> ('a -> 'b t) -> 'b t
end

module StateMonad(State: sig type t end) : Monad with type 'a t = State.t -> 'a*State.t

module WithEpsilons : sig

  type 'a t = {
      main     : 'a;
      epsilons : Term.t list
    }

  val return : 'a -> 'a t

end

module WithEpsilonsMonad : Monad with type 'a t = Term.t list -> 'a WithEpsilons.t

module ListWithEpsilons : sig
  val fold :
    ('a -> 'b -> 'a WithEpsilonsMonad.t) ->
    'a WithEpsilonsMonad.t -> 'b list -> 'a WithEpsilonsMonad.t
  val map :
    ('a -> 'b WithEpsilonsMonad.t) -> 'a list -> 'b list WithEpsilonsMonad.t
end

module SeqWithEpsilons : sig
  val fold :
    ('a -> 'b -> 'a WithEpsilonsMonad.t) ->
    'a WithEpsilonsMonad.t -> 'b Seq.t -> 'a WithEpsilonsMonad.t
  val map :
    ('a -> 'b WithEpsilonsMonad.t) -> 'a Seq.t -> 'b Seq.t WithEpsilonsMonad.t
end

module CLL : sig

  (** In a costed lazy list, each lazy list element is a pair:
      the actual element, and the cost of accessing the tail of the lazy list.
      Accessing the head of the  costed lazy list is always free *)

  type 'a t = ('a * int) LazyList.t

  (** Costed lazy lists form a monad,
      where return produces a singleton list with zero cost to access the empty tail. *)
  val return   : 'a -> 'a t
  val bind     : 'a t -> ('a -> 'b t) -> 'b t
  val ( let@ ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Mixing 2 costed lazy lists with non-free head access.
      mix c1 l1 c2 l2 computes the mix of l1 and l2,
      with c1 and c2 being the costs of accessing the heads of l1 and l2, respectively.
      The output also includes a cost, that of accessing the head of the result,
      namely the min of c1 and c2. *)
  val mix      : int -> 'a t -> int -> 'a t -> int * 'a t
  (* val expand   : 'a t -> C.t -> 'a t -> 'a t *)

end

type logic = [ `NRA | `NIA | `LRA | `LIA | `BV | `Other ]
