(** Module for costed lazy lists. *)

open Containers

(** The module is parameterized by a notion of cost. *)

module Make(C : sig
             type t                  (* type of costs *)
             val compare : t Ord.t   (* costs can be compared *)
             val zero : t            (* no cost value *)
             val ( - ) : t -> t -> t (* costs can be subtracted *)
           end) : sig

  (** In a costed lazy list, each element is paired with the cost of
      accessing the tail. Accessing the head is free. *)

  type 'a t = ('a * C.t) LazyList.t

  (** Costed lazy lists form a monad; return produces a singleton list
      with zero cost to access the empty tail. *)
  val return   : 'a -> 'a t
  val bind     : 'a t -> ('a -> 'b t) -> 'b t
  val ( let@ ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Mixing two costed lazy lists with non-free head access.
      mix c1 l1 c2 l2 computes the mix of l1 and l2,
      with c1 and c2 being the costs of accessing the heads of l1 and l2, respectively.
      The output also includes a cost, that of accessing the head of the result,
      namely the min of c1 and c2. *)
  val mix      : C.t -> 'a t -> C.t -> 'a t -> C.t * 'a t
  (* val expand   : 'a t -> C.t -> 'a t -> 'a t *)

end
