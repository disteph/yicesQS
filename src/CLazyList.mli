(** Module for Costed Lazy Lists *)

open Containers

(** The module is parameterised by a notion of cost *)

module Make(C : sig
             type t                  (* type of costs *)
             val compare : t Ord.t   (* costs can be compared *)
             val zero : t            (* no cost value *)
             val ( - ) : t -> t -> t (* costs can be subtracted *)
           end) : sig

  (** In a costed lazy list, each lazy list element is a pair:
      the actual element, and the cost of accessing the tail of the lazy list.
      Accessing the head of the  costed lazy list is always free *)

  type 'a t = ('a * C.t) LazyList.t

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
  val mix      : C.t -> 'a t -> C.t -> 'a t -> C.t * 'a t
  (* val expand   : 'a t -> C.t -> 'a t -> 'a t *)

end
