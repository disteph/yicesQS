(* Simple lazy list type used to enumerate candidates on demand. *)
type 'a t = 'a node Lazy.t
and 'a node = [ `Cons of 'a * 'a t | `Nil ]

val empty   : [> `Nil ] lazy_t (* Empty lazy list. *)
val return  : 'a -> 'a t (* Singleton lazy list. *)
val length  : 'a t -> int (* Forces the full list. *)
val fold    : ('b Lazy.t -> 'a -> 'b) -> 'b Lazy.t -> 'a t -> 'b Lazy.t
(* Lazy fold that preserves on-demand traversal. *)
val map     : ('a -> 'b) -> 'a t -> 'b t (* Lazy map. *)
val append  : 'a t -> 'a t -> 'a t (* Lazy append. *)
val bind    : 'a t -> ('a -> 'b t) -> 'b t (* Lazy monadic bind. *)
val flatten : 'a t t -> 'a t (* Flatten a lazy list of lazy lists. *)
val extract : int -> 'b t -> 'b list (* Take first n elements. *)
