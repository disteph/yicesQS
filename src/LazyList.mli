type 'a t = 'a node Lazy.t
and 'a node = [ `Cons of 'a * 'a t | `Nil ]

val empty   : [> `Nil ] lazy_t
val return  : 'a -> 'a t
val length  : 'a t -> int
val fold    : ('b Lazy.t -> 'a -> 'b) -> 'b Lazy.t -> 'a t -> 'b Lazy.t
val map     : ('a -> 'b) -> 'a t -> 'b t
val append  : 'a t -> 'a t -> 'a t
val bind    : 'a t -> ('a -> 'b t) -> 'b t
val flatten : 'a t t -> 'a t
val extract : int -> 'b t -> 'b list
