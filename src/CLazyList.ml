(* Costed lazy lists: each element carries the cost to access the tail.
   Used to enumerate candidates in increasing cost order. *)
module Make(C : sig
    type t [@@deriving ord]
    val zero : t
    val (-) : t -> t -> t
  end) = struct

  type 'a t = ('a * C.t) LazyList.t

  (* Singleton with zero access cost. *)
  let return a = LazyList.return(a,C.zero)

  (* mix w1 l1 w2 l2: merge two costed lists whose heads have costs w1/w2,
     returning the smaller head cost and a lazily mixed tail. *)
  let rec mix w1 l1 w2 l2 =
    if C.(compare w1 w2) <= 0
    then
      w1, expand l1 C.(w2 - w1) l2
    else
      w2, expand l2 C.(w1 - w2) l1

  (* expand l diff l': when l' has head cost diff relative to l, adjust
     and continue mixing as we consume l. *)
  and expand l diff l' =
    lazy(match Lazy.force l with
        | `Nil -> Lazy.force l'
        | `Cons((h, w), t) ->
          let w, next = mix diff l' w t in
          `Cons((h, w), next))

  (* bind preserves cost ordering by mixing the mapped head with the
     recursively bound tail. *)
  let rec bind : type a b. a t -> (a -> b t) -> b t = fun a f ->
    lazy(
      match Lazy.force a with
      | `Nil -> `Nil
      | `Cons((h,w),t) ->
        let _, r = mix C.zero (f h) w (bind t f) in
        Lazy.force r)

  let (let@) = bind
end
