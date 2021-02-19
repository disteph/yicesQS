module Make(C : sig
    type t [@@deriving ord]
    val zero : t
    val (-) : t -> t -> t
  end) = struct

  type 'a t = ('a * C.t) LazyList.t

  let return a = LazyList.return(a,C.zero)

  let rec mix w1 l1 w2 l2 =
    if C.(compare w1 w2) <= 0
    then
      w1, expand l1 C.(w2 - w1) l2
    else
      w2, expand l2 C.(w1 - w2) l1

  and expand l diff l' =
    lazy(match Lazy.force l with
        | `Nil -> Lazy.force l'
        | `Cons((h, w), t) ->
          let w, next = mix diff l' w t in
          `Cons((h, w), next))

  let rec bind : type a b. a t -> (a -> b t) -> b t = fun a f ->
    lazy(
      match Lazy.force a with
      | `Nil -> `Nil
      | `Cons((h,w),t) ->
        let _, r = mix C.zero (f h) w (bind t f) in
        Lazy.force r)

  let (let@) = bind
end
