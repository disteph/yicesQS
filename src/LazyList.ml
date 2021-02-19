type 'a t = 'a node Lazy.t
and 'a node = [`Nil | `Cons of 'a * 'a t]

let empty = lazy `Nil
let return a = lazy (`Cons(a,empty))

let rec length l = match Lazy.force l with
  | `Nil -> 0
  | `Cons(_,l) -> length l+1

let rec fold : ('b Lazy.t -> 'a -> 'b) -> 'b Lazy.t -> 'a t -> 'b Lazy.t
  = fun f seed l -> lazy (match Lazy.force l with
                          | `Nil -> Lazy.force seed
                          | `Cons(head,tail) -> f (fold f seed tail) head)

let map (type a b) (f : a -> b) (l : a t) =
  fold (fun nexts element -> `Cons(f element, nexts)) empty l

let append (type a) (s1 : a t) (s2 : a t) : a t =
  fold (fun nexts element -> `Cons(element, nexts)) s2 s1

let bind (type a b) (l : a t) (f : a -> b t) : b t =
  fold (fun nexts element -> Lazy.force (append (f element) nexts)) empty l

let flatten (type a) (l : a t t) : a t = bind l (fun x -> x)
                                       
let rec extract n l =
  if n <= 0 then []
  else
    match Lazy.force l with
    | `Nil -> []
    | `Cons(head,tail) -> head::(extract (n-1) tail)
