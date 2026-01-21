(* Simple lazy list used to enumerate candidates in MBU/IC without
   materializing whole lists. *)
type 'a t = 'a node Lazy.t
and 'a node = [`Nil | `Cons of 'a * 'a t]

(* Empty lazy list. *)
let empty = lazy `Nil
(* Singleton lazy list. *)
let return a = lazy (`Cons(a,empty))

(* Length of a lazy list (forces the full list). *)
let rec length l = match Lazy.force l with
  | `Nil -> 0
  | `Cons(_,l) -> length l+1

(* fold f seed l:
   - f consumes the tail (as a lazy value) and the head
   - seed is the lazy base case
   Returns a lazy result to preserve on-demand traversal. *)
let rec fold : ('b Lazy.t -> 'a -> 'b) -> 'b Lazy.t -> 'a t -> 'b Lazy.t
  = fun f seed l -> lazy (match Lazy.force l with
                          | `Nil -> Lazy.force seed
                          | `Cons(head,tail) -> f (fold f seed tail) head)

(* Lazy map. *)
let map (type a b) (f : a -> b) (l : a t) =
  fold (fun nexts element -> `Cons(f element, nexts)) empty l

(* Lazy append. *)
let append (type a) (s1 : a t) (s2 : a t) : a t =
  fold (fun nexts element -> `Cons(element, nexts)) s2 s1

(* Lazy monadic bind. *)
let bind (type a b) (l : a t) (f : a -> b t) : b t =
  fold (fun nexts element -> Lazy.force (append (f element) nexts)) empty l

(* Flatten a lazy list of lazy lists. *)
let flatten (type a) (l : a t t) : a t = bind l (fun x -> x)
                                       
(* Take the first n elements, forcing as needed. *)
let rec extract n l =
  if n <= 0 then []
  else
    match Lazy.force l with
    | `Nil -> []
    | `Cons(head,tail) -> head::(extract (n-1) tail)
