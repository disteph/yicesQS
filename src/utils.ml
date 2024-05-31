[%%import "debug.mlh"]

open Containers

open Ext

[%%if debug_mode]
let print trace = Tracing.print Format.stdout trace
[%%else]
(* let print trace = Tracing.iprint Format.stdout trace *)
let print _trace _i fs = Format.ifprintf Format.stdout fs
[%%endif]

let pp_space fmt () = Format.fprintf fmt " @,"

module CLL = CLazyList.Make(struct include Int let zero = 0 end)

module type Monad = sig
  type 'a t
  val return : 'a -> 'a t
  val bind   : 'a t -> ('a -> 'b t) -> 'b t
  val (let+) : 'a t -> ('a -> 'b t) -> 'b t
end

module StateMonad(State: sig type t end) : Monad with type 'a t = State.t -> 'a*State.t
  = struct
  type state = State.t
  type 'a t = state -> 'a * state
  let return a s = a,s
  let bind a f s = let a,s = a s in f a s
  let (let+) = bind 
end

module WithEpsilons = struct
  type 'a t = {
      main     : 'a;
      epsilons : Term.t list
    }
  let return main = { main; epsilons = [] }
end

module WithEpsilonsMonad : Monad with type 'a t = Term.t list -> 'a WithEpsilons.t = struct 
  type 'a t = Term.t list -> 'a WithEpsilons.t
  let return main epsilons = WithEpsilons.{ main; epsilons }
  let bind a f s =
    let WithEpsilons.{ main; epsilons } = a s in
    f main epsilons
  let (let+) = bind
end

module ListWithEpsilons = Yices2.Common.MList(WithEpsilonsMonad)

module MSeq(M : Monad) = struct
  open M
  let (let++) = bind
              
  let fold  (aux : 'a -> 'b -> 'a M.t) =
    let aux sofar c =
      let++ sofar = sofar in
      aux sofar c
    in
    Seq.fold_left aux

  let map f l =
    let aux sofar c =
      let++ c = f c in
      return(Seq.(append sofar (singleton c)))
    in
    fold aux (return Seq.nil) l
end

module SeqWithEpsilons = MSeq(WithEpsilonsMonad)

let rec get_disjuncts t =
  let open Term in
  match reveal t with
  | Term(Astar(`YICES_OR_TERM,l)) ->
     l |> List.map get_disjuncts |> List.flatten
  | _ -> [t]

let get_conjuncts t = 
  let open Term in
  match reveal t with
  | Term(A1(`YICES_NOT_TERM, t)) ->
     get_disjuncts t |> List.map Term.not1 |> List.sort_uniq ~cmp:Term.compare
  | _ -> [t]

type logic = [ `NRA | `NIA | `LRA | `LIA | `BV | `Other ]
