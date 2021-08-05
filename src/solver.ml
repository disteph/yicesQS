[%%import "debug.mlh"]

open Containers
(* open Yices2.High *)
open Yices2.Ext_bindings
open Yices2.SMT2

open Command_options

let pp_space fmt () = Format.fprintf fmt " @,"

module HType = Hashtbl.Make(Type)
module HTerm = Hashtbl.Make(Term)

let is_c_line s = Char.equal (String.get s 0) 'c'
  
let p_line s =
  let l = String.split_on_char ' ' s in
  match l with
  | "p"::"cnf"::vars::clauses::[] ->
     int_of_string vars, int_of_string clauses
  | _ -> failwith ("bad p line: "^s)

(* type clause = int list
 * type cnf    = clause list *)
type answer =
  | Unsat
  | Sat of { free : int; total : int }

(* type value = True | False | Free *)
  
exception FromYicesException of Types.error_report * string

let treat filename =
  let l = CCIO.(with_in filename read_lines_l) in
  let nb_var     = ref (-1) in
  let nb_clauses = ref (-1) in
  let skip_zero clause s =
    let i = int_of_string s in
    if i = 0 then clause else i::clause
  in
  let aux cnf line =
    if is_c_line line then cnf
    else if !nb_var = -1
    then
      let vars, clauses = p_line line in
      nb_var := vars;
      nb_clauses := clauses;
      cnf
    else
      let l = String.split_on_char ' ' line in
      let clause = List.fold_left skip_zero [] l in
      clause::cnf
  in
  let cnf = List.fold_left aux [] l in
  let nb_var = !nb_var in
  Global.init();
  let bool_type = Type.bool() in
  let true_term = Term.true0() in
  let false_term = Term.true0() in
  let int2var = Array.make nb_var true_term in
  (* let var2int = HTerm.create (4 * nb_var) in *)
  for i = 1 to nb_var do
    let xi = Term.new_uninterpreted ~name:("x"^string_of_int i) bool_type in
    Array.set int2var (i-1) xi;
    (* HTerm.add var2int xi i; *)
  done;
  let int2var i = Array.get int2var (i-1) in
  (* let var2int xi = HTerm.find var2int xi in *)
  let literal_term lit = if lit < 0 then Term.(not1 (int2var(- lit))) else int2var lit in
  let clause_term clause = Term.orN (List.rev_map literal_term clause) in
  let valid = Term.andN (List.rev_map clause_term cnf) in

  let config = Config.malloc () in
  Config.default ~logic:"QF_BV" config;
  let positive = Context.malloc ~config () in
  let negative = Context.malloc ~config () in
  let param    = Param.malloc () in
  Param.set param ~name:"branching" ~value:"positive";
  Context.assert_formula positive valid;
  Context.assert_formula negative (Term.not1 valid);
  let answer =
    match Context.check ~param positive with
    |  `STATUS_ERROR
       | `STATUS_IDLE
       | `STATUS_INTERRUPTED
       | `STATUS_SEARCHING
       | `STATUS_UNKNOWN -> failwith "Status error in 1st run"
    | `STATUS_UNSAT -> Unsat
    | `STATUS_SAT ->
       (* let bits = Array.make nb_var Free in
        * let free_bits () =
        *   let c = ref 0 in
        *   for i = 0 to nb_var - 1 do
        *     match Array.get bits i with
        *     | Free -> incr c
        *     | _ -> ()
        *   done;
        *   !c
        * in *)
       let fixed_bits = ref 0 in
       let record_model context array =
         let model = Context.get_model context ~keep_subst:true in
         for i = 1 to nb_var do
           let b = Model.get_bool_value model (int2var i) in
           Array.set array (i-1) b
         done
       in
       let model_from_array array =
         let l = ref [] in
         for i = nb_var downto 1 do
           l := (int2var i, if Array.get array (i-1) then true_term else false_term)::!l
         done;
         Model.from_map !l
       in
       let true_model  = ref (Array.make nb_var true) in
       let false_model = ref (Array.make nb_var true) in
       let next_model  = ref (Array.make nb_var true) in
       record_model positive !true_model;
       let halfpoint() =
         let diff_count = ref 0 in    (* Nb of bits where the two models differ *)
         let last_diff = ref (-1) in  (* Index between 0 and n-1 of the last diff *)
         let side = ref true in       (* Which side do we prefer when bits differ *)
         for i = 0 to nb_var - 1 do
           let btrue  = Array.get !true_model  i in
           let bfalse = Array.get !false_model i in
           if not(Bool.equal btrue bfalse)
           then
             begin
               Array.set !next_model i (if !side then btrue else bfalse);
               side := not !side;
               incr diff_count;
               last_diff := i
             end
         done;
         if !diff_count <=1 then Some !last_diff
         else None
       in
       let dichotomy() =
         let bit = ref None in
         while Option.is_none !bit do
           bit := halfpoint();
           match !bit with
           | None ->
              let model = model_from_array !next_model in
              if Model.formula_true_in_model model valid
              then
                begin
                  true_model := !next_model;
                  next_model := !true_model
                end
              else
                begin
                  false_model := !next_model;
                  next_model := !false_model
                end
           | Some _ -> ()
         done;
         let diff_bit = Option.get_exn_or "bad while" !bit in
         diff_bit, Array.get !true_model diff_bit
       in
       let rec fbf_loop = function
         |  `STATUS_ERROR
            | `STATUS_IDLE
            | `STATUS_INTERRUPTED
            | `STATUS_SEARCHING
            | `STATUS_UNKNOWN -> failwith "Status error in loop"
         | `STATUS_SAT ->
            record_model negative !false_model;
            let diff_bit, good_val = dichotomy() in
            let fixed = Term.(int2var diff_bit === (if good_val then true_term else false_term)) in
            Context.assert_formula negative fixed;
            incr fixed_bits;
            fbf_loop (Context.check ~param negative)
         | `STATUS_UNSAT ->
            Sat{ free = nb_var - !fixed_bits; total = nb_var }
       in
       fbf_loop (Context.check ~param negative)
  in
  match answer with
  | Unsat -> Format.(fprintf stdout) "unsat";
  | Sat{free;total} -> Format.(fprintf stdout) "sat %d %d" free total;

                              (* let config = Config.malloc () in *)
                              (* Config.set config ~name:"solver-type" ~value:"mcsat"; *)
                              (* Config.set config ~name:"model-interpolation" ~value:"true"; *)
