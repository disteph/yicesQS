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

let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs
let flush () = Format.(fprintf stdout) "@]%!@[<v>"

let treat filename =
  print 1 "@,@[Parsing file@]";
  let l = CCIO.(with_in filename read_lines_l) in
  print 1 "@,@[done. building CNF in memory.@]";
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
  print 1 "@,@[done, with %d bits@]" nb_var;
  Global.init();
  let bool_type = Type.bool() in
  let true_term = Term.true0() in
  let false_term = Term.false0() in
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
  print 2 "@,@[Starting first run (%d vars, %d clauses)@]" nb_var !nb_clauses;
  let answer =
    match Context.check ~param positive with
    |  `STATUS_ERROR
       | `STATUS_IDLE
       | `STATUS_INTERRUPTED
       | `STATUS_SEARCHING
       | `STATUS_UNKNOWN -> failwith "Status error in 1st run"
    | `STATUS_UNSAT ->
       Unsat
    | `STATUS_SAT ->
       print 1 "@,@[sat. looking for free bits@]";
       print 1 "@,@[Formula is %a@]" Term.pp valid;
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
       flush();
       let fixed_bits = ref 0 in
       let record_model context array =
         let model = Context.get_model context ~keep_subst:true in
         print 2 "@,@[Recording model %a@]" Model.pp model;
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
         if !diff_count <= 1 then Some !last_diff
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
                  let tmp = !true_model in
                  true_model := !next_model;
                  next_model := tmp
                end
              else
                begin
                  let tmp = !false_model in
                  false_model := !next_model;
                  next_model := tmp
                end
           | Some _ -> ()
         done;
         let diff_bit = Option.get_exn_or "bad while" !bit in
         diff_bit+1, Array.get !true_model diff_bit
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
            let fixed = Term.(if good_val then int2var diff_bit else not1(int2var diff_bit)) in
            print 2 "@,@[Adding assumption %a@]" Term.pp fixed;
            Context.assert_formula negative fixed;
            incr fixed_bits;
            print 2 "@,@[fixing %dth bit: bit %d to %b@]" !fixed_bits diff_bit good_val;
            let status = Context.check ~param negative in
            print 3 "@,@[Updated context_false@]";
            fbf_loop status
         | `STATUS_UNSAT ->
            Sat{ free = nb_var - !fixed_bits; total = nb_var }
       in
       print 3 "@,@[Checking context_false@]";
       let status = Context.check ~param negative in
       print 3 "@,@[Updated context_false@]";
       fbf_loop status
  in
  match answer with
  | Unsat -> Format.(fprintf stdout) "unsat";
  | Sat{free;total} -> Format.(fprintf stdout) "sat %d %d" free total;
