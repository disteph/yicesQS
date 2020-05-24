open Ocamlbuild_plugin

let debug_option = ref false
let () = Options.add ("-debug-mode", Unit(fun ()-> debug_option := true), "allows tracing")

let debug_mode env _build =
  let arg = env "src/debug.mlh" in
  if !debug_option
  then Echo(["[%%define debug_mode true]"], arg)
  else Echo(["[%%define debug_mode false]"], arg)
    
(* let rpaths = string_list_of_file "link.rpath" *)
let static_flags = S [A "-cclib"; A "-static"]

let () = dispatch begin function
    | After_rules ->
      List.iter (
        fun path ->
          let rpath_flags = S [A "-cclib"; A ("-Wl,-rpath," ^ path)] in
          flag ["ocaml"; "link"; "program"; "rpath"] rpath_flags;
          flag ["ocaml"; "link"; "library"; "rpath"] rpath_flags;
      ) [] (* rpaths *);
      flag ["ocaml"; "link"; "program"; "static"] static_flags;
      rule "src/debug.mlh" ~prod:"src/debug.mlh" ~insert:(`top) debug_mode;
      dep ["ocaml"; "ocamldep"] ["src/debug.mlh"];
      dep ["ocaml"; "compile"] ["src/debug.mlh"];
      (* pdep ["ocaml"; "compile"] "autodep" (fun param -> [param]); *)
    | _ -> ()
  end
