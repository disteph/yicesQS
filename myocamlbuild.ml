open Ocamlbuild_plugin

let static_flags = S [A "-cclib"; A "-static"]

let debug value env _build =
  print_endline("debug is "^value);
  let arg = env "%/debug.mlh" in
  Echo(["[%%define debug_mode "^value^"]"], arg)

let () = dispatch begin function
    | After_rules ->
      let mode = try
          if getenv "MODE" = "debug" then "true" else "false"
        with _ -> "false"
      in
      rule "debug.mlh true"  ~prod:"%/debug.mlh" ~insert:(`top) (debug mode);
      dep ["ocaml"; "compile"]   ["src/debug.mlh"];
      dep ["ocaml"; "ocamldep"]  ["src/debug.mlh"];
      List.iter (
        fun path ->
          let rpath_flags = S [A "-cclib"; A ("-Wl,-rpath," ^ path)] in
          flag ["ocaml"; "link"; "program"; "rpath"] rpath_flags;
          flag ["ocaml"; "link"; "library"; "rpath"] rpath_flags;
      ) [] (* rpaths *);
      (* flag ["ocaml"; "link"; "program"; "static"] static_flags; *)
      (* pdep ["ocaml"; "compile"] "autodep" (fun param -> [param]); *)
      (try
         let ldflags = getenv "LDFLAGS" in
         print_endline("Using \"-ccopt "^ldflags^"\" from LDFLAGS environment variable.");
         flag ["ocaml"; "link"] (S [A "-ccopt"; A ldflags])
       with
         _ -> ())
    | _ -> ()
  end
