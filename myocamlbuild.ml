open Ocamlbuild_plugin

let static_flags = S [A "-cclib"; A "-static"]

let () = dispatch begin function
    | After_rules ->
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
