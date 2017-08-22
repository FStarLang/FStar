open Dynlink
module U = FStar_Util

let load_tactic s =
    let _ = (try Dynlink.loadfile s with
    | e ->
        let str =
            match e with
            | Dynlink.Error e -> Dynlink.error_message e
            | _ -> "Could not dynlink tactic"
        in
        failwith str) in
    U.print1 "Dynlinked %s\n" tac;
    ()

let load_tactics tacs =
    List.iter load_tactic tacs

 let load_tactics_dir dir =
    (* Dynlink all .cmxs files in the given directory *)
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun s -> String.sub s (String.length s - 4) 4 = "cmxs")
    |> List.map (fun s -> dir ^ "/" ^ s)
    |> List.iter load_tactic

let compile_modules dir ms =
    let fs_home = FStar_Options.fstar_home () in
    let compile m =
        Sys.command ("ocamlfind ocamlopt -shared " ^
        "-I " ^ fs_home ^ "/src/ocaml-output/_build/src/tactics/ml " ^
        "-I " ^ fs_home ^ "/src/ocaml-output/_build/ulib/ml " ^
        "-I " ^ fs_home ^ "/src/ocaml-output/_build/ulib/ml/compiler " ^
        "-I " ^ fs_home ^ "/src/ocaml-output/_build/src/ocaml-output/ " ^
        "-I " ^ fs_home ^ "/src/ocaml-output/_build/src/basic/ml " ^
        "-linkpkg -package zarith -o " ^ m ^ ".cmxs " ^ m ^ ".ml") in
    ms
    |> List.map (fun m -> dir ^ "/" ^ m)
    |> List.iter (fun x -> compile x; ())
