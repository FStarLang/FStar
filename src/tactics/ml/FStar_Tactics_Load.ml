open Dynlink

module U = FStar_Util

let loaded_taclib = ref false

let load_tactic tac =
  let dynlink fname =
    try
      Dynlink.loadfile fname
    with Dynlink.Error e ->
      failwith (U.format2 "Dynlinking %s failed: %s" fname (Dynlink.error_message e)) in

  if not !loaded_taclib then begin
      dynlink (FStar_Options.fstar_home () ^ "/bin/fstar-tactics-lib/fstartaclib.cmxs");
      loaded_taclib := true
    end;
  dynlink tac;
  ignore (U.print1 "Dynlinked %s\n" tac)

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
     let packages = ["fstar-tactics-lib"] in
     let pkg pname = "-package " ^ pname in
     let args = ["ocamlopt"; "-shared"] (* FIXME shell injection *)
                @ (List.map pkg packages)
                @ ["-o"; m ^ ".cmxs"; m ^ ".ml"] in
     let env_setter = U.format1 "OCAMLPATH=\"%s/bin/\"" fs_home in
     let cmd = String.concat " " (env_setter :: "ocamlfind" :: args) in
     print_string (cmd ^ "\n");
     Sys.command cmd in
    ms
    |> List.map (fun m -> dir ^ "/" ^ m)
    |> List.iter (fun x -> ignore (compile x))
