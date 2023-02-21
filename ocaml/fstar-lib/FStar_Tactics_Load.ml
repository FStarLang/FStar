open Dynlink

module U = FStar_Compiler_Util
module E = FStar_Errors
module O = FStar_Options

let perr  s   = if O.debug_any () then U.print_error s
let perr1 s x = if O.debug_any () then U.print1_error s x

let dynlink fname =
  try
    perr ("Attempting to load " ^ fname ^ "\n");
    Dynlink.loadfile fname
  with Dynlink.Error e ->
    let msg = U.format2 "Dynlinking %s failed: %s" fname (Dynlink.error_message e) in
    perr msg;
    failwith msg

let load_tactic tac =
  dynlink tac;
  perr1 "Loaded %s\n" tac

let load_tactics tacs =
    List.iter load_tactic tacs

let load_tactics_dir dir =
    (* Dynlink all .cmxs files in the given directory *)
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun s -> String.length s >= 5 && String.sub s (String.length s - 5) 5 = ".cmxs")
    |> List.map (fun s -> dir ^ "/" ^ s)
    |> List.iter load_tactic

let compile_modules dir ms =
   let compile m =
     let packages = [ "fstar.lib" ] in
     let pkg pname = "-package " ^ pname in
     let args = ["ocamlopt"; "-shared"] (* FIXME shell injection *)
                @ ["-I"; dir]
                @ (List.map pkg packages)
                @ ["-o"; m ^ ".cmxs"; m ^ ".ml"] in
     (* Note: not useful when in an OPAM setting *)
     let ocamlpath_sep = match FStar_Platform.system with
       | Windows -> ";"
       | Posix -> ":"
     in
     let old_ocamlpath = try Sys.getenv "OCAMLPATH" with Not_found -> "" in
     let env_setter = U.format5 "env OCAMLPATH=\"%s/../lib/%s%s/%s%s\""
       FStar_Options.fstar_bin_directory
       ocamlpath_sep
       FStar_Options.fstar_bin_directory
       ocamlpath_sep
       old_ocamlpath
     in
     let cmd = String.concat " " (env_setter :: "ocamlfind" :: args) in
     let rc = Sys.command cmd in
     if rc <> 0
     then E.raise_err (E.Fatal_FailToCompileNativeTactic, (U.format2 "Failed to compile native tactic. Command\n`%s`\nreturned with exit code %s"
                                  cmd (string_of_int rc)))
     else ()
   in
   try
     ms
      |> List.map (fun m -> dir ^ "/" ^ m)
      |> List.iter compile
   with e ->
     perr (U.format1 "Failed to load native tactic: %s\n" (Printexc.to_string e));
     raise e
