open Dynlink

module U = FStar_Util
module E = FStar_Errors

let loaded_taclib = ref false

(* We had weird failures, so don't trust in Dynlink.error_message *)
let error_message : Dynlink.error -> string =
    fun e ->
    let s = match e with
    | Not_a_bytecode_file _ -> "Not_a_bytecode_file"
    | Inconsistent_import _ -> "Inconsistent_import"
    | Unavailable_unit _ -> "Unavailable_unit"
    | Unsafe_file -> "Unsafe_file"
    | Linking_error _ -> "Linking_error"
    | Corrupted_interface _ -> "Corrupted_interface"
    | File_not_found _ -> "File_not_found"
    | Cannot_open_dll _ -> "Cannot_open_dll"
    | Inconsistent_implementation _ -> "Inconsistent_implementation"
    in s ^ ": " ^ Dynlink.error_message e

let find_taclib () =
  let r = Process.run "ocamlfind" [| "query"; "fstar-tactics-lib" |] in
  match r with
  | { Process.Output.exit_status = Process.Exit.Exit 0; stdout; _ } ->
      String.trim (List.hd stdout)
  | _ ->
      FStar_Options.fstar_bin_directory ^ "/fstar-tactics-lib"


let load_tactic tac =
  let dynlink fname =
    try
      print_string ("Loading plugin from " ^ fname ^ "\n");
      Dynlink.loadfile fname
    with Dynlink.Error e ->
      failwith (U.format2 "Dynlinking %s failed: %s" fname (error_message e)) in

  if not !loaded_taclib then begin
    dynlink (find_taclib () ^ "/fstartaclib.cmxs");
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
    |> List.filter (fun s -> String.length s >= 5 && String.sub s (String.length s - 5) 5 = ".cmxs")
    |> List.map (fun s -> dir ^ "/" ^ s)
    |> List.iter load_tactic

let compile_modules dir ms =
   let compile m =
     let packages = ["fstar-tactics-lib"] in
     let pkg pname = "-package " ^ pname in
     let args = ["ocamlopt"; "-shared"] (* FIXME shell injection *)
                @ ["-I"; dir]
                @ (List.map pkg packages)
                @ ["-o"; m ^ ".cmxs"; m ^ ".ml"] in
     (* Note: not useful when in an OPAM setting *)
     let env_setter = U.format1 "env OCAMLPATH=\"%s/\"" FStar_Options.fstar_bin_directory in
     let cmd = String.concat " " (env_setter :: "ocamlfind" :: args) in
     let rc = Sys.command cmd in
     if rc <> 0
     then E.raise_err (E.Fatal_FailToCompileNativeTactic, (U.format2 "Failed to compile native tactic. Command\n`%s`\nreturned with exit code %s"
                                  cmd (string_of_int rc)))
     else ()
   in ms
      |> List.map (fun m -> dir ^ "/" ^ m)
      |> List.iter compile
