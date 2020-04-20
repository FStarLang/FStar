open Dynlink

module U = FStar_Util
module E = FStar_Errors
module O = FStar_Options

let perr  s   = if O.debug_any () then U.print_error s
let perr1 s x = if O.debug_any () then U.print1_error s x

let find_taclib () =
  let r = Process.run "ocamlfind" [| "query"; "fstar-tactics-lib" |] in
  match r with
  | { Process.Output.exit_status = Process.Exit.Exit 0; stdout; _ } ->
      String.trim (List.hd stdout)
  | _ ->
      FStar_Options.fstar_bin_directory ^ "/fstar-tactics-lib"

let dynlink fname =
  try
    perr ("Attempting to load " ^ fname ^ "\n");
    Dynlink.loadfile fname
  with Dynlink.Error e ->
    failwith (U.format2 "Dynlinking %s failed: %s" fname (Dynlink.error_message e))

let load_lib : unit -> unit =
  let already_loaded = ref false in
  fun () ->
    if not (!already_loaded) then begin
      dynlink (find_taclib () ^ "/fstartaclib.cmxs");
      already_loaded := true;
      perr "Loaded fstartaclib successfully\n"
    end

let try_load_lib () =
  (* It might not be there, just try to load it and ignore if not *)
  try load_lib ()
  with | _ -> perr "Did NOT load fstartaclib\n"

let load_tactic tac =
  load_lib ();
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
