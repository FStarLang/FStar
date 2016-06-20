(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.FStar
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Interactive

(* process_args:  parses command line arguments, setting FStar.Options *)
(*                returns an error status and list of filenames        *)
let process_args () : parse_cmdline_res * list<string> =
  Options.parse_cmd_line ()

(* cleanup: kills background Z3 processes; relevant when --n_cores > 1 *)
let cleanup () = Util.kill_all ()

(* printing total error count *)
let report_errors () =
  let errs =
      if (Options.universes())
      then FStar.TypeChecker.Errors.get_err_count()
      else FStar.Tc.Errors.get_err_count () in
  if errs > 0 then begin
    Util.print1_error "%s errors were reported (see above)\n" (string_of_int errs);
    exit 1
  end

(* printing a finished message *)
let finished_message fmods =
  if not (Options.silent()) then begin
    fmods |> List.iter (fun (iface, name) ->
                let tag = if iface then "i'face" else "module" in
                if Options.should_print_message name.str
                then Util.print_string (Util.format2 "Verifying %s: %s\n" tag (Ident.text_of_lid name)));
    print_string (Util.format1 "%s\n" (Util.colorize_bold "All verification conditions discharged successfully"))
  end

(* Extraction to OCaml, F# or Kremlin *)
let codegen uf_mods_env =
  let opt = Options.codegen () in
  if opt <> None then
    let mllibs = match uf_mods_env with
        | Inl (fmods, env) -> snd <| Util.fold_map Extraction.ML.ExtractMod.extract (Extraction.ML.Env.mkContext env) fmods
        | Inr (umods, env) -> snd <| Util.fold_map Extraction.ML.Modul.extract (Extraction.ML.UEnv.mkContext env) umods in
    let mllibs = List.flatten mllibs in
    let ext = match opt with
      | Some "FSharp" -> ".fs"
      | Some "OCaml" -> ".ml"
      | Some "Kremlin" -> ".krml"
      | _ -> failwith "Unrecognized option"
    in
    match opt with
    | Some "FSharp" | Some "OCaml" ->
        let newDocs = List.collect Extraction.ML.Code.doc_of_mllib mllibs in
        List.iter (fun (n,d) ->
          Util.write_file (Options.prepend_output_dir (n^ext)) (FStar.Format.pretty 120 d)
        ) newDocs
    | Some "Kremlin" ->
        let programs = List.flatten (List.map Extraction.Kremlin.translate mllibs) in
        let bin: Extraction.Kremlin.binary_format = Extraction.Kremlin.current_version, programs in
        save_value_to_file "out.krml" bin
   | _ -> failwith "Unrecognized option"



(****************************************************************************)
(* Main function                                                            *)
(****************************************************************************)
let go _ =
  let res, filenames = process_args () in
  match res with
    | Help ->
        Options.display_usage(); exit 0
    | Die msg ->
        Util.print_string msg
    | GoOn ->
        if Options.dep() <> None  //--dep: Just compute and print the transitive dependency graph; don't verify anything
        then Parser.Dep.print (Parser.Dep.collect filenames)
        else if (Options.interactive()) then //--in
          let filenames =
            if (Options.explicit_deps()) then begin
              if List.length filenames = 0 then
                Util.print_error "--explicit_deps was provided without a file list!\n";
                filenames
              end
            else begin
              if List.length filenames > 0 then
                Util.print_warning "ignoring the file list (no --explicit_deps)\n";
                detect_dependencies_with_first_interactive_chunk ()
              end
          in
          if Options.universes()
          then let fmods, dsenv, env = Universal.batch_mode_tc filenames in //check all the dependences in batch mode
               interactive_mode (dsenv, env) None Universal.interactive_tc //and then start checking chunks from the current buffer
          else let fmods, dsenv, env = Stratified.batch_mode_tc filenames in //check all the dependences in batch mode
               interactive_mode (dsenv, env) None Stratified.interactive_tc //and then start checking chunks from the current buffer

        else if List.length filenames >= 1 then begin //normal batch mode
          (* Unless dependencies are explicit, and unless the user used
           * --verify_module manually, we take the filenames passed on
           * the command-line to be those we want to verify. *)
          if not (Options.explicit_deps()) && not (Options.verify_module () <> []) then begin
            let files = 
              List.map (fun f -> 
                    match Parser.Dep.check_and_strip_suffix (basename f) with 
                    | None -> Util.print1 "Unrecognized file type: %s\n" f; exit 1
                    | Some f -> String.lowercase f) filenames in
            List.iter Options.add_verify_module files
          end;
          if Options.universes()
          then let fmods, dsenv, env = Universal.batch_mode_tc filenames in
               report_errors ();
               codegen (Inr (fmods, env));
               finished_message (fmods |> List.map Universal.module_or_interface_name)               
          else let fmods, dsenv, env = Stratified.batch_mode_tc filenames in
               report_errors ();
               codegen (Inl (fmods, env));
               finished_message (fmods |> List.map Stratified.module_or_interface_name)
        end else
          Util.print_error "no file provided\n"

module F_Util = FStar.Absyn.Util
module U_Util = FStar.Syntax.Util

let main () =
  try
    go ();
    cleanup ();
    exit 0
  with | e ->
    (begin 
        if F_Util.handleable e then F_Util.handle_err false () e;
        if U_Util.handleable e then U_Util.handle_err false e;
        if (Options.trace_error()) then
          Util.print2_error "Unexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
        else if not (F_Util.handleable e || U_Util.handleable e) then
          Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e)
     end; 
     cleanup();
     FStar.TypeChecker.Errors.report_all () |> ignore;
     report_errors ();
     exit 1)
