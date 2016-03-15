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
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

(* cleanup: kills background Z3 processes; relevant when --n_cores > 1 *)
let cleanup () = Util.kill_all ()

(* printing total error count *)
let report_errors nopt =
  let errs =
    match nopt with
    | None -> 
      if !Options.universes
      then FStar.TypeChecker.Errors.get_err_count()
      else FStar.Tc.Errors.get_err_count ()
    | Some n -> n in
  if errs > 0 then begin
    Util.print1_error "%s errors were reported (see above)\n" (string_of_int errs);
    exit 1
  end

(* printing a finished message *)
let finished_message fmods =
  if not !Options.silent then begin
    let msg =
      if !Options.verify then "Verifying"
      else if !Options.pretype then "Lax type-checked"
      else "Parsed and desugared" in
        fmods |> List.iter (fun (iface, name) ->
                 let tag = if iface then "i'face" else "module" in
                 if Options.should_print_message name.str
                 then Util.print_string (Util.format3 "%s %s: %s\n" msg tag (Ident.text_of_lid name)));
        print_string (Util.format1 "%s\n" (Util.colorize_bold "All verification conditions discharged successfully"))
    end

(* Extraction to OCaml or F# *)
let codegen uf_mods_env =
  if !Options.codegen = Some "OCaml" ||
     !Options.codegen = Some "FSharp"
  then begin
    let mllibs = match uf_mods_env with 
        | Inl (fmods, env) -> snd <| Util.fold_map Extraction.ML.ExtractMod.extract (Extraction.ML.Env.mkContext env) fmods
        | Inr (umods, env) -> snd <| Util.fold_map Extraction.ML.Modul.extract (Extraction.ML.UEnv.mkContext env) umods in
    let mllibs = List.flatten mllibs in
    let ext = if !Options.codegen = Some "FSharp" then ".fs" else ".ml" in
    let newDocs = List.collect Extraction.ML.Code.doc_of_mllib mllibs in
    List.iter (fun (n,d) -> Util.write_file (Options.prependOutputDir (n^ext)) (FStar.Format.pretty 120 d)) newDocs
    end

(****************************************************************************)
(* Main function                                                            *)
(****************************************************************************)
let go _ =
  let res, filenames = process_args () in
  match res with
    | Help ->
        Options.display_usage (Options.specs())
    | Die msg ->
        Util.print_string msg
    | GoOn ->
        if !Options.dep <> None  //--dep: Just compute and print the transitive dependency graph; don't verify anything
        then Parser.Dep.print (Parser.Dep.collect filenames)
        else if !Options.interactive then //--in
          let filenames =
            if !Options.explicit_deps then begin
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
          if !Options.universes
          then let fmods, dsenv, env = Universal.batch_mode_tc filenames in //check all the dependences in batch mode
               interactive_mode (dsenv, env) None Universal.interactive_tc //and then start checking chunks from the current buffer
          else let fmods, dsenv, env = Stratified.batch_mode_tc filenames in //check all the dependences in batch mode
               interactive_mode (dsenv, env) None Stratified.interactive_tc //and then start checking chunks from the current buffer

        else if List.length filenames >= 1 then //normal batch mode
          if !Options.universes
          then let fmods, dsenv, env = Universal.batch_mode_tc filenames in
               report_errors None;
               codegen (Inr (fmods, env));
               finished_message (fmods |> List.map Universal.module_or_interface_name)               
          else let fmods, dsenv, env = Stratified.batch_mode_tc filenames in
               report_errors None;
               codegen (Inl (fmods, env));
               finished_message (fmods |> List.map Stratified.module_or_interface_name)
        else
          Util.print_error "no file provided\n"

module F_Util = FStar.Absyn.Util
module U_Util = FStar.Syntax.Util

let main () =
  try
    go ();
    cleanup ();
    exit 0
  with | e ->
    if F_Util.handleable e then F_Util.handle_err false () e;
    if U_Util.handleable e then U_Util.handle_err false () e;
    if !Options.trace_error then
      Util.print2_error "Unexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
    else if not (F_Util.handleable e || U_Util.handleable e) then
      Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e);
      cleanup ();
      exit 1
