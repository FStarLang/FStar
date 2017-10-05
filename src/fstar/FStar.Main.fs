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
module FStar.Main
open FStar.ST
open FStar.All
open FStar.Util
open FStar.Getopt
open FStar.Ident

let () = FStar.Version.dummy ()

(* process_args:  parses command line arguments, setting FStar.Options *)
(*                returns an error status and list of filenames        *)
let process_args () : parse_cmdline_res * list<string> =
  Options.parse_cmd_line ()

(* cleanup: kills background Z3 processes; relevant when --n_cores > 1 *)
let cleanup () = Util.kill_all ()

(* printing a finished message *)
let finished_message fmods errs =
  let print_to = if errs > 0 then Util.print_error else Util.print_string in
  if not (Options.silent()) then begin
    fmods |> List.iter (fun ((iface, name), time) ->
                let tag = if iface then "i'face (or impl+i'face)" else "module" in
                if Options.should_print_message name.str
                then if time >= 0
                then print_to (Util.format3 "Verified %s: %s (%s milliseconds)\n"
                                                        tag (Ident.text_of_lid name) (Util.string_of_int time))
                else print_to (Util.format2 "Verified %s: %s\n" tag (Ident.text_of_lid name)));
    if errs > 0
    then if errs = 1
         then Util.print_error "1 error was reported (see above)\n"
         else Util.print1_error "%s errors were reported (see above)\n" (string_of_int errs)
    else print1 "%s\n" (Util.colorize_bold "All verification conditions discharged successfully")
  end

(* printing total error count *)
let report_errors fmods =
  FStar.Errors.report_all () |> ignore;
  let nerrs = FStar.Errors.get_err_count() in
  if nerrs > 0 then begin
    finished_message fmods nerrs;
    exit 1
  end

(* Extraction to OCaml, F# or Kremlin *)
let codegen (umods, env) =
  let opt = Options.codegen () in
  if opt <> None then
    let mllibs = snd <| Util.fold_map Extraction.ML.Modul.extract (Extraction.ML.UEnv.mkContext env) umods in
    let mllibs = List.flatten mllibs in
    let ext = match opt with
      | Some "FSharp" -> ".fs"
      | Some "OCaml" -> ".ml"
      | Some "Kremlin" -> ".krml"
      | _ -> failwith "Unrecognized option"
    in
    match opt with
    | Some "FSharp" | Some "OCaml" ->
        (* When bootstrapped in F#, this will use the old printer in
           FStar.Extraction.ML.Code for both OCaml and F# extraction.
           When bootstarpped in OCaml, this will use the old printer
           for F# extraction and the new printer for OCaml extraction. *)
        let outdir = Options.output_dir() in
        List.iter (FStar.Extraction.ML.PrintML.print outdir ext) mllibs
    | Some "Kremlin" ->
        let programs = List.flatten (List.map Extraction.Kremlin.translate mllibs) in
        let bin: Extraction.Kremlin.binary_format = Extraction.Kremlin.current_version, programs in
        save_value_to_file (Options.prepend_output_dir "out.krml") bin
   | _ -> failwith "Unrecognized option"

let gen_native_tactics (umods, env) out_dir =
    (* Extract module and its dependencies to OCaml *)
    Options.set_option "codegen" (Options.String "OCaml");
    let mllibs = snd <| Util.fold_map Extraction.ML.Modul.extract (Extraction.ML.UEnv.mkContext env) umods in
    let mllibs = List.flatten mllibs in
    List.iter (FStar.Extraction.ML.PrintML.print (Some out_dir) ".ml") mllibs;

    (* Compile the modules which contain tactics into dynamically-linkable OCaml plugins *)
    let user_tactics_modules = Universal.user_tactics_modules in
    Tactics.Load.compile_modules out_dir (!user_tactics_modules)

let init_native_tactics () =
  Tactics.Load.load_tactics (Options.load ());
  match Options.use_native_tactics () with
  | Some dir ->
      Util.print1 "Using native tactics from %s\n" dir;
      Tactics.Load.load_tactics_dir dir
  | None -> ()

(****************************************************************************)
(* Main function                                                            *)
(****************************************************************************)
let go _ =
  let res, filenames = process_args () in
  match res with
    | Help ->
        Options.display_usage(); exit 0
    | Error msg ->
        Util.print_string msg
    | Success ->
        init_native_tactics ();

        if Options.dep() <> None  //--dep: Just compute and print the transitive dependency graph; don't verify anything
        then Parser.Dep.print (Parser.Dep.collect Parser.Dep.VerifyAll filenames)
        else if Options.interactive () then begin //--in
          if Options.explicit_deps () then begin
            Util.print_error "--explicit_deps incompatible with --in\n";
            exit 1
          end;
          if List.length filenames <> 1 then begin
            Util.print_error "fstar-mode.el should pass the current filename to F*\n";
            exit 1
          end;
          let filename = List.hd filenames in

          if Options.verify_module () <> [] then
            Util.print_warning "Interactive mode; ignoring --verify_module";

          (* interactive_mode takes care of calling [find_deps_if_needed] *)
          if Options.legacy_interactive () then FStar.Interactive.Legacy.interactive_mode filename
          else FStar.Interactive.Ide.interactive_mode filename
	    //and then start checking chunks from the current buffer
        end //end interactive mode
        else if Options.doc() then // --doc Generate Markdown documentation files
          FStar.Fsdoc.Generator.generate filenames
        else if Options.indent () then
          if FStar.Platform.is_fstar_compiler_using_ocaml
          then FStar.Indent.generate filenames
          else failwith "You seem to be using the F#-generated version ofthe compiler ; \
                         reindenting is not known to work yet with this version"
        else if List.length filenames >= 1 then begin //normal batch mode
          let verify_mode =
            if Options.verify_all () then begin
              if Options.verify_module () <> [] then begin
                Util.print_error "--verify_module is incompatible with --verify_all";
                exit 1
              end;
              Parser.Dep.VerifyAll
            end else if Options.verify_module () <> [] then
              Parser.Dep.VerifyUserList
            else
              Parser.Dep.VerifyFigureItOut
          in
          let filenames = FStar.Dependencies.find_deps_if_needed verify_mode filenames in
          (match Options.gen_native_tactics () with
          | Some dir ->
             Util.print1 "Generating native tactics in %s\n" dir;
             Options.set_option "lax" (Options.Bool true)
          | None -> ());
          let fmods, env = Universal.batch_mode_tc filenames in
          let module_names_and_times = fmods |> List.map (fun (x, t) -> Universal.module_or_interface_name x, t) in
          report_errors module_names_and_times;
          codegen (fmods |> List.map fst, env);
          (match Options.gen_native_tactics () with
          | Some dir ->
              gen_native_tactics (fmods |> List.map fst, env) dir
          | None -> ());
          finished_message module_names_and_times 0
        end //end normal batch mode
        else
          Util.print_error "no file provided\n"


let main () =
  try
    go ();
    cleanup ();
    exit 0
  with | e ->
    let trace = Util.trace_of_exn e in
    begin
      if FStar.Errors.handleable e then FStar.Errors.err_exn e;
      if (Options.trace_error()) then
        Util.print2_error "Unexpected error\n%s\n%s\n" (Util.message_of_exn e) trace
      else if not (FStar.Errors.handleable e) then
        Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e)
    end;
    cleanup();
    report_errors [];
    exit 1
