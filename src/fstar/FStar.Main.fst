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
module FStar.Main
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Compiler.Util
open FStar.Getopt
open FStar.Ident
open FStar.CheckedFiles
open FStar.Universal
open FStar.Compiler

open FStar.Class.Show

module E = FStar.Errors
module UF = FStar.Syntax.Unionfind
module RE = FStar.Reflection.V2.Embeddings

let _ = FStar.Version.dummy ()

(* These modules only mentioned to put them in the dep graph
and hence compile and link them in. They do not export anything,
instead they register primitive steps in the normalizer during
initialization. *)
open FStar.Reflection.V1.Interpreter {}
open FStar.Reflection.V2.Interpreter {}

(* process_args:  parses command line arguments, setting FStar.Options *)
(*                returns an error status and list of filenames        *)
let process_args () : parse_cmdline_res & list string =
  Options.parse_cmd_line ()

(* cleanup: kills background Z3 processes; relevant when --n_cores > 1 *)
(* GM: unclear if it's useful now? *)
let cleanup () = Util.kill_all ()

(* printing a finished message *)
let finished_message fmods errs =
  let print_to = if errs > 0 then Util.print_error else Util.print_string in
  if not (Options.silent()) then begin
    fmods |> List.iter (fun (iface, name) ->
                let tag = if iface then "i'face (or impl+i'face)" else "module" in
                if Options.should_print_message (string_of_lid name)
                then print_to (Util.format2 "Verified %s: %s\n" tag (Ident.string_of_lid name)));
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

let load_native_tactics () =
    let modules_to_load = Options.load() |> List.map Ident.lid_of_str in
    let cmxs_to_load = Options.load_cmxs () |> List.map Ident.lid_of_str in
    let ml_module_name m = FStar.Extraction.ML.Util.ml_module_name_of_lid m in
    let ml_file m = ml_module_name m ^ ".ml" in
    let cmxs_file m =
        let cmxs = ml_module_name m ^ ".cmxs" in
        match FStar.Options.find_file cmxs with
        | Some f -> f
        | None ->
          if List.contains m cmxs_to_load  //if this module comes from the cmxs list, fail hard
          then E.raise_error0 E.Fatal_FailToCompileNativeTactic (Util.format1 "Could not find %s to load" cmxs)
          else  //else try to find and compile the ml file
            match FStar.Options.find_file (ml_file m) with
            | None ->
              E.raise_error0 E.Fatal_FailToCompileNativeTactic
                (Util.format1 "Failed to compile native tactic; extracted module %s not found" (ml_file m))
            | Some ml ->
              let dir = Util.dirname ml in
              FStar.Tactics.Load.compile_modules dir [ml_module_name m];
              begin match FStar.Options.find_file cmxs with
                | None ->
                  E.raise_error0 E.Fatal_FailToCompileNativeTactic
                    (Util.format1 "Failed to compile native tactic; compiled object %s not found" cmxs)
                | Some f -> f
              end
    in
    let cmxs_files = (modules_to_load@cmxs_to_load) |> List.map cmxs_file in
    if Debug.any () then
      Util.print1 "Will try to load cmxs files: [%s]\n" (String.concat ", " cmxs_files);
    Tactics.Load.load_tactics cmxs_files;
    iter_opt (Options.use_native_tactics ()) Tactics.Load.load_tactics_dir;
    ()


(* Need to keep names of input files for a second pass when prettyprinting *)
(* This reference is set once in `go` and read in `main` if the print or *)
(* print_in_place options are passed *)
let fstar_files: ref (option (list string)) = Util.mk_ref None

(****************************************************************************)
(* Main function                                                            *)
(****************************************************************************)
let go _ =
  let res, filenames = process_args () in
  if Options.trace_error () then begin
    let h = get_sigint_handler () in
    let h' s =
      let open FStar.Pprint in
      let open FStar.Errors.Msg in
      Debug.enable (); (* make sure diag is printed *)
      Options.set_option "error_contexts" (Options.Bool true);
      (* ^ Print context. Stack trace will be added since we have trace_error. *)
      Errors.diag Range.dummyRange [
        text "GOT SIGINT! Exiting";
      ];
      exit 1
    in
    set_sigint_handler (sigint_handler_f h')
  end;
  match res with
    | Empty ->
        Options.display_usage(); exit 1

    | Help ->
        Options.display_usage(); exit 0

    | Error msg ->
        Util.print_error msg; exit 1

    | _ when Options.print_cache_version () ->
        Util.print1 "F* cache version number: %s\n"
                     (string_of_int FStar.CheckedFiles.cache_version_number);
        exit 0

    | Success ->
        fstar_files := Some filenames;

        if Debug.any () then (
          Util.print1 "- F* executable: %s\n" (Util.exec_name);
          Util.print1 "- F* exec dir: %s\n" (Options.fstar_bin_directory);
          Util.print1 "- Library root: %s\n" ((Util.dflt "<none>" (Options.lib_root ())));
          Util.print1 "- Full include path: %s\n" (show (Options.include_path ()));
          Util.print_string "\n";
          ()
        );

        load_native_tactics ();

        (* Set the unionfind graph to read-only mode.
         * This will be unset by the typechecker and other pieces
         * of code that intend to use it. It helps us catch errors. *)
        (* TODO: also needed by the interactive mode below. *)
        UF.set_ro ();

        (* --dep: Just compute and print the transitive dependency graph;
                  don't verify anything *)
        if Options.dep() <> None
        then let _, deps = Parser.Dep.collect filenames FStar.CheckedFiles.load_parsing_data_from_cache in
             Parser.Dep.print deps;
             report_errors []

        (* --print: Emit files in canonical source syntax *)
        else if Options.print () || Options.print_in_place () then
          if FStar.Platform.is_fstar_compiler_using_ocaml
          then let printing_mode =
                   if Options.print ()
                   then FStar.Prettyprint.FromTempToStdout
                   else FStar.Prettyprint.FromTempToFile
               in
               FStar.Prettyprint.generate printing_mode filenames
          else failwith "You seem to be using the F#-generated version ofthe compiler ; \o
                         reindenting is not known to work yet with this version"

        (* --read_checked: read and print a checked file *)
        else if Some? (Options.read_checked_file ()) then
          let path = Some?.v <| Options.read_checked_file () in
          let env = Universal.init_env Parser.Dep.empty_deps in
          let res = FStar.CheckedFiles.load_tc_result path in
          match res with
          | None ->
            let open FStar.Pprint in
            Errors.raise_error0 Errors.Fatal_ModuleOrFileNotFound [
                Errors.Msg.text "Could not read checked file:" ^/^ doc_of_string path
              ]

          | Some (_, tcr) ->
            print1 "%s\n" (show tcr.checked_module)

        else if Options.list_plugins () then
          let ps = FStar.TypeChecker.Cfg.list_plugins () in
          let ts = FStar.Tactics.Interpreter.native_tactics_steps () in
          Util.print1 "Registered plugins:\n%s\n" (String.concat "\n" (List.map (fun p -> "  " ^ show p.FStar.TypeChecker.Primops.Base.name) ps));
          Util.print1 "Registered tactic plugins:\n%s\n" (String.concat "\n" (List.map (fun p -> "  " ^ show p.FStar.TypeChecker.Primops.Base.name) ts));
          ()

        else if Options.locate () then (
          Util.print1 "%s\n" (Util.get_exec_dir () |> Util.normalize_file_path);
          exit 0

        ) else if Options.locate_lib () then (
          match Options.lib_root () with
          | None ->
            Util.print_error "No library found (is --no_default_includes set?)\n";
            exit 1
          | Some s ->
            Util.print1 "%s\n" (Util.normalize_file_path s);
            exit 0

        ) else if Options.locate_ocaml () then (
          // This is correct right now, but probably should change.
          Util.print1 "%s\n" (Util.get_exec_dir () ^ "/../lib" |> Util.normalize_file_path);
          exit 0

        ) else if Some? (Options.read_krml_file ()) then
          let path = Some?.v <| Options.read_krml_file () in
          match load_value_from_file path <: option FStar.Extraction.Krml.binary_format with
          | None ->
            let open FStar.Pprint in
            Errors.raise_error0 Errors.Fatal_ModuleOrFileNotFound [
                Errors.Msg.text "Could not read krml file:" ^/^ doc_of_string path
              ]
          | Some (version, files) ->
            print1 "Karamel format version: %s\n" (show version);
            (* Just "show decls" would print it, we just format this a bit *)
            files |> List.iter (fun (name, decls) ->
              print1 "%s:\n" name;
              decls |> List.iter (fun d -> print1 "  %s\n" (show d))
            )

        (* --lsp *)
        else if Options.lsp_server () then
          FStar.Interactive.Lsp.start_server ()

        (* For the following cases we might need native tactics, try to load *)
        else begin

        (* --ide, --in: Interactive mode *)
        if Options.interactive () then begin
          UF.set_rw ();
          match filenames with
          | [] -> (* input validation: move to process args? *)
            Errors.log_issue0 Errors.Error_MissingFileName
              "--ide: Name of current file missing in command line invocation\n";
            exit 1
          | _ :: _ :: _ -> (* input validation: move to process args? *)
            Errors.log_issue0 Errors.Error_TooManyFiles
              "--ide: Too many files in command line invocation\n";
            exit 1
          | [filename] ->
            if Options.legacy_interactive () then
              FStar.Interactive.Legacy.interactive_mode filename
            else
              FStar.Interactive.Ide.interactive_mode filename
          end

        (* Normal, batch mode compiler *)
        else if List.length filenames >= 1 then begin //normal batch mode
          let filenames, dep_graph = FStar.Dependencies.find_deps_if_needed filenames FStar.CheckedFiles.load_parsing_data_from_cache in
          let tcrs, env, cleanup = Universal.batch_mode_tc filenames dep_graph in
          ignore (cleanup env);
          let module_names =
            tcrs
            |> List.map (fun tcr ->
               Universal.module_or_interface_name tcr.checked_module)
          in
          report_errors module_names;
          finished_message module_names 0
        end //end batch mode

        else
          Errors.raise_error0 Errors.Error_MissingFileName "No file provided"
        end

(* This is pretty awful. Now that we have Lazy_embedding, we can get rid of this table. *)
let lazy_chooser (k:Syntax.Syntax.lazy_kind) (i:Syntax.Syntax.lazyinfo) : Syntax.Syntax.term
  = match k with
    (* TODO: explain *)
    | FStar.Syntax.Syntax.BadLazy               -> failwith "lazy chooser: got a BadLazy"
    | FStar.Syntax.Syntax.Lazy_bv               -> RE.unfold_lazy_bv          i
    | FStar.Syntax.Syntax.Lazy_namedv           -> RE.unfold_lazy_namedv      i
    | FStar.Syntax.Syntax.Lazy_binder           -> RE.unfold_lazy_binder      i
    | FStar.Syntax.Syntax.Lazy_letbinding       -> RE.unfold_lazy_letbinding  i
    | FStar.Syntax.Syntax.Lazy_optionstate      -> RE.unfold_lazy_optionstate i
    | FStar.Syntax.Syntax.Lazy_fvar             -> RE.unfold_lazy_fvar        i
    | FStar.Syntax.Syntax.Lazy_comp             -> RE.unfold_lazy_comp        i
    | FStar.Syntax.Syntax.Lazy_env              -> RE.unfold_lazy_env         i
    | FStar.Syntax.Syntax.Lazy_sigelt           -> RE.unfold_lazy_sigelt      i
    | FStar.Syntax.Syntax.Lazy_universe         -> RE.unfold_lazy_universe    i

    | FStar.Syntax.Syntax.Lazy_proofstate       -> Tactics.Embedding.unfold_lazy_proofstate i
    | FStar.Syntax.Syntax.Lazy_goal             -> Tactics.Embedding.unfold_lazy_goal i

    | FStar.Syntax.Syntax.Lazy_doc              -> RE.unfold_lazy_doc i

    | FStar.Syntax.Syntax.Lazy_uvar             -> FStar.Syntax.Util.exp_string "((uvar))"
    | FStar.Syntax.Syntax.Lazy_universe_uvar    -> FStar.Syntax.Util.exp_string "((universe_uvar))"
    | FStar.Syntax.Syntax.Lazy_issue            -> FStar.Syntax.Util.exp_string "((issue))"
    | FStar.Syntax.Syntax.Lazy_ident            -> FStar.Syntax.Util.exp_string "((ident))"
    | FStar.Syntax.Syntax.Lazy_tref             -> FStar.Syntax.Util.exp_string "((tref))"

    | FStar.Syntax.Syntax.Lazy_embedding (_, t) -> Thunk.force t
    | FStar.Syntax.Syntax.Lazy_extension s      -> FStar.Syntax.Util.exp_string (format1 "((extension %s))" s)
  
// This is called directly by the Javascript port (it doesn't call Main)
let setup_hooks () =
    FStar.Syntax.DsEnv.ugly_sigelt_to_string_hook := show;
    FStar.Errors.set_parse_warn_error FStar.Parser.ParseIt.parse_warn_error;
    FStar.Syntax.Syntax.lazy_chooser := Some lazy_chooser;
    FStar.Syntax.Util.tts_f := Some show;
    FStar.Syntax.Util.ttd_f := Some Class.PP.pp;
    FStar.TypeChecker.Normalize.unembed_binder_knot := Some RE.e_binder;
    List.iter Tactics.Interpreter.register_tactic_primitive_step Tactics.V1.Primops.ops;
    List.iter Tactics.Interpreter.register_tactic_primitive_step Tactics.V2.Primops.ops;
    ()

let handle_error e =
    if FStar.Errors.handleable e then
      FStar.Errors.err_exn e;
    if Options.trace_error() then
      Util.print2_error "Unexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
    else if not (FStar.Errors.handleable e) then
      Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e);
    cleanup();
    report_errors []

let main () =
  try
    setup_hooks ();
    let _, time = Util.record_time go in
    if FStar.Options.query_stats()
    then Util.print2_error "TOTAL TIME %s ms: %s\n"
              (FStar.Compiler.Util.string_of_int time)
              (String.concat " " (FStar.Getopt.cmdline()));
    cleanup ();
    exit 0
  with
  | e -> handle_error e;
        exit 1
