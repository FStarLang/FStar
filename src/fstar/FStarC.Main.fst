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
module FStarC.Main
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Getopt
open FStarC.Ident
open FStarC.CheckedFiles
open FStarC.Universal
open FStarC

open FStarC.Class.Show

module E = FStarC.Errors
module UF = FStarC.Syntax.Unionfind

(* These modules only mentioned to put them in the dep graph
and hence compile and link them in. They do not export anything,
instead they register primitive steps in the normalizer during
initialization. *)
open FStarC.Reflection.V1.Interpreter {}
open FStarC.Reflection.V2.Interpreter {}
(* Same, except that it only defines some types for userspace to refer to. *)
open FStarC.Tactics.Types.Reflection {}
open FStarC.NormSteps {}

(* process_args:  parses command line arguments, setting FStarC.Options *)
(*                returns an error status and list of filenames        *)
let process_args () : parse_cmdline_res & list string =
  Options.parse_cmd_line ()

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
  FStarC.Errors.report_all () |> ignore;
  let nerrs = FStarC.Errors.get_err_count() in
  if nerrs > 0 then begin
    finished_message fmods nerrs;
    exit 1
  end

let load_native_tactics () =
    let open FStarC.Errors.Msg in
    let modules_to_load = Options.load() |> List.map Ident.lid_of_str in
    let cmxs_to_load = Options.load_cmxs () |> List.map Ident.lid_of_str in
    let ml_module_name m = FStarC.Extraction.ML.Util.ml_module_name_of_lid m in
    let ml_file m = ml_module_name m ^ ".ml" in
    let cmxs_file m =
        let cmxs = ml_module_name m ^ ".cmxs" in
        match Find.find_file_odir cmxs with
        | Some f -> f
        | None ->
          if List.contains m cmxs_to_load  //if this module comes from the cmxs list, fail hard
          then E.raise_error0 E.Fatal_FailToCompileNativeTactic (Util.format1 "Could not find %s to load" cmxs)
          else  //else try to find and compile the ml file
            match Find.find_file_odir (ml_file m) with
            | None ->
              E.raise_error0 E.Fatal_FailToCompileNativeTactic [
                text "Failed to compile native tactic.";
                text (format1 "Extracted module %s not found." (ml_file m))
              ]
            | Some ml ->
              let dir = Filepath.dirname ml in
              Plugins.compile_modules dir [ml_module_name m];
              begin match Find.find_file_odir cmxs with
                | None ->
                  E.raise_error0 E.Fatal_FailToCompileNativeTactic [
                    text "Failed to compile native tactic.";
                    text (format1 "Compilation seemingly succeeded, but compiled object %s not found." cmxs);
                  ]
                | Some f -> f
              end
    in

    let cmxs_files = (modules_to_load@cmxs_to_load) |> List.map cmxs_file in
    Plugins.load_plugins cmxs_files;
    iter_opt (Options.use_native_tactics ())
      Plugins.load_plugins_dir;
    ()


(* Need to keep names of input files for a second pass when prettyprinting *)
(* This reference is set once in `go` and read in `main` if the print or *)
(* print_in_place options are passed *)
let fstar_files: ref (option (list string)) = mk_ref None

(* This is used to print a backtrace when F* is interrupted by SIGINT *)
let set_error_trap () =
  let h = get_sigint_handler () in
  let h' s =
    let open FStarC.Pprint in
    let open FStarC.Errors.Msg in
    Debug.enable (); (* make sure diag is printed *)
    Options.set_option "error_contexts" (Options.Bool true);
    (* ^ Print context. Stack trace will be added since we have trace_error. *)
    Errors.diag Range.dummyRange [
      text "GOT SIGINT! Exiting";
    ];
    exit 1
  in
  set_sigint_handler (sigint_handler_f h')

let print_help_for (o : string) : unit =
  match Options.help_for_option o with
  | None -> ()
  | Some doc -> Util.print_error (Errors.Msg.renderdoc doc)

(* Normal mode with some flags, files, etc *)
let go_normal () =
  let res, filenames0 = process_args () in

  if Some? (Options.output_to()) &&
     not (Some? (Options.dep ())) &&
     List.length filenames0 > 1
  then
    Errors.raise_error0 Errors.Fatal_OptionsNotCompatible [
      Errors.Msg.text "When using -o, you can only provide a single file in the
        command line (except for dependency analysis).";
    ];

  let chopsuf (suf s : string) : option string =
    if ends_with s suf
    then Some (String.substring s 0 (String.length s - String.length suf))
    else None
  in
  let ( ||| ) x y =
    match x with
    | None -> y
    | _ -> x
  in
  let checked_of (f:string) =
    chopsuf ".checked" f ||| chopsuf ".checked.lax" f
  in

  let filenames =
    filenames0 |>
    List.map (fun f ->
      if not (Filepath.file_exists f) then f else
      (* ^ only rewrite if file exists *)
      match checked_of f with
      | Some f' ->
        if Debug.any () then
          print1 "Rewriting argument file %s to its source file\n" f;
        (match Find.find_file (Filepath.basename f') with
         | Some r -> r
         | None -> failwith "Couldn't find source for file" ^ f' ^ "!\n")
      | None -> f
    )
  in
  if Debug.any () then
    print2 "Rewrote\n%s\ninto\n%s\n\n" (show filenames0) (show filenames);

  (* Compat: create the --odir and --cache_dir if they don't exist.
  F* has done this for a long time, only sinc it simplified
  the handling of options. I think this should probably be removed,
  but a few makefiles here and there rely on it. *)
  iter_opt (Find.get_odir ()) (mkdir false true);
  iter_opt (Find.get_cache_dir ()) (mkdir false true);

  let check_no_filenames opt =
    if Cons? filenames then (
      Util.print1_error "error: No filenames should be passed with option %s\n" opt;
      exit 1
    )
  in
  if Options.trace_error () then set_error_trap ();
  match res with
    | Empty     -> Options.display_usage(); exit 1
    | Help      -> Options.display_usage(); exit 0
    | Error (msg, opt) ->
      Util.print_error ("error: " ^ msg);
      print_help_for opt;
      exit 1

    | Success when Options.print_cache_version () ->
      Util.print1 "F* cache version number: %s\n"
                   (string_of_int FStarC.CheckedFiles.cache_version_number);
      exit 0

    (* --dep: Just compute and print the transitive dependency graph;
              don't verify anything *)
    | Success when Options.dep () <> None ->
      let _, deps = Parser.Dep.collect filenames FStarC.CheckedFiles.load_parsing_data_from_cache in
      Parser.Dep.print deps;
      report_errors []

    (* --print: Emit files in canonical source syntax *)
    | Success when Options.print () || Options.print_in_place () ->
      let printing_mode =
        if Options.print ()
        then Prettyprint.FromTempToStdout
        else Prettyprint.FromTempToFile
      in
      Prettyprint.generate printing_mode filenames

    (* --read_checked: read and print a checked file *)
    | Success when Some? (Options.read_checked_file ()) -> (
      let path = Some?.v <| Options.read_checked_file () in
      let env = Universal.init_env Parser.Dep.empty_deps in
      let res = CheckedFiles.load_tc_result path in
      match res with
      | None ->
        let open FStarC.Pprint in
        Errors.raise_error0 Errors.Fatal_ModuleOrFileNotFound [
          Errors.Msg.text "Could not read checked file:" ^/^ doc_of_string path
        ]

      | Some (deps, tcr) ->
        print1 "Deps: %s\n" (show deps);
        print1 "%s\n" (show tcr.checked_module)
    )

    (* --read_krml_file: read and print a krml file *)
    | Success when Some? (Options.read_krml_file ()) -> (
      let path = Some?.v <| Options.read_krml_file () in
      match load_value_from_file path <: option Extraction.Krml.binary_format with
      | None ->
        let open FStarC.Pprint in
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
    )

    (* --list_plugins: emit a list of plugins and exit *)
    | Success when Options.list_plugins () ->
      let ps = TypeChecker.Cfg.list_plugins () in
      let ts = Tactics.Interpreter.native_tactics_steps () in
      Util.print1 "Registered plugins:\n%s\n" (String.concat "\n" (List.map (fun p -> "  " ^ show p.TypeChecker.Primops.Base.name) ps));
      Util.print1 "Registered tactic plugins:\n%s\n" (String.concat "\n" (List.map (fun p -> "  " ^ show p.TypeChecker.Primops.Base.name) ts));
      ()

    (* --locate, --locate_lib, --locate_ocaml, --locate_file *)
    | Success when Options.locate () ->
      check_no_filenames "--locate";
      Util.print1 "%s\n" (Find.locate ());
      exit 0

    | Success when Options.locate_lib () -> (
      check_no_filenames "--locate_lib";
      match Find.locate_lib () with
      | None ->
        Util.print_error "No library found (is --no_default_includes set?)\n";
        exit 1
      | Some s ->
        Util.print1 "%s\n" s;
        exit 0
    )

    | Success when Options.locate_ocaml () ->
      check_no_filenames "--locate_ocaml";
      Util.print1 "%s\n" (Find.locate_ocaml ());
      exit 0

    | Success when Some? (Options.locate_file ()) -> (
      check_no_filenames "--locate_file";
      let f = Some?.v (Options.locate_file ()) in
      match Find.find_file f with
      | None ->
        Util.print1_error "File %s was not found in include path.\n" f;
        exit 1
      | Some fn ->
        Util.print1 "%s\n" (Filepath.normalize_file_path fn);
        exit 0
    )

    | Success when Some? (Options.locate_z3 ()) -> (
      check_no_filenames "--locate_z3";
      let v = Some?.v (Options.locate_z3 ()) in
      match Find.Z3.locate_z3 v with
      | None ->
        // Use an actual error to reuse the pretty printing.
        Errors.log_issue0 Errors.Error_Z3InvocationError ([
          Errors.Msg.text <| Util.format1 "Z3 version '%s' was not found." v;
          ] @ Find.Z3.z3_install_suggestion v);
        report_errors []; // but make sure to report.
        exit 1
      | Some fn ->
        Util.print1 "%s\n" fn;
        exit 0
    )

    (* either batch or interactive mode *)
    | Success ->
      fstar_files := Some filenames;

      if Debug.any () then (
        Util.print3 "- F* version %s -- %s (on %s)\n"  !Options._version !Options._commit (Platform.kernel ());
        Util.print1 "- Executable: %s\n" (Util.exec_name);
        Util.print1 "- Library root: %s\n" (Util.dflt "<none>" (Find.lib_root ()));
        Util.print1 "- Full include path: %s\n" (show (Find.full_include_path ()));
        Util.print_string "\n";
        ()
      );

      (* Set the unionfind graph to read-only mode.
       * This will be unset by the typechecker and other pieces
       * of code that intend to use it. It helps us catch errors. *)
      UF.set_ro ();

      (* Try to load the plugins that are specified in the command line *)
      load_native_tactics ();

      (* --lsp: interactive mode for Language Server Protocol *)
      if Options.lsp_server () then
        Interactive.Lsp.start_server ()
      (* --ide, --in: Interactive mode *)
      else if Options.interactive () then begin
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
            Interactive.Legacy.interactive_mode filename
          else
            Interactive.Ide.interactive_mode filename
        end

      (* Normal, batch mode compiler *)
      else begin
        if Nil? filenames then
          Errors.raise_error0 Errors.Error_MissingFileName "No file provided";

        let filenames, dep_graph = Dependencies.find_deps_if_needed filenames CheckedFiles.load_parsing_data_from_cache in
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

(****************************************************************************)
(* Main function                                                            *)
(****************************************************************************)

(* choose a main driver function and go *)
let go () =
  let args = Util.get_cmd_args () in
  match args with
  | _ :: "--ocamlenv" :: [] ->
    let new_ocamlpath = OCaml.new_ocamlpath () in
    Util.print1 "OCAMLPATH='%s'; export OCAMLPATH;\n" (OCaml.shellescape new_ocamlpath);
    exit 0

  | _ :: "--ocamlenv" :: cmd :: args ->
    OCaml.exec_in_ocamlenv cmd args

  | _ :: "--ocamlc" :: rest ->
    OCaml.exec_ocamlc rest

  | _ :: "--ocamlopt" :: rest ->
    OCaml.exec_ocamlopt rest

  | _ :: "--ocamlopt_plugin" :: rest ->
    OCaml.exec_ocamlopt_plugin rest

  | _ -> go_normal ()

let handle_error e =
    if FStarC.Errors.handleable e then
      FStarC.Errors.err_exn e
    else begin
      Util.print1_error "Unexpected error: %s\n" (Util.message_of_exn e);
      if Options.trace_error() then
        Util.print1_error "Trace:\n%s\n" (Util.trace_of_exn e)
      else
        Util.print_error "Please file a bug report, ideally with a minimized version of the source program that triggered the error.\n"
    end;
    report_errors []

let main () =
  try
    Hooks.setup_hooks ();
    let _, time = Timing.record_ms go in
    if FStarC.Options.query_stats()
    then Util.print2_error "TOTAL TIME %s ms: %s\n"
              (FStarC.Util.string_of_int time)
              (String.concat " " (FStarC.Getopt.cmdline()));
    exit 0
  with
  | e ->
    handle_error e;
    exit 1
