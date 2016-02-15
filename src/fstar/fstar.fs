(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Util
open FStar.Getopt
open FStar.Tc.Util
open FStar.Ident

let process_args () =
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

let cleanup () = Util.kill_all ()

let has_prims_cache (l: list<string>) :bool = List.mem "Prims.cache" l

open FStar.TypeChecker.Env
let u_parse env fn =
    try
        match Parser.ParseIt.parse (Inl fn) with
            | Inl (Inl ast) ->
                Parser.ToSyntax.desugar_file env ast

            | Inl (Inr _) ->
                Util.print1_error "%s expected a module\n" fn;
                exit 1

            | Inr (msg, r) ->
                Util.print_string <| Print.format_error r msg;
                exit 1
    with e when (!Options.trace_error
                    && FStar.Syntax.Util.handleable e
                    && (FStar.Syntax.Util.handle_err false () e; false)) ->
                    failwith "Impossible"

        | e when (not !Options.trace_error && FStar.Syntax.Util.handleable e) ->
        FStar.Syntax.Util.handle_err false () e;
        exit 1

let u_tc_prims () =
    let solver = if !Options.verify then SMTEncoding.Encode.solver else SMTEncoding.Encode.dummy in
    let env = FStar.TypeChecker.Env.initial_env
         FStar.TypeChecker.Tc.type_of
         solver
         Const.prims_lid in
    env.solver.init env;
    let p = Options.prims () in
    let dsenv, prims_mod = u_parse (Parser.Env.empty_env()) p in
    let prims_mod, env = FStar.TypeChecker.Tc.check_module env (List.hd prims_mod) in
    prims_mod, dsenv, env


let test_universes filenames =
    try
        let prims_mod, dsenv, env = u_tc_prims() in
        let dsenv, mods, env = List.fold_left (fun (dsenv, fmods, env) fn ->
           Util.print1 "Parsing file %s\n" fn;
           let dsenv, mods = u_parse dsenv fn in
           let _, env = TypeChecker.Tc.check_module env (List.hd mods) in
           dsenv, mods@fmods, env) (dsenv, [], env) filenames in
        env.solver.finish();
        dsenv, mods, env
    with
        | Syntax.Syntax.Error(msg, r) when not (!Options.trace_error) ->
          Util.print_error (Util.format2 "%s\n%s\n" (Range.string_of_range r) msg);
          exit 1

open FStar.Tc.Env
let tc_prims () =
    let solver = if !Options.verify then ToSMT.Encode.solver else ToSMT.Encode.dummy in
    let env = Tc.Env.initial_env solver Const.prims_lid in
    env.solver.init env;

    let p = Options.prims () in
    let dsenv, prims_mod = Parser.Driver.parse_file (Parser.DesugarEnv.empty_env()) p in
    let prims_mod, env = Tc.Tc.check_module env (List.hd prims_mod) in
    prims_mod, dsenv, env

let report_errors nopt =
    let errs = match nopt with
        | None -> Tc.Errors.get_err_count ()
        | Some n -> n in
    if errs>0
    then begin
        Util.print1_error "%s errors were reported (see above)\n" (string_of_int errs);
        exit 1
    end

let report_universes_errors nopt =
    let errs = match nopt with
        | None -> TypeChecker.Errors.get_err_count ()
        | Some n -> n in
    if errs>0
    then begin
        Util.print1_error "%s errors were reported (see above)\n" (string_of_int errs);
        exit 1
    end

let tc_one_file dsenv env fn =
    let dsenv, fmods = Parser.Driver.parse_file dsenv fn in
    let env, all_mods = fmods |> List.fold_left (fun (env, all_mods) m ->
        let ms, env = Tc.Tc.check_module env m in
        env, ms@all_mods) (env, []) in
    dsenv, env, List.rev all_mods

let tc_one_fragment curmod dsenv env frag =
    try
        match Parser.Driver.parse_fragment curmod dsenv frag with
            | Parser.Driver.Empty ->
              Some (curmod, dsenv, env)

            | Parser.Driver.Modul (dsenv, modul) ->
              let env = match curmod with
                | None -> env
                | Some _ ->
                  raise (Absyn.Syntax.Err("Interactive mode only supports a single module at the top-level")) in
              let modul, env = Tc.Tc.tc_partial_modul env modul in
              Some (Some modul, dsenv, env)

            | Parser.Driver.Decls (dsenv, decls) ->
              begin match curmod with
                | None -> Util.print_error "fragment without an enclosing module"; exit 1
                | Some modul ->
                  let modul, env  = Tc.Tc.tc_more_partial_modul env modul decls in
                  Some (Some modul, dsenv, env)
              end
    with
        | Absyn.Syntax.Error(msg, r) ->
          Tc.Errors.add_errors env [(msg,r)];
          None

        | Absyn.Syntax.Err msg ->
          Tc.Errors.add_errors env [(msg,Absyn.Syntax.dummyRange)];
          None

        | e -> raise e

type input_chunks =
    | Push of string
    | Pop  of string
    | Code of string * (string * string)

type stack_elt =
    (option<modul>
     * Parser.DesugarEnv.env
     * Tc.Env.env)
type stack = list<stack_elt>


let batch_mode_tc_no_prims dsenv env filenames admit_fsi =
    let all_mods, dsenv, env = filenames |> List.fold_left (fun (all_mods, dsenv, env) f ->
        Util.reset_gensym();
        let dsenv, env, ms = tc_one_file dsenv env f in
        all_mods@ms, dsenv, env)
        ([], dsenv, env) in

    if !Options.interactive && Tc.Errors.get_err_count () = 0
    then env.solver.refresh()
    else env.solver.finish();
    all_mods, dsenv, env

let find_deps_if_needed files =
    if !Options.explicit_deps then
      files, []
    else
      let _, deps = Parser.Dep.collect files in
      let deps = List.rev deps in
      let deps =
        if basename (List.hd deps) = "prims.fst" then
          List.tl deps
        else begin
          Util.print_error "dependency analysis did not find prims.fst?!";
          exit 1
        end
      in
      let admit_fsi = ref [] in
      List.iter (fun d ->
        let d = basename d in
        if get_file_extension d = "fsti" then
          admit_fsi := substring d 0 (String.length d - 5) :: !admit_fsi
        else if get_file_extension d = "fsi" then begin
          admit_fsi := substring d 0 (String.length d - 4) :: !admit_fsi
        end
      ) deps;
      deps, !admit_fsi

let batch_mode_tc filenames =
    let prims_mod, dsenv, env = tc_prims () in

    let filenames, admit_fsi = find_deps_if_needed filenames in
    let all_mods, dsenv, env = batch_mode_tc_no_prims dsenv env filenames admit_fsi in
    prims_mod @ all_mods, dsenv, env

let finished_message fmods =
    if not !Options.silent
    then begin
        let msg =
            if !Options.verify then "Verifying"
            else if !Options.pretype then "Lax type-checked"
            else "Parsed and desugared" in
         fmods |> List.iter (fun m ->
            let tag = if m.is_interface then "i'face" else "module" in
            if Options.should_print_message m.name.str
            then Util.print_string (Util.format3 "%s %s: %s\n" msg tag (Syntax.text_of_lid m.name)));
         print_string (Util.format1 "%s\n" (Util.colorize_bold "All verification conditions discharged successfully"))
    end

type interactive_state = {
  chunk: string_builder;
  stdin: ref<option<stream_reader>>; // Initialized once.
  buffer: ref<list<input_chunks>>;
  log: ref<option<file_handle>>;
}

let the_interactive_state = {
  chunk = Util.new_string_builder ();
  stdin = ref None;
  buffer = ref [];
  log = ref None
}

let rec read_chunk () =
    let s = the_interactive_state in
    let log =
      if !Options.debug <> [] then
        let transcript = match !s.log with
          | Some transcript ->
              transcript
          | None ->
              let transcript = Util.open_file_for_writing "transcript" in
              s.log := Some transcript;
              transcript
        in
        fun line ->
          Util.append_to_file transcript line;
          Util.flush_file transcript
      else
        fun _ ->
          ()
    in

    let stdin =
      match !s.stdin with
      | Some i ->
          i
      | None ->
          let i = Util.open_stdin () in
          s.stdin := Some i;
          i
    in
    let line = match Util.read_line stdin with
        | None -> exit 0
        | Some l -> l in
    log line;

    let l = Util.trim_string line in
    if Util.starts_with l "#end"
    then begin
        let responses = match Util.split l " " with
            | [_; ok; fail] -> (ok, fail)
            | _ -> ("ok", "fail") in
        let str = Util.string_of_string_builder s.chunk in
        Util.clear_string_builder s.chunk; Code (str, responses)
    end
    else if Util.starts_with l "#pop"
    then (Util.clear_string_builder s.chunk; Pop l)
    else if Util.starts_with l "#push"
    then (Util.clear_string_builder s.chunk; Push l)
    else if l = "#finish"
    then exit 0
    else (Util.string_builder_append s.chunk line;
          Util.string_builder_append s.chunk "\n";
          read_chunk())

let shift_chunk () =
  let s = the_interactive_state in
  match !s.buffer with
  | [] ->
      read_chunk ()
  | chunk :: chunks ->
      s.buffer := chunks;
      chunk

let fill_buffer () =
  let s = the_interactive_state in
  s.buffer := !s.buffer @ [ read_chunk () ]

let interactive_mode dsenv env =
    if Option.isSome !Options.codegen
    then (Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag");

    let rec go (stack:stack) (curmod:option<modul>) dsenv env =
        begin match shift_chunk () with
            | Pop msg ->
              Parser.DesugarEnv.pop dsenv |> ignore;
              Tc.Env.pop env msg |> ignore;
              env.solver.refresh();
              Options.reset_options() |> ignore;
              let (curmod, dsenv, env), stack = match stack with
                | [] -> Util.print_error "too many pops"; exit 1
                | hd::tl -> hd, tl in
              go stack curmod dsenv env

            | Push msg ->
              let stack = (curmod, dsenv, env)::stack in
              let dsenv = Parser.DesugarEnv.push dsenv in
              let env = Tc.Env.push env msg in
              go stack curmod dsenv env

            | Code (text, (ok, fail)) ->
                let mark dsenv env =
                    let dsenv = Parser.DesugarEnv.mark dsenv in
                    let env = Tc.Env.mark env in
                    dsenv, env in

                let reset_mark dsenv env =
                    let dsenv = Parser.DesugarEnv.reset_mark dsenv in
                    let env = Tc.Env.reset_mark env in
                    dsenv, env in

                let commit_mark dsenv env =
                    let dsenv = Parser.DesugarEnv.commit_mark dsenv in
                    let env = Tc.Env.commit_mark env in
                    dsenv, env in

                let fail curmod dsenv_mark env_mark =
                    Tc.Errors.report_all() |> ignore;
                    Tc.Errors.num_errs := 0;
                    Util.print1_error "%s\n" fail;
                    let dsenv, env = reset_mark dsenv_mark env_mark in
                    go stack curmod dsenv env in

              let dsenv_mark, env_mark = mark dsenv env in
              let res = tc_one_fragment curmod dsenv_mark env_mark text in

              begin match res with
                | Some (curmod, dsenv, env) ->
                  if !Tc.Errors.num_errs=0
                  then begin
                     Util.print1 "\n%s\n" ok;
                     let dsenv, env = commit_mark dsenv env in
                     go stack curmod dsenv env
                  end
                  else fail curmod dsenv_mark env_mark

                | _ ->
                  fail curmod dsenv_mark env_mark
              end
        end in

    go [] None dsenv env


let codegen fmods env=
    if !Options.codegen = Some "OCaml"
    || !Options.codegen = Some "FSharp"
    then begin
        let c, mllibs = Util.fold_map Extraction.ML.ExtractMod.extract (Extraction.ML.Env.mkContext env) fmods in
        let mllibs = List.flatten mllibs in
        let ext = if !Options.codegen = Some "FSharp" then ".fs" else ".ml" in
        let newDocs = List.collect Extraction.ML.Code.doc_of_mllib mllibs in
//                           else List.collect Extraction.OCaml.Code.doc_of_mllib mllibs, ".ml" in
        List.iter (fun (n,d) -> Util.write_file (Options.prependOutputDir (n^ext)) (FStar.Format.pretty 120 d)) newDocs
    end

exception Found of string

let find_initial_module_name () =
  fill_buffer (); fill_buffer ();
  try begin match !the_interactive_state.buffer with
    | [Push _; Code (code, _)] ->
        let lines = Util.split code "\n" in
        List.iter (fun line ->
          let line = trim_string line in
          if String.length line > 7 && substring line 0 6 = "module" then
            let module_name = substring line 7 (String.length line - 7) in
            raise (Found module_name)
        ) lines
    | _ ->
        ()
    end;
    None
  with Found n ->
    Some n

let detect_dependencies_with_first_interactive_chunk () =
  match find_initial_module_name () with
  | None ->
      raise (Err "No initial module directive found\n")
  | Some module_name ->
      let file_of_module_name = Parser.Dep.build_map [] in
      let filename = smap_try_find file_of_module_name (String.lowercase module_name) in
      match filename with
      | None ->
          raise (Err (Util.format2 "I found a \"module %s\" directive, but there \
            is no %s.fst\n" module_name module_name))
      | Some filename ->
          let _, all_filenames = Parser.Dep.collect [ filename ] in
          List.rev (List.tl all_filenames)


(* Main function *)
let go _ =
  let res, filenames = process_args () in
  match res with
    | Help ->
      Options.display_usage (Options.specs())
    | Die msg ->
      Util.print_string msg
    | GoOn ->
      if !Options.dep <> None then
        Parser.Dep.print (Parser.Dep.collect filenames)
      else if !Options.universes
      then (test_universes filenames |> ignore;
            report_universes_errors None)
        (* Normal mode of operations *)
      else if !Options.interactive then
        let filenames =
          if !Options.explicit_deps then begin
            if List.length filenames = 0 then
              Util.print_error "--explicit_deps was provided without a file list!\n";
            filenames
          end else begin
            if List.length filenames > 0 then
              Util.print_warning "ignoring the file list (no --explicit_deps)\n";
            detect_dependencies_with_first_interactive_chunk ()
          end
        in
        let fmods, dsenv, env = batch_mode_tc filenames in
        interactive_mode dsenv env
      else if List.length filenames >= 1 then
        (let fmods, dsenv, env = batch_mode_tc filenames in
        report_errors None;
        codegen fmods env;
        finished_message fmods)
      else
        Util.print_error "no file provided\n"

let main () =
    try
      go ();
      cleanup ();
      exit 0
    with
    | e ->
        if Util.handleable e then Util.handle_err false () e;
        if !Options.trace_error
        then Util.print2_error "Unexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
        else if not (Util.handleable e)
        then Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e);
        cleanup ();
        exit 1
