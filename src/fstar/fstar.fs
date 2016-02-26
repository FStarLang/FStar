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

(* Module abbreviations for the stratified type-checker *)
module F_DsEnv   = FStar.Parser.DesugarEnv 
module F_TcEnv   = FStar.Tc.Env
module F_Syntax  = FStar.Absyn.Syntax
module F_Util    = FStar.Absyn.Util
module F_Desugar = FStar.Parser.Desugar
module F_SMT     = FStar.ToSMT.Encode
module F_Const   = FStar.Absyn.Const
module F_Tc      = FStar.Tc.Tc

(* Module abbreviations for the universal type-checker  *)
module U_DsEnv   = FStar.Parser.Env 
module U_TcEnv   = FStar.TypeChecker.Env
module U_Syntax  = FStar.Syntax.Syntax
module U_Util    = FStar.Syntax.Util
module U_Desugar = FStar.Parser.ToSyntax
module U_SMT     = FStar.SMTEncoding.Encode
module U_Const   = FStar.Syntax.Const
module U_Tc      = FStar.TypeChecker.Tc

(***********************************************************************)
(* process_args:  parses command line arguments, setting FStar.Options *)
(*                returns an error status and list of filenames        *)
(***********************************************************************)
let process_args () : parse_cmdline_res * list<string> =
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

(***********************************************************************)
(* finishing up *)
(***********************************************************************)

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

(***********************************************************************)
(* Finding the transitive dependences of a list of files               *)
(***********************************************************************)
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
                admit_fsi := substring d 0 (String.length d - 4) :: !admit_fsi end
    ) deps;
    deps, !admit_fsi

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)

(* stratified *)
let parse (env:F_DsEnv.env) (fn:string) : F_DsEnv.env  
                                        * list<F_Syntax.modul> =
  let ast = Parser.Driver.parse_file fn in
  F_Desugar.desugar_file env ast

(* universes *)
let u_parse (env:U_DsEnv.env) (fn:string) : U_DsEnv.env  
                                          * list<U_Syntax.modul> =
  let ast = Parser.Driver.parse_file fn in
  U_Desugar.desugar_file env ast


(***********************************************************************)
(* Checking Prims.fst                                                  *)
(***********************************************************************)

(* stratified *)
let tc_prims () =
  let solver = if !Options.verify then F_SMT.solver else F_SMT.dummy in
  let env = F_TcEnv.initial_env solver F_Const.prims_lid in
  env.solver.init env;
  let p = Options.prims () in
  let dsenv, prims_mod = parse (F_DsEnv.empty_env()) p in
  let prims_mod, env = F_Tc.check_module env (List.hd prims_mod) in
  prims_mod, dsenv, env

(* universes *)
let u_tc_prims () =
  let solver = if !Options.verify then U_SMT.solver else U_SMT.dummy in
  let env = U_TcEnv.initial_env U_Tc.type_of solver U_Const.prims_lid in
  env.solver.init env;
  let p = Options.prims () in
  let dsenv, prims_mod = u_parse (U_DsEnv.empty_env()) p in
  let prims_mod, env = U_Tc.check_module env (List.hd prims_mod) in
  prims_mod, dsenv, env

(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)

(* stratified *)
let tc_one_file dsenv env fn =
  let dsenv, fmods = parse dsenv fn in
  let env, all_mods =
    fmods |> List.fold_left (fun (env, all_mods) m ->
                            let ms, env = F_Tc.check_module env m in
                            env, ms@all_mods) (env, []) in
  dsenv, env, List.rev all_mods

(* universes *)
let u_tc_one_file dsenv env fn =
  let dsenv, fmods = u_parse dsenv fn in
  let env, all_mods =
    fmods |> List.fold_left (fun (env, all_mods) m ->
                            let m, env = U_Tc.check_module env m in
                            env, m::all_mods) (env, []) in
  dsenv, env, List.rev all_mods

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)

(* stratified *)
let batch_mode_tc_no_prims dsenv env filenames =
  let all_mods, dsenv, env =
    filenames |> List.fold_left (fun (all_mods, dsenv, env) f ->
                                F_Util.reset_gensym();
                                let dsenv, env, ms = tc_one_file dsenv env f in
                                all_mods@ms, dsenv, env)
                                ([], dsenv, env) in
  if !Options.interactive && FStar.Tc.Errors.get_err_count () = 0
  then env.solver.refresh()
  else env.solver.finish();
  all_mods, dsenv, env

let batch_mode_tc filenames =
  let prims_mod, dsenv, env = tc_prims () in
  let filenames, admit_fsi = find_deps_if_needed filenames in
  let all_mods, dsenv, env = batch_mode_tc_no_prims dsenv env filenames in
  prims_mod @ all_mods, dsenv, env

(* universes *)
let u_batch_mode_tc_no_prims dsenv env filenames =
  let all_mods, dsenv, env =
    filenames |> List.fold_left (fun (all_mods, dsenv, env) f ->
                                U_Syntax.reset_gensym();
                                let dsenv, env, ms = u_tc_one_file dsenv env f in
                                all_mods@ms, dsenv, env)
                                ([], dsenv, env) in
  if !Options.interactive && FStar.TypeChecker.Errors.get_err_count () = 0
  then env.solver.refresh()
  else env.solver.finish();
  all_mods, dsenv, env

let u_batch_mode_tc filenames =
  let prims_mod, dsenv, env = u_tc_prims () in
  let filenames, admit_fsi = find_deps_if_needed filenames in
  let all_mods, dsenv, env = u_batch_mode_tc_no_prims dsenv env filenames in
  prims_mod :: all_mods, dsenv, env

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)

(* stratified *)
let tc_one_fragment curmod dsenv env frag =
  try
    match Parser.Driver.parse_fragment frag with
    | Parser.Driver.Empty ->
      Some (curmod, dsenv, env)

    | Parser.Driver.Modul ast_modul -> 
      let dsenv, modul = F_Desugar.desugar_partial_modul curmod dsenv ast_modul in
      let env = match curmod with
          | None -> env
          | Some _ -> raise (Absyn.Syntax.Err("Interactive mode only supports a single module at the top-level")) in
      let modul, env = F_Tc.tc_partial_modul env modul in
      Some (Some modul, dsenv, env)

    | Parser.Driver.Decls ast_decls -> 
      let dsenv, decls = F_Desugar.desugar_decls dsenv ast_decls in
      match curmod with
        | None -> Util.print_error "fragment without an enclosing module"; exit 1
        | Some modul ->
            let modul, env  = F_Tc.tc_more_partial_modul env modul decls in
            Some (Some modul, dsenv, env) 

    with
      | F_Syntax.Error(msg, r) ->
          Tc.Errors.add_errors env [(msg,r)];
          None
      | F_Syntax.Err msg ->
          Tc.Errors.add_errors env [(msg,Range.dummyRange)];
          None
      | e -> raise e

(* universes *)
let u_tc_one_fragment curmod dsenv (env:U_TcEnv.env) frag =
  try
    match Parser.Driver.parse_fragment frag with
    | Parser.Driver.Empty ->
      Some (curmod, dsenv, env)

    | Parser.Driver.Modul ast_modul -> 
      let dsenv, modul = U_Desugar.desugar_partial_modul curmod dsenv ast_modul in
      let env = match curmod with
          | None -> env
          | Some _ -> raise (Absyn.Syntax.Err("Interactive mode only supports a single module at the top-level")) in
      let modul, _, env = U_Tc.tc_partial_modul env modul in
      Some (Some modul, dsenv, env)

    | Parser.Driver.Decls ast_decls -> 
      let dsenv, decls = U_Desugar.desugar_decls dsenv ast_decls in
      match curmod with
        | None -> Util.print_error "fragment without an enclosing module"; exit 1
        | Some modul ->
            let modul, _, env  = U_Tc.tc_more_partial_modul env modul decls in
            Some (Some modul, dsenv, env) 

    with
      | U_Syntax.Error(msg, r) ->
          TypeChecker.Errors.add_errors env [(msg,r)];
          None
      | U_Syntax.Err msg ->
          TypeChecker.Errors.add_errors env [(msg,Range.dummyRange)];
          None
      | e -> raise e

(***********************************************************************)
(* Interactive mode: the user interface                                *)
(***********************************************************************)
type input_chunks =
  | Push of string
  | Pop  of string
  | Code of string * (string * string)

type stack<'env,'modul> = list<('env * 'modul)>

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

(***********************************************************************)
(* Reading some input *)
(***********************************************************************)
let rec read_chunk () =
  let s = the_interactive_state in
  let log =
    if !Options.debug <> [] then
      let transcript =
        match !s.log with
        | Some transcript -> transcript
        | None ->
            let transcript = Util.open_file_for_writing "transcript" in
            s.log := Some transcript;
            transcript
      in
      fun line ->
        Util.append_to_file transcript line;
        Util.flush_file transcript
    else
      fun _ -> ()
  in
  let stdin =
    match !s.stdin with
    | Some i -> i
    | None ->
        let i = Util.open_stdin () in
        s.stdin := Some i;
        i
  in
  let line =
    match Util.read_line stdin with
    | None -> exit 0
    | Some l -> l
  in
  log line;

  let l = Util.trim_string line in
  if Util.starts_with l "#end" then begin
    let responses =
      match Util.split l " " with
      | [_; ok; fail] -> (ok, fail)
      | _ -> ("ok", "fail") in
    let str = Util.string_of_string_builder s.chunk in
    Util.clear_string_builder s.chunk; Code (str, responses)
    end
  else if Util.starts_with l "#pop" then (Util.clear_string_builder s.chunk; Pop l)
  else if Util.starts_with l "#push" then (Util.clear_string_builder s.chunk; Push l)
  else if l = "#finish" then exit 0
  else
    (Util.string_builder_append s.chunk line;
    Util.string_builder_append s.chunk "\n";
    read_chunk())

let shift_chunk () =
  let s = the_interactive_state in
  match !s.buffer with
  | [] -> read_chunk ()
  | chunk :: chunks ->
      s.buffer := chunks;
      chunk

let fill_buffer () =
  let s = the_interactive_state in
  s.buffer := !s.buffer @ [ read_chunk () ]

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
    | _ -> ()
    end;
    None
  with Found n -> Some n

let detect_dependencies_with_first_interactive_chunk () =
 let fail msg = 
    if !Options.universes
    then raise (U_Syntax.Err msg)
    else raise (F_Syntax.Err msg) in
  match find_initial_module_name () with
  | None ->
    fail "No initial module directive found\n"
  | Some module_name ->
      let file_of_module_name = Parser.Dep.build_map [] in
      let filename = smap_try_find file_of_module_name (String.lowercase module_name) in
      match filename with
      | None ->
         fail (Util.format2 "I found a \"module %s\" directive, but there \
            is no %s.fst\n" module_name module_name)
      | Some filename ->
          let _, all_filenames = Parser.Dep.collect [ filename ] in
          List.rev (List.tl all_filenames)

(******************************************************************************************)
(* The interface expected to be provided by a type-checker to run in the interactive loop *)
(******************************************************************************************)
type interactive_tc<'env,'modul> = {
    pop:         'env -> string -> unit;
    push:        'env -> string -> 'env;
    mark:        'env -> 'env;
    reset_mark:  'env -> 'env;
    commit_mark: 'env -> 'env;
    check_frag:  'env -> 'modul -> string -> option<('modul * 'env * int)>;
    report_fail:  unit -> unit
}

(******************************************************************************************)
(* The main interactive loop *)
(******************************************************************************************)
let interactive_mode (env:'env) (initial_mod:'modul) (tc:interactive_tc<'env,'modul>) = 
  if Option.isSome !Options.codegen then
    (Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag");
    let rec go (stack:stack<'env,'modul>) (curmod:'modul) (env:'env) = begin
      match shift_chunk () with
      | Pop msg ->
          tc.pop env msg;
          let (env, curmod), stack =
            match stack with
            | [] -> Util.print_error "too many pops"; exit 1
            | hd::tl -> hd, tl
          in
          go stack curmod env
      | Push msg ->
          let stack = (env, curmod)::stack in
          let env = tc.push env msg in
          go stack curmod env

      | Code (text, (ok, fail)) ->
          let fail curmod env_mark =
            tc.report_fail();
            Util.print1 "%s\n" fail;
            let env = tc.reset_mark env_mark in
            go stack curmod env in
          
          let env_mark = tc.mark env in
          let res = tc.check_frag env_mark curmod text in begin
            match res with
            | Some (curmod, env, n_errs) ->
                if n_errs=0 then begin
                  Util.print1 "\n%s\n" ok;
                  let env = tc.commit_mark env in
                  go stack curmod env
                  end
                else fail curmod env_mark
            | _ -> fail curmod env_mark
            end
    end in
    go [] initial_mod env

(* Two instances of the interactive type-checker *)
(* stratified *)
let stratified_interactive_tc : interactive_tc<(F_DsEnv.env * F_TcEnv.env), option<F_Syntax.modul>> = 
    let pop (dsenv, env) msg = 
          F_DsEnv.pop dsenv |> ignore;
          F_TcEnv.pop env msg |> ignore;
          env.solver.refresh();
          Options.reset_options() |> ignore in

    let push (dsenv, env) msg = 
          let dsenv = F_DsEnv.push dsenv in
          let env = F_TcEnv.push env msg in
          (dsenv, env) in

    let mark (dsenv, env) =
        let dsenv = F_DsEnv.mark dsenv in
        let env = F_TcEnv.mark env in
        dsenv, env in

    let reset_mark (dsenv, env) =
        let dsenv = F_DsEnv.reset_mark dsenv in
        let env = F_TcEnv.reset_mark env in
        dsenv, env in

    let commit_mark (dsenv, env) =
        let dsenv = F_DsEnv.commit_mark dsenv in
        let env = F_TcEnv.commit_mark env in
        dsenv, env in

    let check_frag (dsenv, env) curmod text =  
        match tc_one_fragment curmod dsenv env text with 
            | Some (m, dsenv, env) -> 
              Some (m, (dsenv, env), FStar.Tc.Errors.get_err_count())
            | _ -> None in

    let report_fail () = 
        Tc.Errors.report_all() |> ignore;
        Tc.Errors.num_errs := 0 in

    { pop = pop; 
      push = push;
      mark = mark;
      reset_mark = reset_mark;
      commit_mark = commit_mark;
      check_frag = check_frag;
      report_fail = report_fail}

(* universal *)
let universal_interactive_tc : interactive_tc<(U_DsEnv.env * U_TcEnv.env), option<U_Syntax.modul>> = 
    let pop (dsenv, env) msg = 
          U_DsEnv.pop dsenv |> ignore;
          U_TcEnv.pop env msg |> ignore;
          env.solver.refresh();
          Options.reset_options() |> ignore in

    let push (dsenv, env) msg = 
          let dsenv = U_DsEnv.push dsenv in
          let env = U_TcEnv.push env msg in
          (dsenv, env) in

    let mark (dsenv, env) =
        let dsenv = U_DsEnv.mark dsenv in
        let env = U_TcEnv.mark env in
        dsenv, env in

    let reset_mark (dsenv, env) =
        let dsenv = U_DsEnv.reset_mark dsenv in
        let env = U_TcEnv.reset_mark env in
        dsenv, env in

    let commit_mark (dsenv, env) =
        let dsenv = U_DsEnv.commit_mark dsenv in
        let env = U_TcEnv.commit_mark env in
        dsenv, env in

    let check_frag (dsenv, (env:U_TcEnv.env)) curmod text =  
        match u_tc_one_fragment curmod dsenv env text with 
            | Some (m, dsenv, env) -> 
              Some (m, (dsenv, env), FStar.Tc.Errors.get_err_count())
            | _ -> None in

    let report_fail () = 
        TypeChecker.Errors.report_all() |> ignore;
        TypeChecker.Errors.num_errs := 0 in

    { pop = pop; 
      push = push;
      mark = mark;
      reset_mark = reset_mark;
      commit_mark = commit_mark;
      check_frag = check_frag;
      report_fail = report_fail}


(****************************************************************************)
(* Extraction to OCaml or FSharp *)
(****************************************************************************)
let codegen fmods env =
  if !Options.codegen = Some "OCaml" ||
     !Options.codegen = Some "FSharp"
  then begin
    let c, mllibs = Util.fold_map Extraction.ML.ExtractMod.extract (Extraction.ML.Env.mkContext env) fmods in
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
          then let fmods, dsenv, env = u_batch_mode_tc filenames in //check all the dependences in batch mode
               interactive_mode (dsenv, env) None universal_interactive_tc //and then start checking chunks from the current buffer
          else let fmods, dsenv, env = batch_mode_tc filenames in //check all the dependences in batch mode
               interactive_mode (dsenv, env) None stratified_interactive_tc //and then start checking chunks from the current buffer

        else if List.length filenames >= 1 then //normal batch mode
          if !Options.universes
          then let fmods, dsenv, env = u_batch_mode_tc filenames in
               report_errors None;
               finished_message (fmods |> List.map (fun m -> m.is_interface, m.name))               
          else let fmods, dsenv, env = batch_mode_tc filenames in
               report_errors None;
               codegen fmods env;
               finished_message (fmods |> List.map (fun m -> m.is_interface, m.name))
        else
          Util.print_error "no file provided\n"

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
