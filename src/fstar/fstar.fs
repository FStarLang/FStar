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
open FStar.Tc.Env

let process_args () =
  let file_list = Util.mk_ref [] in
  let res = Getopt.parse_cmdline (Options.specs()) (fun i -> file_list := !file_list @ [i]) in
    (match res with
       | GoOn -> ignore (Options.set_fstar_home ())
       | _ -> ());
    (res, !file_list)

let cleanup () = Util.kill_all ()

let has_prims_cache (l: list<string>) :bool = List.mem "Prims.cache" l

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
        print1 "Error: %s errors were reported (see above)\n" (string_of_int errs);
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
              let modul, npds, env = Tc.Tc.tc_partial_modul env modul in
              Some (Some (modul, npds), dsenv, env)

            | Parser.Driver.Decls (dsenv, decls) ->
              begin match curmod with
                | None -> failwith "Fragment without an enclosing module"
                | Some (modul,npds) ->
                  let modul, npds', env  = Tc.Tc.tc_more_partial_modul env modul decls in
                  Some (Some (modul, npds@npds'), dsenv, env)
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
    (option<(modul * list<sigelt>)>
     * Parser.DesugarEnv.env
     * Tc.Env.env)
type stack = list<stack_elt>


let batch_mode_tc_no_prims dsenv env filenames =
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
      files
    else
      let _, deps = Parser.Dep.collect files in
      (* Use just the file name: it's in one of the include directories, after
       * all; furthermore, the dependency check enforce the "no duplicate
       * filenames" policy. *)
      let deps = List.rev deps in
      List.iter print_endline deps;
      let deps =
        if basename (List.hd deps) = "prims.fst" then
          List.tl deps
        else
          failwith "dependency analysis did not find prims.fst?!"
      in
      List.iter (fun d ->
        let d = basename d in
        if get_file_extension d = ".fsti" then
          Options.admit_fsi := substring d 0 (String.length d - 5) :: !Options.admit_fsi
        else if get_file_extension d = ".fsi" then
          Options.admit_fsi := substring d 0 (String.length d - 4) :: !Options.admit_fsi
      ) deps;
      deps

let batch_mode_tc filenames =
    let prims_mod, dsenv, env = tc_prims () in

    let filenames = find_deps_if_needed filenames in
    let all_mods, dsenv, env = batch_mode_tc_no_prims dsenv env filenames in
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
         print_string "\x1b[0;1mAll verification conditions discharged successfully\x1b[0m\n"
    end

type interactive_state = {
  chunk: string_builder;
  stdin: ref<option<stream_reader>>; // Initialized once.
  buffer: ref<list<input_chunks>>; // The buffer has at most size one.
}

let interactive_state = {
  chunk = Util.new_string_builder ();
  stdin = ref None;
  buffer = ref []
}

let rec read_chunk () =
    let should_log = !Options.debug <> [] in
    let log =
        if should_log
        then let transcript = Util.open_file_for_writing "transcript" in
             (fun line -> Util.append_to_file transcript line;
                          Util.flush_file transcript)
        else (fun line -> ()) in

    let s = interactive_state in
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
  let s = interactive_state in
  match !s.buffer with
  | [] ->
      read_chunk ()
  | chunk :: chunks ->
      s.buffer := chunks;
      chunk

let fill_buffer () =
  let s = interactive_state in
  s.buffer := !s.buffer @ [ read_chunk () ]

let interactive_mode dsenv env =
    if Option.isSome !Options.codegen
    then (Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag");

    let rec go (stack:stack) curmod dsenv env =
        begin match shift_chunk () with
            | Pop msg ->
              Parser.DesugarEnv.pop dsenv |> ignore;
              Tc.Env.pop env msg |> ignore;
              env.solver.refresh();
              Options.reset_options() |> ignore;
              let (curmod, dsenv, env), stack = match stack with
                | [] -> failwith "Too many pops"
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
                    Util.print1 "%s\n" fail;
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
        List.iter (fun (n,d) -> Util.write_file (Options.prependOutputDir (n^ext)) (FSharp.Format.pretty 120 d)) newDocs
    end

exception Found of string

let find_initial_module_name () =
  fill_buffer (); fill_buffer ();
  try begin match !interactive_state.buffer with
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
        (* This is the fstardep tool *)
        Parser.Dep.print (Parser.Dep.collect filenames)
      else if !Options.interactive then
        (* Interactive mode *)
        match find_initial_module_name () with
        | None ->
            Util.print_string "No initial module directive found\n";
        | Some module_name ->
            let file_of_module_name = Parser.Dep.build_map [] in
            let filename = smap_try_find file_of_module_name (String.lowercase module_name) in
            match filename with
            | None ->
                Util.print2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name
            | Some filename ->
                let _, all_filenames = Parser.Dep.collect [ filename ] in
                let fmods, dsenv, env = batch_mode_tc (List.rev (List.tl all_filenames)) in
                interactive_mode dsenv env
      else if List.length filenames >= 1 then
        (* Normal mode of operations *)
        (let fmods, dsenv, env = batch_mode_tc filenames in
        report_errors None;
        codegen fmods env;
        finished_message fmods)
      else
        Util.print_string "No file provided\n"

let main () =
    try
      go ();
      cleanup ();
      exit 0
    with
    | e ->
        if Util.handleable e then Util.handle_err false () e;
        if !Options.trace_error
        then Util.print2 "\nUnexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
        else if not (Util.handleable e)
        then Util.print1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e);
        cleanup ();
        exit 1
