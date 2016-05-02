(*
   Copyright 2008-2016  Nikhil Swamy and Microsoft Research

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

//Batch-mode type-checking for the stratified type-checker
module FStar.Interactive
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident

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

(****************************************************************************************)
(* Internal data structures for managing chunks of input from the editor                *)
(****************************************************************************************)
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

module U_Syntax = FStar.Syntax.Syntax
module F_Syntax = FStar.Absyn.Syntax
let detect_dependencies_with_first_interactive_chunk () =
 try
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
              Options.verify_module := [ String.lowercase module_name ];
              let _, all_filenames = Parser.Dep.collect [ filename ] in
              List.rev (List.tl all_filenames)
 with 
    | U_Syntax.Error(msg, r) -> 
      FStar.TypeChecker.Errors.warn r msg;
      FStar.TypeChecker.Errors.warn r ("Dependency analysis may not be correct because the file failed to parse: "^msg);
      [] 
    | F_Syntax.Error(msg, r) -> 
      FStar.Tc.Errors.warn r msg;
      FStar.Tc.Errors.warn r ("Dependency analysis may not be correct because the file failed to parse: "^msg);
      [] 
    | U_Syntax.Err msg
    | F_Syntax.Err msg -> 
      FStar.Tc.Errors.warn Range.dummyRange ("Dependency analysis may not be correct because the file failed to parse: " ^msg);
      []
          

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
