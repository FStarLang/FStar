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
    push:        'env -> bool -> string -> 'env;
    mark:        'env -> 'env;
    reset_mark:  'env -> 'env;
    commit_mark: 'env -> 'env;
    check_frag:  'env -> 'modul -> FStar.Parser.ParseIt.input_frag -> option<('modul * 'env * int)>;
    report_fail:  unit -> unit;
    tc_prims:     unit -> 'env;
    tc_one_file:  list<string> -> 'env -> (option<string> * string) * 'env * 'modul * list<string>
}

(****************************************************************************************)
(* Internal data structures for managing chunks of input from the editor                *)
(****************************************************************************************)
type input_chunks =
  | Push of (bool * int * int) //the bool flag indicates lax flag set from the editor
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
    if Options.debug_any() then
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
  else if Util.starts_with l "#push" then (Util.clear_string_builder s.chunk;
        let lc_lax = Util.trim_string (Util.substring_from l (String.length "#push")) in
        let lc = match Util.split lc_lax " " with
            | [l; c; "#lax"] -> true, Util.int_of_string l, Util.int_of_string c
            | [l; c]         -> false, Util.int_of_string l, Util.int_of_string c
            | _              ->
              Util.print_warning ("Error locations may be wrong, unrecognized string after #push: " ^ lc_lax);
              false, 1, 0
        in
        Push lc)
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
let detect_dependencies_with_first_interactive_chunk () : string         //the filename of the buffer being checked, if any
                                                        * list<string>   //all its dependences 
  =
  let failr msg r =
    if Options.universes()
    then FStar.TypeChecker.Errors.warn r msg
    else FStar.Tc.Errors.warn r msg;
    exit 1
  in
  let fail msg = failr msg Range.dummyRange in
  let parse_msg = "Dependency analysis may not be correct because the file failed to parse: " in
  try
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
          | Some (None, Some filename)
          | Some (Some filename, None) ->
              Options.add_verify_module module_name;
              let _, all_filenames, _ = Parser.Dep.collect Parser.Dep.VerifyUserList [ filename ] in
              filename, List.rev (List.tl all_filenames)
          | Some (Some _, Some _) ->
             fail (Util.format1 "The combination of split interfaces and \
               interactive verification is not supported for: %s\n" module_name)
          | Some (None, None) ->
              failwith "impossible"

  with
  | U_Syntax.Error(msg, r)
  | F_Syntax.Error(msg, r) ->
      failr (parse_msg ^ msg) r
  | U_Syntax.Err msg
  | F_Syntax.Err msg ->
      fail (parse_msg ^ msg)


(******************************************************************************************)
(* The main interactive loop *)
(******************************************************************************************)
open FStar.Parser.ParseIt

type m_timestamps = list<(option<string> * string * time)>

let interactive_mode (filename:option<string>) (filenames:list<string>) (initial_mod:'modul) (tc:interactive_tc<'env,'modul>) =
    Util.print1 "Interactive mode called with: %s\n" (List.fold_left (fun s f -> s ^ f) "" filenames);

    if Option.isSome (Options.codegen()) 
    then Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag";

    let rec tc_deps (stack:stack<'env,'modul>) (env:'env) (remaining:list<string>) (ts:m_timestamps) = //:stack<'env,'modul> * 'env * m_timestamps =
      match remaining with
        | [] -> stack, env, ts
        | _  ->
          //invariant: length stack = length ts
          let (intf, impl), env, modl, remaining = tc.tc_one_file remaining env in
          let stack = (env, modl)::stack in
          Util.print_string "\nCalling push\n";
          let env = tc.push env true "tc modul" in  //AR: TODO: Here choosing lax to be true, more configurable?
          tc_deps stack env remaining (ts@[intf, impl, now()])
    in 
    
    //AR: TODO: make this code f#/ocaml independent by adding a utility in basic/util.fs and basic/ml/FStar_Util.ml
    let update_deps (stk:stack<'env, 'modul>) (env:'env) (ts:m_timestamps) = //:(stack<'env, 'modul> * 'env * m_timestamps) =
      Util.print_string "Update deps called";
      //invariant: length stack = length ts
      let is_stale (intf:option<string>) (impl:string) (t:time) :bool =
        (is_file_modified_after impl t ||
         (match intf with
            | Some f -> is_file_modified_after f t
            | None   -> false))
      in

      let rec iterate (good_stack:stack<'env, 'modul>) (good_ts:m_timestamps) (stack:stack<'env, 'modul>) (env:'env) (ts:m_timestamps) = //:(stack<'env, 'modul> * 'env * m_timestamps) =
        //invariant length good_stack = length good_ts, and same for stack and ts
        match stack, ts with
            | (env, modl)::stack, (intf, impl, t)::ts' ->
              if is_stale intf impl t then
                //collect all the file names
                let filenames = List.fold_left (fun acc (intf, impl, _) ->
                  Util.print_string "\nCalling pop\n";
                  tc.pop env "";
                  match intf with
                    | Some f -> acc @ [f; impl]
                    | None   -> acc @ [impl]
                ) [] ts in
                tc_deps (List.rev good_stack) env filenames good_ts
              else iterate (good_stack@[env, modl]) (good_ts@[intf, impl, t]) stack env ts'
            | [], [] ->
              Util.print_string "No file was found stale\n";
              List.rev good_stack, env, good_ts
            | _, _   -> failwith "Impossible"
      in

      iterate [] [] (List.rev stk) env ts
    in

    let rec go line_col (stack:stack<'env,'modul>) (curmod:'modul) (env:'env) (ts:m_timestamps) = begin
      match shift_chunk () with
      | Pop msg ->
          tc.pop env msg;
          let (env, curmod), stack =
            match stack with
            | [] -> Util.print_error "too many pops"; exit 1
            | hd::tl -> hd, tl
          in
          go line_col stack curmod env ts

      | Push (lax, l, c) ->
          let stack, env, ts = if List.length stack = List.length ts then update_deps stack env ts else stack, env, ts in
          let stack = (env, curmod)::stack in
          let env = tc.push env lax "#push" in
//          Util.print2 "Got push (%s, %s)" (Util.string_of_int <| fst lc) (Util.string_of_int <| snd lc);
          go (l, c) stack curmod env ts

      | Code (text, (ok, fail)) ->
          let fail curmod env_mark =
            tc.report_fail();
            Util.print1 "%s\n" fail;
            let env = tc.reset_mark env_mark in
            go line_col stack curmod env ts in

          let env_mark = tc.mark env in
          let frag = {frag_text=text;
                      frag_line=fst line_col; 
                      frag_col=snd line_col} in
//          Util.print3 "got frag %s, %s, %s" frag.frag_text 
//            (Util.string_of_int frag.frag_line)
//            (Util.string_of_int frag.frag_col);
          let res = tc.check_frag env_mark curmod frag in begin
            match res with
            | Some (curmod, env, n_errs) ->
                if n_errs=0 then begin
                  Util.print1 "\n%s\n" ok;
                  let env = tc.commit_mark env in
                  go line_col stack curmod env ts
                  end
                else fail curmod env_mark
            | _ -> fail curmod env_mark
            end
    end in

    let env = tc.tc_prims () in
    let stack, env, ts = tc_deps [] env filenames [] in 

    if Options.universes()
    && (FStar.Options.record_hints() //and if we're recording or using hints
    || FStar.Options.use_hints())
    && Option.isSome filename
    then FStar.SMTEncoding.Solver.with_hints_db (Option.get filename) (fun () -> go (1, 0) stack initial_mod env ts)
    else go (1, 0) stack initial_mod env ts
