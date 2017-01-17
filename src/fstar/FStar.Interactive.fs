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
    push:        'env -> bool -> bool -> string -> 'env;
    mark:        'env -> 'env;
    reset_mark:  'env -> 'env;
    commit_mark: 'env -> 'env;
    check_frag:  'env -> 'modul -> FStar.Parser.ParseIt.input_frag -> option<('modul * 'env * int)>;
    report_fail:  unit -> unit;
    tc_prims:     unit -> 'env;
    tc_one_file:  list<string> -> 'env -> (option<string> * string) * 'env * 'modul * list<string>;
    //cleanup is currently called when all the fragments from the current buffer are popped
    //the reason is that tc_partial_modul in tc.fs currently calls a solver.push, that needs to be popped before next fragment is type checked
    //so the implementation of this (in universal.fs) calls solver.pop currently
    cleanup:     'env -> unit
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
  stdin = mk_ref None;
  buffer = mk_ref [];
  log = mk_ref None
}

(***********************************************************************)
(* Reading some input *)
(***********************************************************************)
let rec read_chunk () =
  let s = the_interactive_state in
  let log : string -> unit =
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


(******************************************************************************************)
(* The main interactive loop *)
(******************************************************************************************)
open FStar.Parser.ParseIt

let deps_of_our_file filename =
  (* Now that fstar-mode.el passes the name of the current file, we must parse
   * and lax-check everything but the current module we're editing. *)
  let deps = FStar.Dependencies.find_deps_if_needed Parser.Dep.VerifyFigureItOut [ filename ] in
  List.filter (fun x ->
    Parser.Dep.lowercase_module_name x <> Parser.Dep.lowercase_module_name filename
  ) deps

(* .fsti name (optional) * .fst name * .fsti recorded timestamp (optional) * .fst recorded timestamp  *)
type m_timestamps = list<(option<string> * string * option<time> * time)>

    (*
     * type check remaining dependencies and record the timestamps.
     * m is the current module name, not the module name of the dependency. it's actually a dummy that is pushed on the stack and never used.
     * it is used for type checking the fragments of the current module, but for dependencies it is a dummy.
     * adding it as the stack entry needed it.
     * env is the environment in which next dependency should be type checked.
     * the returned timestamps are in the reverse order (i.e. final dependency first), it's the same order as the stack.
     * note that for dependencies, the stack and ts go together (i.e. their sizes are same)
     * returns the new stack, environment, and timestamps.
     *)
    let rec tc_deps (tc:interactive_tc<'env,'modul>) (m:'modul) (stack:stack<'env,'modul>) 
		    (env:'env) (remaining:list<string>) (ts:m_timestamps) 
//      : stack<'env,'modul> * 'env * m_timestamps
      = match remaining with
        | [] -> stack, env, ts
        | _  ->
          let stack = (env, m)::stack in
          //setting the restore command line options flag true
          let env = tc.push env (Options.lax ()) true "typecheck_modul" in
          let (intf, impl), env, modl, remaining = tc.tc_one_file remaining env in
          let intf_t, impl_t =
            let intf_t =
              match intf with
                | Some intf -> Some (get_file_last_modification_time intf)
                | None      -> None
            in
            let impl_t = get_file_last_modification_time impl in
            intf_t, impl_t
          in
          tc_deps tc m stack env remaining ((intf, impl, intf_t, impl_t)::ts)


    (*
     * check if some dependencies have been modified, added, or deleted
     * if so, only type check them and anything that follows, while maintaining others as is (current dependency graph is a total order)
     * we will first compute the dependencies again, and then traverse the ts list
     * if we find that the dependency at the head of ts does not match that at the head of the newly computed dependency,
     * or that the dependency is stale, we will typecheck that dependency, and everything that comes after that again
     * the stack and timestamps are passed in "last dependency first" order, so we will reverse them before checking
     * as with tc_deps, m is the dummy argument used for the stack entry
     * returns the new stack, environment, and timestamps
     *)
    let update_deps (filename:string) (tc:interactive_tc<'env,'modul>) (m:'modul) (stk:stack<'env, 'modul>) (env:'env) (ts:m_timestamps) 
      : (stack<'env, 'modul> * 'env * m_timestamps) =
      let is_stale (intf:option<string>) (impl:string) (intf_t:option<time>) (impl_t:time) :bool =
        let impl_mt = get_file_last_modification_time impl in
        (is_before impl_t impl_mt ||
         (match intf, intf_t with
            | Some intf, Some intf_t ->
              let intf_mt = get_file_last_modification_time intf in
              is_before intf_t intf_mt
            | None, None             -> false
            | _, _                   -> failwith "Impossible, if the interface is None, the timestamp entry should also be None"))
      in

      (*
       * iterate over the timestamps list
       * if the current entry matches the head of the deps, and is not stale, then leave it as is, and go to next, else discard everything after that and tc_deps the deps again
       * good_stack and good_ts are stack and timestamps that are not stale so far
       * st and ts are expected to be in "first dependency first order"
       * also, for the first call to iterate, good_stack and good_ts are empty
       * during recursive calls, the good_stack and good_ts grow "last dependency first" order.
       * returns the new stack, environment, and timestamps
       *)
      let rec iterate (depnames:list<string>) (st:stack<'env, 'modul>) (env':'env) (ts:m_timestamps) (good_stack:stack<'env, 'modul>) (good_ts:m_timestamps) = //:(stack<'env, 'modul> * 'env * m_timestamps) =
        //invariant length good_stack = length good_ts, and same for stack and ts

        let match_dep (depnames:list<string>) (intf:option<string>) (impl:string) : (bool * list<string>) =
          match intf with
            | None      ->
              (match depnames with
                 | dep::depnames' -> if dep = impl then true, depnames' else false, depnames
                 | _              -> false, depnames)
            | Some intf ->
              (match depnames with
                 | depintf::dep::depnames' -> if depintf = intf && dep = impl then true, depnames' else false, depnames
                 | _                       -> false, depnames)
        in

        //expected the stack to be in "last dependency first order", we want to pop in the proper order (although should not matter)
        let rec pop_tc_and_stack env (stack:list<('env * 'modul)>) ts =
          match ts with
            | []    -> (* stack should also be empty here *) env
            | _::ts ->
              //pop
              tc.pop env "";
              let (env, _), stack = List.hd stack, List.tl stack in
              pop_tc_and_stack env stack ts
        in

        match ts with
          | ts_elt::ts' ->
            let intf, impl, intf_t, impl_t = ts_elt in
            let b, depnames' = match_dep depnames intf impl in
            if not b || (is_stale intf impl intf_t impl_t) then
              //reverse st from "first dependency first order" to "last dependency first order"
              let env = pop_tc_and_stack env' (List.rev_append st []) ts in
              tc_deps tc m good_stack env depnames good_ts
            else
              let stack_elt, st' = List.hd st, List.tl st in
              iterate depnames' st' env' ts' (stack_elt::good_stack) (ts_elt::good_ts)
          | []           -> (* st should also be empty here *) tc_deps tc m good_stack env' depnames good_ts
      in

      (* Well, the file list hasn't changed, so our (single) file is still there. *)
      let filenames = deps_of_our_file filename in
      //reverse stk and ts, since iterate expects them in "first dependency first order"
      iterate filenames (List.rev_append stk []) env (List.rev_append ts []) [] []

    let rec go (line_col:(int*int))
	       (filename:string) 
	       (tc:interactive_tc<'env,'modul>) 
	       (stack:stack<'env,'modul>) (curmod:'modul) (env:'env) (ts:m_timestamps) : unit = begin
      match shift_chunk () with
      | Pop msg ->
          tc.pop env msg;
          let (env, curmod), stack =
            match stack with
            | [] -> Util.print_error "too many pops"; exit 1
            | hd::tl -> hd, tl
          in
          //all the fragments from the current buffer have been popped, call cleanup
          let _ = if List.length stack = List.length ts then tc.cleanup env else () in
          go line_col filename tc stack curmod env ts

      | Push (lax, l, c) ->
          //if we are at a stage where we have not yet pushed a fragment from the current buffer, see if some dependency is stale
          //if so, update it
          //also if this is the first chunk, we need to restore the command line options
          let restore_cmd_line_options, (stack, env, ts) =
            if List.length stack = List.length ts then true, update_deps filename tc curmod stack env ts else false, (stack, env, ts)
          in
          let stack = (env, curmod)::stack in
          let env = tc.push env lax restore_cmd_line_options "#push" in
          go (l, c) filename tc stack curmod env ts

      | Code (text, (ok, fail)) ->
          let fail curmod env_mark =
            tc.report_fail();
            Util.print1 "%s\n" fail;
            let env = tc.reset_mark env_mark in
            go line_col filename tc stack curmod env ts
          in

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
                  go line_col filename tc stack curmod env ts
                  end
                else fail curmod env_mark
            | _ -> fail curmod env_mark
            end
    end

// filename is the name of the file currently edited
let interactive_mode (filename:string)
                     (initial_mod:'modul)
                     (tc:interactive_tc<'env,'modul>) : unit =
    if Option.isSome (Options.codegen())
    then Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag";

    //type check prims and the dependencies
    let filenames = deps_of_our_file filename in
    let env = tc.tc_prims () in
    let stack, env, ts = tc_deps tc initial_mod [] env filenames [] in

    if Options.universes()
    && (FStar.Options.record_hints() //and if we're recording or using hints
    || FStar.Options.use_hints())
    then FStar.SMTEncoding.Solver.with_hints_db (List.hd (Options.file_list ())) (fun () -> go (1, 0) filename tc stack initial_mod env ts)
    else go (1, 0) filename tc stack initial_mod env ts
