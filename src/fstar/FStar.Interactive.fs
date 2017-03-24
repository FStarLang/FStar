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

module FStar.Interactive
open FStar.All
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident

open FStar.Universal
open FStar.TypeChecker.Env

module DsEnv   = FStar.ToSyntax.Env
module TcEnv   = FStar.TypeChecker.Env

// A custom version of the function that's in FStar.Universal.fs just for the
// sake of the interactive mode
let tc_one_file (remaining:list<string>) (uenv:uenv) = //:((string option * string) * uenv * modul option * string list) =
  let dsenv, env = uenv in
  let (intf, impl), dsenv, env, remaining =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let _, dsenv, env = tc_one_file_and_intf (Some intf) impl dsenv env in
          (Some intf, impl), dsenv, env, remaining
        | intf_or_impl :: remaining ->
          let _, dsenv, env = tc_one_file_and_intf None intf_or_impl dsenv env in
          (None, intf_or_impl), dsenv, env, remaining
        | [] -> failwith "Impossible"
  in
  (intf, impl), (dsenv, env), None, remaining

// Ibid.
let tc_prims () = //:uenv =
  let _, dsenv, env = tc_prims () in
  (dsenv, env)


// The interactive mode has its own notion of a stack that is super flaky,
// seeing that there's a lot of mutable state under the hood. This is most
// likely not working as the original author intended it to.

type env_t = DsEnv.env * TcEnv.env
type modul_t = option<Syntax.Syntax.modul>
type stack_t = list<(env_t * modul_t)>

// Note: many of these functions are passing env around just for the sake of
// providing a link to the solver (to avoid a cross-project dependency). They're
// not actually doing anything useful with the environment you're passing it (e.g.
// pop or reset_mark).

let pop (_, env) msg =
    pop_context env msg;
    Options.pop()

let push ((dsenv: DsEnv.env), env) lax restore_cmd_line_options msg =
    let env = { env with lax = lax } in
    let res = push_context (dsenv, env) msg in
    Options.push();
    if restore_cmd_line_options then Options.restore_cmd_line_options false |> ignore;
    res

let mark (dsenv, env) =
    let dsenv = DsEnv.mark dsenv in
    let env = TcEnv.mark env in
    Options.push();
    dsenv, env

let reset_mark (_, env) =
    let dsenv = DsEnv.reset_mark () in
    let env = TcEnv.reset_mark env in
    Options.pop();
    dsenv, env

let cleanup (dsenv, env) = TcEnv.cleanup_interactive env

let commit_mark (dsenv, env) =
    let dsenv = DsEnv.commit_mark dsenv in
    let env = TcEnv.commit_mark env in
    dsenv, env

let check_frag (dsenv, (env:TcEnv.env)) curmod text =
    try
        match tc_one_fragment curmod dsenv env text with
            | Some (m, dsenv, env) ->
                  Some (m, (dsenv, env), FStar.Errors.get_err_count())
            | _ -> None
    with
        | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
          FStar.TypeChecker.Err.add_errors env [(msg, r)];
          None

        | FStar.Errors.Err msg when not ((Options.trace_error())) ->
          FStar.TypeChecker.Err.add_errors env [(msg, FStar.TypeChecker.Env.get_range env)];
          None

let report_fail () =
    FStar.Errors.report_all() |> ignore;
    FStar.Errors.num_errs := 0

(******************************************************************************************)
(* The interface expected to be provided by a type-checker to run in the interactive loop *)
(******************************************************************************************)


(****************************************************************************************)
(* Internal data structures for managing chunks of input from the editor                *)
(****************************************************************************************)
type input_chunks =
  | Push of bool * int * int //the bool flag indicates lax flag set from the editor
  | Pop  of string
  | Code of string * (string * string)
  | Info of string * int * int


type interactive_state = {
  // The current chunk -- chunks end on #end boundaries per the communication
  // protocol.
  chunk: string_builder;
  stdin: ref<option<stream_reader>>; // Initialized once.
  // A list of chunks read so far
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
  else if Util.starts_with l "#push" then (
        Util.clear_string_builder s.chunk;
        let lc_lax = Util.trim_string (Util.substring_from l (String.length "#push")) in
        let lc = match Util.split lc_lax " " with
            | [l; c; "#lax"] -> true, Util.int_of_string l, Util.int_of_string c
            | [l; c]         -> false, Util.int_of_string l, Util.int_of_string c
            | _              ->
              Util.print_warning ("Error locations may be wrong, unrecognized string after #push: " ^ lc_lax);
              false, 1, 0
        in
        Push lc)
  else if Util.starts_with l "#info" then
      match Util.split l " " with
      | [_; file; row; col] ->
        Util.clear_string_builder s.chunk;
        Info (file, Util.int_of_string row, Util.int_of_string col)
      | _ ->
        Util.print_error ("Unrecognized \"#info\" request: " ^l);
        exit 1
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
   * and lax-check everything but the current module we're editing. This
   * function may, optionally, return an interface if the currently edited
   * module is an implementation and an interface was found. *)
  let deps = FStar.Dependencies.find_deps_if_needed Parser.Dep.VerifyFigureItOut [ filename ] in
  let deps, same_name = List.partition (fun x ->
    Parser.Dep.lowercase_module_name x <> Parser.Dep.lowercase_module_name filename
  ) deps in
  let maybe_intf = match same_name with
    | [ intf; impl ] ->
        if not (Parser.Dep.is_interface intf) || not (Parser.Dep.is_implementation impl) then
          Util.print_warning (Util.format2 "Found %s and %s but not an interface + implementation" intf impl);
        Some intf
    | [ impl ] ->
        None
    | _ ->
        Util.print_warning (Util.format1 "Unexpected: ended up with %s" (String.concat " " same_name));
        None
  in
  deps, maybe_intf

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
let rec tc_deps (m:modul_t) (stack:stack_t) 
                (env:env_t) (remaining:list<string>) (ts:m_timestamps) 
//      : stack<'env,modul_t> * 'env * m_timestamps
  = match remaining with
    | [] -> stack, env, ts
    | _  ->
      let stack = (env, m)::stack in
      //setting the restore command line options flag true
      let env = push env (Options.lax ()) true "typecheck_modul" in
      let (intf, impl), env, modl, remaining = tc_one_file remaining env in
      let intf_t, impl_t =
        let intf_t =
          match intf with
            | Some intf -> Some (get_file_last_modification_time intf)
            | None      -> None
        in
        let impl_t = get_file_last_modification_time impl in
        intf_t, impl_t
      in
      tc_deps m stack env remaining ((intf, impl, intf_t, impl_t)::ts)


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
let update_deps (filename:string) (m:modul_t) (stk:stack_t) (env:env_t) (ts:m_timestamps) 
  : (stack_t * env_t * m_timestamps) =
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
  let rec iterate (depnames:list<string>) (st:stack_t) (env':env_t)
  (ts:m_timestamps) (good_stack:stack_t) (good_ts:m_timestamps) = //:(stack<'env, modul_t> * 'env * m_timestamps) =
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
    let rec pop_tc_and_stack env (stack:list<(env_t * modul_t)>) ts =
      match ts with
        | []    -> (* stack should also be empty here *) env
        | _::ts ->
          //pop
          pop env "";
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
          tc_deps m good_stack env depnames good_ts
        else
          let stack_elt, st' = List.hd st, List.tl st in
          iterate depnames' st' env' ts' (stack_elt::good_stack) (ts_elt::good_ts)
      | []           -> (* st should also be empty here *) tc_deps m good_stack env' depnames good_ts
  in

  (* Well, the file list hasn't changed, so our (single) file is still there. *)
  let filenames, _ = deps_of_our_file filename in
  //reverse stk and ts, since iterate expects them in "first dependency first order"
  iterate filenames (List.rev_append stk []) env (List.rev_append ts []) [] []

let rec go (line_col:(int*int))
           (filename:string) 
           (stack:stack_t) (curmod:modul_t) (env:env_t) (ts:m_timestamps) : unit = begin
  match shift_chunk () with
  | Info(file, row, col) ->
    let iopt = FStar.TypeChecker.Err.info_at_pos (snd env) file row col in
    (match iopt with
     | None ->
       Util.print_string "\n#done-nok\n"
     | Some s ->
       Util.print1 "%s\n#done-ok\n" s);
    go line_col filename stack curmod env ts
  | Pop msg ->
      // This shrinks all internal stacks by 1
      pop env msg;
      let (env, curmod), stack =
        match stack with
        | [] -> Util.print_error "too many pops"; exit 1
        | hd::tl -> hd, tl
      in
      //all the fragments from the current buffer have been popped, call cleanup
      let _ = if List.length stack = List.length ts then cleanup env else () in
      go line_col filename stack curmod env ts

  | Push (lax, l, c) ->
      // This grows all internal stacks by 1
      //if we are at a stage where we have not yet pushed a fragment from the current buffer, see if some dependency is stale
      //if so, update it
      //also if this is the first chunk, we need to restore the command line options
      let restore_cmd_line_options, (stack, env, ts) =
        if List.length stack = List.length ts then true, update_deps filename curmod stack env ts else false, (stack, env, ts)
      in
      let stack = (env, curmod)::stack in
      let env = push env lax restore_cmd_line_options "#push" in
      go (l, c) filename stack curmod env ts

  | Code (text, (ok, fail)) ->
      // This does not grow any of the internal stacks.
      let fail curmod env_mark =
        report_fail();
        Util.print1 "%s\n" fail;
        // Side-effect: pops from an internal, hidden stack
        // At this stage, the internal stack has grown with size 1. BUT! The
        // interactive mode will send us a pop message.
        let env = reset_mark env_mark in
        go line_col filename stack curmod env ts
      in

      // Side-effect: pushes to an internal, hidden stack
      let env_mark = mark env in
      let frag = {frag_text=text;
                  frag_line=fst line_col;
                  frag_col=snd line_col} in
//          Util.print3 "got frag %s, %s, %s" frag.frag_text
//            (Util.string_of_int frag.frag_line)
//            (Util.string_of_int frag.frag_col);
      let res = check_frag env_mark curmod frag in begin
        match res with
        | Some (curmod, env, n_errs) ->
            if n_errs=0 then begin
              Util.print1 "\n%s\n" ok;
              // Side-effect: pops from an internal, hidden stack
              // At this stage, the internal stack has grown with size 1.
              let env = commit_mark env in
              go line_col filename stack curmod env ts
              end
            else fail curmod env_mark
        | _ -> fail curmod env_mark
        end
end

// filename is the name of the file currently edited
let interactive_mode (filename:string): unit =

  if Option.isSome (Options.codegen())
  then Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag";

  //type check prims and the dependencies
  let filenames, maybe_intf = deps_of_our_file filename in
  let env = tc_prims () in
  let stack, env, ts = tc_deps None [] env filenames [] in

  let initial_mod, env = match maybe_intf with
    | Some intf ->
        // We found an interface: send it to the interactive mode as if it
        // were a regular chunk
        let frag = {
          frag_text = file_get_contents intf;
          frag_line = 0;
          frag_col = 0
        } in
        begin match check_frag env None frag with
        | Some (curmod, env, n_errs) ->
            if n_errs <> 0 then begin
              Util.print_warning (Util.format1
                "Found the interface %s but it has errors!"
                intf);
              exit 1
            end;
            Util.print_string "Reminder: fst+fsti in interactive mode is unsound.\n";
            curmod, env
        | None ->
            Util.print_warning (Util.format1
              "Found the interface %s but could not parse it first!"
              intf);
            exit 1
        end
    | None ->
        None, env
  in

  if FStar.Options.record_hints() //and if we're recording or using hints
  || FStar.Options.use_hints()
  then FStar.SMTEncoding.Solver.with_hints_db (List.hd (Options.file_list ())) (fun () -> go (1, 0) filename stack initial_mod env ts)
  else go (1, 0) filename stack initial_mod env ts
