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

module FStar.Interactive.Legacy
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident

open FStar.Universal
open FStar.TypeChecker.Env
open FStar.Parser

module DsEnv   = FStar.Syntax.DsEnv
module TcEnv   = FStar.TypeChecker.Env

// A custom version of the function that's in FStar.Universal.fs just for the
// sake of the interactive mode
let tc_one_file (remaining:list<string>) (env:TcEnv.env) = //:((string option * string) * uenv * string list) =
  let (intf, impl), env, remaining =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let _, env = tc_one_file_for_ide env (Some intf) impl Dep.empty_parsing_data in
          (Some intf, impl), env, remaining
        | intf_or_impl :: remaining ->
          let _, env = tc_one_file_for_ide env None intf_or_impl Dep.empty_parsing_data in
          (None, intf_or_impl), env, remaining
        | [] -> failwith "Impossible"
  in
  (intf, impl), env, remaining

// The interactive mode has its own notion of a stack that is super flaky,
// seeing that there's a lot of mutable state under the hood. This is most
// likely not working as the original author intended it to.

type env_t = TcEnv.env
type modul_t = option<Syntax.Syntax.modul>
type stack_t = list<(env_t * modul_t)>

// Note: many of these functions are passing env around just for the sake of
// providing a link to the solver (to avoid a cross-project dependency). They're
// not actually doing anything useful with the environment you're passing it (e.g.
// pop).

let pop env msg =
    ignore (TypeChecker.Tc.pop_context env msg);
    Options.pop()

let push_with_kind env lax restore_cmd_line_options msg =
    let env = { env with lax = lax } in
    let res = TypeChecker.Tc.push_context env msg in
    Options.push();
    if restore_cmd_line_options then Options.restore_cmd_line_options false |> ignore;
    res

let check_frag (env:TcEnv.env) curmod frag =
    try
        let m, env = tc_one_fragment curmod env frag in
        Some (m, env, FStar.Errors.get_err_count())
    with
        | FStar.Errors.Error(e, msg, r) when not ((Options.trace_error())) ->
          FStar.Errors.add_errors [(e, msg, r)];
          None

        | FStar.Errors.Err (e, msg) when not ((Options.trace_error())) ->
          FStar.Errors.add_errors [(e, msg, FStar.TypeChecker.Env.get_range env)];
          None

let report_fail () =
    FStar.Errors.report_all() |> ignore;
    FStar.Errors.clear()

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
  | Info of string * bool * option<(string * int * int)>
  | Completions of string


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
              Errors. log_issue Range.dummyRange (Errors.Warning_WrongErrorLocation, ("Error locations may be wrong, unrecognized string after #push: " ^ lc_lax));
              false, 1, 0
        in
        Push lc)
  else if Util.starts_with l "#info " then
      match Util.split l " " with
      | [_; symbol] ->
        Util.clear_string_builder s.chunk;
        Info (symbol, true, None)
      | [_; symbol; file; row; col] ->
        Util.clear_string_builder s.chunk;
        Info (symbol, false, Some (file, Util.int_of_string row, Util.int_of_string col))
      | _ ->
        Errors. log_issue Range.dummyRange (Errors.Error_IDEUnrecognized, "Unrecognized \"#info\" request: " ^l);
        exit 1
  else if Util.starts_with l "#completions " then
      match Util.split l " " with
      | [_; prefix; "#"] -> // Extra "#" marks the end of the input.  FIXME protocol could take more structured messages.
        Util.clear_string_builder s.chunk;
        Completions (prefix)
      | _ ->
        Errors. log_issue Range.dummyRange (Errors.Error_IDEUnrecognized, "Unrecognized \"#completions\" request: " ^ l);
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
  let deps, dep_graph = FStar.Dependencies.find_deps_if_needed [ filename ] FStar.CheckedFiles.load_parsing_data_from_cache in
  let deps, same_name = List.partition (fun x ->
    Parser.Dep.lowercase_module_name x <> Parser.Dep.lowercase_module_name filename
  ) deps in
  let maybe_intf = match same_name with
    | [ intf; impl ] ->
        if not (Parser.Dep.is_interface intf) || not (Parser.Dep.is_implementation impl) then
          Errors. log_issue Range.dummyRange (Errors.Warning_MissingInterfaceOrImplementation, (Util.format2 "Found %s and %s but not an interface + implementation" intf impl));
        Some intf
    | [ impl ] ->
        None
    | _ ->
        Errors. log_issue Range.dummyRange (Errors.Warning_UnexpectedFile, (Util.format1 "Unexpected: ended up with %s" (String.concat " " same_name)));
        None
  in
  deps, maybe_intf, dep_graph

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
                (env:TcEnv.env) (remaining:list<string>) (ts:m_timestamps)
//      : stack<'env,modul_t> * 'env * m_timestamps
  = match remaining with
    | [] -> stack, env, ts
    | _  ->
      let stack = (env, m)::stack in
      //setting the restore command line options flag true
      let env = push_with_kind env (Options.lax ()) true "typecheck_modul" in
      let (intf, impl), env, remaining = tc_one_file remaining env in
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
    let rec pop_tc_and_stack (env:env_t) (stack:list<(env_t * modul_t)>) ts =
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
  let filenames, _, dep_graph = deps_of_our_file filename in
  //reverse stk and ts, since iterate expects them in "first dependency first order"
  iterate filenames (List.rev_append stk []) env (List.rev_append ts []) [] []

let format_info env name typ range (doc: option<string>) =
  Util.format4 "(defined at %s) %s: %s%s"
    (Range.string_of_range range)
    name
    (FStar.TypeChecker.Normalize.term_to_string env typ)
    (match doc with
     | Some docstring -> Util.format1 "#doc %s" docstring
     | None -> "")

let rec go (line_col:(int*int))
           (filename:string)
           (stack:stack_t) (curmod:modul_t) (env:env_t) (ts:m_timestamps) : unit = begin
  match shift_chunk () with
  | Info(symbol, fqn_only, pos_opt) ->
    let info_at_pos_opt = match pos_opt with
      | None -> None
      | Some (file, row, col) -> FStar.TypeChecker.Err.info_at_pos env file row col in
    let info_opt = match info_at_pos_opt with
      | Some _ -> info_at_pos_opt
      | None -> // Use name lookup as a fallback
        if symbol = "" then None
        else let lid = Ident.lid_of_ids (List.map Ident.id_of_text (Util.split symbol ".")) in
             let lid = if fqn_only then lid
                       else match DsEnv.resolve_to_fully_qualified_name env.dsenv lid with
                            | None -> lid
                            | Some lid -> lid in
             try_lookup_lid env lid
               |> Util.map_option (fun ((_, typ), r) -> (Inr lid, typ, r)) in
    (match info_opt with
     | None -> Util.print_string "\n#done-nok\n"
     | Some (name_or_lid, typ, rng) ->
       let name, doc =
         match name_or_lid with
         | Inl name -> name, None
         | Inr lid -> Ident.string_of_lid lid, (DsEnv.try_lookup_doc env.dsenv lid |> Util.map_option fst) in
       Util.print1 "%s\n#done-ok\n" (format_info env name typ rng doc));
    go line_col filename stack curmod env ts
  | Completions search_term ->
    //search_term is the partially written identifer by the user
    // FIXME a regular expression might be faster than this explicit matching
    let rec measure_anchored_match
      : list<string> -> list<ident> -> option<(list<ident> * int)>
      //determines it the candidate may match the search term
      //and, if so, provides an integer measure of the degree of the match
      //Q: isn't the output list<ident> always the same as the candidate?
        // About the degree of the match, cpitclaudel says:
        //      Because we're measuring the length of the match and we allow partial
        //      matches. Say we're matching FS.Li.app against FStar.List.Append. Then
        //      the length we want is (length "FStar" + 1 + length "List" + 1 + length
        //      "app"), not (length "FStar" + 1 + length "List" + 1 + length
        //      "append"). This length is used to know how much of the candidate to
        //      highlight in the company-mode popup (we want to display the candidate
        //      as FStar.List.append.
      = fun search_term candidate ->
          match search_term, candidate with
          | [], _ -> Some ([], 0)
          | _, [] -> None
          | hs :: ts, hc :: tc ->
            let hc_text = FStar.Ident.text_of_id hc in
            if Util.starts_with hc_text hs then
               match ts with
               | [] -> Some (candidate, String.length hs)
               | _ -> measure_anchored_match ts tc |>
                        Util.map_option (fun (matched, len) -> (hc :: matched, String.length hc_text + 1 + len))
            else None in
    let rec locate_match
      : list<string> -> list<ident> -> option<(list<ident> * list<ident> * int)>
      = fun needle candidate ->
      match measure_anchored_match needle candidate with
      | Some (matched, n) -> Some ([], matched, n)
      | None ->
        match candidate with
        | [] -> None
        | hc :: tc ->
          locate_match needle tc |>
            Util.map_option (fun (prefix, matched, len) -> (hc :: prefix, matched, len)) in
    let str_of_ids ids = Util.concat_l "." (List.map FStar.Ident.text_of_id ids) in
    let match_lident_against needle lident =
        locate_match needle (lident.ns @ [lident.ident])
    in
    let shorten_namespace (prefix, matched, match_len) =
      let naked_match = match matched with [_] -> true | _ -> false in
      let stripped_ns, shortened = Syntax.DsEnv.shorten_module_path env.dsenv prefix naked_match in
      (str_of_ids shortened, str_of_ids matched, str_of_ids stripped_ns, match_len) in
    let prepare_candidate (prefix, matched, stripped_ns, match_len) =
      if prefix = "" then
        (matched, stripped_ns, match_len)
      else
        (prefix ^ "." ^ matched, stripped_ns, String.length prefix + match_len + 1) in
    let needle = Util.split search_term "." in
    let all_lidents_in_env = FStar.TypeChecker.Env.lidents env in
    let matches =
        //There are two cases here:
        //Either the needle is of the form:
        //   (a) A.x   where A resolves to the module L.M.N
        //or (b) the needle's namespace is not a well-formed module.
        //In case (a), we go to the desugaring to find the names
        //   transitively exported by L.M.N
        //In case (b), we find all lidents in the type-checking environment
        //   and rank them by potential matches to the needle
        let case_a_find_transitive_includes (orig_ns:list<string>) (m:lident) (id:string)
            : list<(list<ident> * list<ident> * int)>
            =
            let exported_names = DsEnv.transitive_exported_ids env.dsenv m in
            let matched_length =
              List.fold_left
                (fun out s -> String.length s + out + 1)
                (String.length id)
                orig_ns
            in
            exported_names |>
            List.filter_map (fun n ->
            if Util.starts_with n id
            then let lid = Ident.lid_of_ns_and_id (Ident.ids_of_lid m) (Ident.id_of_text n) in
                 Option.map (fun fqn -> [], (List.map Ident.id_of_text orig_ns)@[fqn.ident], matched_length)
                            (DsEnv.resolve_to_fully_qualified_name env.dsenv lid)
            else None)
        in
        let case_b_find_matches_in_env ()
          : list<(list<ident> * list<ident> * int)>
          = let matches = List.filter_map (match_lident_against needle) all_lidents_in_env in
            //Retain only the ones that can be resolved that are resolvable to themselves in dsenv
            matches |> List.filter (fun (ns, id, _) ->
              match DsEnv.resolve_to_fully_qualified_name env.dsenv (Ident.lid_of_ids id) with
              | None -> false
              | Some l -> Ident.lid_equals l (Ident.lid_of_ids (ns@id)))
        in
        let ns, id = Util.prefix needle in
        let matched_ids =
            match ns with
            | [] -> case_b_find_matches_in_env ()
            | _ ->
              let l = Ident.lid_of_path ns Range.dummyRange in
              match FStar.Syntax.DsEnv.resolve_module_name env.dsenv l true with
              | None ->
                case_b_find_matches_in_env ()
              | Some m ->
                case_a_find_transitive_includes ns m id
        in
        matched_ids |>
        List.map (fun x -> prepare_candidate (shorten_namespace x))
    in
    List.iter (fun (candidate, ns, match_len) ->
               Util.print3 "%s %s %s \n"
               (Util.string_of_int match_len) ns candidate)
              (Util.sort_with (fun (cd1, ns1, _) (cd2, ns2, _) ->
                               match String.compare cd1 cd2 with
                               | 0 -> String.compare ns1 ns2
                               | n -> n)
                              matches);
    Util.print_string "#done-ok\n";
    go line_col filename stack curmod env ts
  | Pop msg ->
      // This shrinks all internal stacks by 1
      pop env msg;
      let (env, curmod), stack =
        match stack with
        | [] -> Errors. log_issue Range.dummyRange (Errors.Error_IDETooManyPops,  "too many pops"); exit 1
        | hd::tl -> hd, tl
      in
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
      let env = push_with_kind env lax restore_cmd_line_options "#push" in
      go (l, c) filename stack curmod env ts

  | Code (text, (ok, fail)) ->
      // This does not grow any of the internal stacks.
      let fail curmod tcenv =
        report_fail();
        Util.print1 "%s\n" fail;
        // The interactive mode will send a pop here
        go line_col filename stack curmod tcenv ts
      in

      let frag = {frag_fname="<input>";
                  frag_text=text;
                  frag_line=fst line_col;
                  frag_col=snd line_col} in
      let res = check_frag env curmod frag in begin
        match res with
        | Some (curmod, env, n_errs) ->
            if n_errs=0 then begin
              Util.print1 "\n%s\n" ok;
              go line_col filename stack curmod env ts
              end
            else fail curmod env
        | _ -> fail curmod env
        end
end

// filename is the name of the file currently edited
let interactive_mode (filename:string): unit =

  if Option.isSome (Options.codegen())
  then Errors. log_issue Range.dummyRange (Errors.Warning_IDEIgnoreCodeGen, "code-generation is not supported in interactive mode, ignoring the codegen flag");

  //type check prims and the dependencies
  let filenames, maybe_intf, dep_graph = deps_of_our_file filename in
  let env = init_env dep_graph in
  let stack, env, ts = tc_deps None [] env filenames [] in
  let initial_range = Range.mk_range filename (Range.mk_pos 1 0) (Range.mk_pos 1 0) in
  let env = FStar.TypeChecker.Env.set_range env initial_range in
  let env =
    match maybe_intf with
    | Some intf ->
        // We found an interface: record its contents in the desugaring environment
        // to be interleaved with the module implementation on-demand
        FStar.Universal.load_interface_decls env intf
    | None ->
        env
  in

  if FStar.Options.record_hints() //and if we're recording or using hints
  || FStar.Options.use_hints()
  then FStar.SMTEncoding.Solver.with_hints_db
            (List.hd (Options.file_list ()))
            (fun () -> go (1, 0) filename stack None env ts)
  else go (1, 0) filename stack None env ts
