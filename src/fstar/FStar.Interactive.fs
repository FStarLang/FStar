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
open FStar.Errors

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

let check_frag (dsenv, (env:TcEnv.env)) curmod frag =
  try
    match tc_one_fragment curmod dsenv env frag with
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


(*********************)
(* Dependency checks *)
(*********************)

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
        Util.print_warning (Util.format1 "Unsupported: ended up with %s" (String.concat " " same_name));
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

(***********************************************************************)
(* Reading queries and writing responses *)
(***********************************************************************)

let json_to_str = function
  | JsonNull -> "null"
  | JsonBool b -> Util.format1 "bool (%s)" (if b then "true" else "false")
  | JsonInt i -> Util.format1 "int (%s)" (Util.string_of_int i)
  | JsonStr s -> Util.format1 "string (%s)" s
  | JsonList _ -> "list (...)"
  | JsonAssoc _ -> "dictionary (...)"

exception UnexpectedJsonType of string * json

let js_fail expected got =
  raise (UnexpectedJsonType (expected, got))

let js_int = function
  | JsonInt i -> i
  | other -> js_fail "int" other
let js_str = function
  | JsonStr s -> s
  | other -> js_fail "string" other
let js_list = function
  | JsonList l -> l
  | other -> js_fail "list" other
let js_assoc = function
  | JsonAssoc a -> a
  | other -> js_fail "dictionary" other

type push_kind = | PushLax | PushFull

let js_pushkind s : push_kind = match js_str s with
  | "lax" -> PushLax
  | "full" -> PushFull
  | _ -> js_fail "push_kind" s

type query' =
| Exit
| DescribeProtocol
| Pop
| Push of push_kind * string * int * int
| AutoComplete of string
| Lookup of string * option<(string * int * int)> * list<string>
| ProtocolViolation of string
and query = { qq: query'; qid: string }

let interactive_protocol_vernum = 1

let interactive_protocol_features =
  ["autocomplete"; "describe-protocol"; "exit";
   "lookup"; "lookup/documentation"; "pop"; "push"]

exception InvalidQuery of string
type query_status = | QueryOK | QueryNOK | QueryViolatesProtocol

let try_assoc key a =
  Util.map_option snd (Util.try_find (fun (k, _) -> k = key) a)

let unpack_interactive_query json =
  let assoc errloc key a =
    match try_assoc key a with
    | Some v -> v
    | None -> raise (InvalidQuery (Util.format2 "Missing key [%s] in %s." key errloc)) in

  let request = json |> js_assoc in

  let qid = assoc "query" "query-id" request |> js_str in
  let query = assoc "query" "query" request |> js_str in
  let args = assoc "query" "args" request |> js_assoc in

  let arg k = assoc "[args]" k args in
  let try_arg k = try_assoc k args in

  { qid = qid;
    qq = match query with
         | "exit" -> Exit
         | "pop" -> Pop
         | "describe-protocol" -> DescribeProtocol
         | "push" -> Push (arg "kind" |> js_pushkind,
                          arg "code" |> js_str,
                          arg "line" |> js_int,
                          arg "column" |> js_int)
         | "autocomplete" -> AutoComplete (arg "partial-symbol" |> js_str)
         | "lookup" -> Lookup (arg "symbol" |> js_str,
                              try_arg "location"
                                |> Util.map_option js_assoc
                                |> Util.map_option (fun loc ->
                                    (assoc "[location]" "filename" loc |> js_str,
                                     assoc "[location]" "line" loc |> js_int,
                                     assoc "[location]" "column" loc |> js_int)),
                              List.map js_str (arg "requested-info" |> js_list))
         | _ -> ProtocolViolation (Util.format1 "Unknown query '%s'" query) }

let read_interactive_query stream : query =
  try
    match Util.read_line stream with
    | None -> exit 0
    | Some line ->
      match Util.json_of_string line with
      | None -> { qid = "?"; qq = ProtocolViolation "Json parsing failed." }
      | Some request -> unpack_interactive_query request
  with
  | InvalidQuery msg -> { qid = "?"; qq = ProtocolViolation msg }
  | UnexpectedJsonType (expected, got) ->
    { qid = "?";
      qq = ProtocolViolation (Util.format2 "JSON decoding failed: expected %s, got %s"
                              expected (json_to_str got)) }

let json_of_opt json_of_a opt_a =
  Util.dflt JsonNull (Util.map_option json_of_a opt_a)

let json_of_pos pos =
  JsonList [JsonInt (Range.line_of_pos pos); JsonInt (Range.col_of_pos pos)]

let json_of_range r =
  JsonAssoc [("fname", JsonStr (Range.file_of_range r));
             ("beg", json_of_pos (Range.start_of_range r));
             ("end", json_of_pos (Range.end_of_range r))]

let json_of_issue_level i =
  JsonStr (match i with
           | ENotImplemented -> "not-implemented"
           | EInfo -> "info"
           | EWarning -> "warning"
           | EError -> "error")

let json_of_issue issue =
  JsonAssoc [("level", json_of_issue_level issue.issue_level);
             ("message", JsonStr issue.issue_message);
             ("ranges", JsonList (match issue.issue_range with
                                  | None -> []
                                  | Some r -> [json_of_range r]))]

type lookup_result = { lr_name: string;
                       lr_def_range: option<Range.range>;
                       lr_typ: option<string>;
                       lr_doc: option<string> }

let json_of_lookup_result lr =
  JsonAssoc [("name", JsonStr lr.lr_name);
             ("defined-at", json_of_opt json_of_range lr.lr_def_range);
             ("type", json_of_opt JsonStr lr.lr_typ);
             ("documentation", json_of_opt JsonStr lr.lr_doc)]

let json_of_protocol_info =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList <| List.map JsonStr interactive_protocol_features in
  [("version", js_version); ("features", js_features)]

let write_json json =
  Util.print_raw (Util.string_of_json json);
  Util.print_raw "\n"

let write_response qid status response =
  let qid = JsonStr qid in
  let status = match status with
               | QueryOK -> JsonStr "success"
               | QueryNOK -> JsonStr "failure"
               | QueryViolatesProtocol -> JsonStr "protocol-violation" in
  write_json (JsonAssoc [("kind", JsonStr "response");
                         ("query-id", qid);
                         ("status", status);
                         ("response", response)])

let write_message level contents =
  write_json (JsonAssoc [("kind", JsonStr "message");
                         ("level", JsonStr level);
                         ("contents", JsonStr contents)])

let write_hello () =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList (List.map JsonStr interactive_protocol_features) in
  write_json (JsonAssoc (("kind", JsonStr "protocol-info") :: json_of_protocol_info))

(******************************************************************************************)
(* The main interactive loop *)
(******************************************************************************************)
open FStar.Parser.ParseIt

type repl_state = { repl_line: int; repl_column: int; repl_fname: string;
                    repl_stack: stack_t; repl_curmod: modul_t;
                    repl_env: env_t; repl_ts: m_timestamps;
                    repl_stdin: stream_reader }

let run_exit st =
  ((QueryOK, JsonNull), Inr 0)

let run_describe_protocol st =
  ((QueryOK, JsonAssoc json_of_protocol_info), Inl st)

let run_protocol_violation st message =
  ((QueryViolatesProtocol, JsonStr message), Inl st)

let run_pop st = // This shrinks all internal stacks by 1
  match st.repl_stack with
  | [] -> // FIXME this isn't strict enough: the initial dependency checks create
         // multiple entries in the stack (so an error should be raised when
         // length <= length_after_deps_check, not when length = 0.
    ((QueryNOK, JsonStr "Too many pops"), Inl st)

  | (env, curmod) :: stack ->
    pop st.repl_env "#pop";

    // Clean up if all the fragments from the current buffer have been popped
    if List.length stack = List.length st.repl_ts then cleanup env;

    ((QueryOK, JsonNull),
      Inl ({ st with repl_env = env; repl_curmod = curmod; repl_stack = stack }))

let run_push st kind text line column = // This grows all internal stacks by 1
  let stack, env, ts = st.repl_stack, st.repl_env, st.repl_ts in

  // If we are at a stage where we have not yet pushed a fragment from the
  // current buffer, see if some dependency is stale. If so, update it. Also
  // if this is the first chunk, we need to restore the command line options.
  let restore_cmd_line_options, (stack, env, ts) =
    if List.length stack = List.length ts
    then true, update_deps st.repl_fname st.repl_curmod stack env ts
    else false, (stack, env, ts) in

  let stack = (env, st.repl_curmod) :: stack in
  let env = push env (kind = PushLax) restore_cmd_line_options "#push" in

  // This pushes to an internal, hidden stack
  let env_mark = mark env in

  let frag = { frag_text = text; frag_line = line; frag_col = column } in
  let res = check_frag env_mark st.repl_curmod (frag, false) in

  let errors = FStar.Errors.report_all() |> List.map json_of_issue in
  FStar.Errors.clear ();

  let st' = { st with repl_stack = stack; repl_ts = ts;
                      repl_line = line; repl_column = column } in

  match res with
  | Some (curmod, env, nerrs) when nerrs = 0 ->
    // At this stage, the internal stack has grown with size 1.
    let env = commit_mark env in
    ((QueryOK, JsonList errors),
      Inl ({ st' with repl_curmod = curmod; repl_env = env }))
  | _ ->
    // The previous version of the protocol required the client to send a #pop
    // immediately after failed pushes; this version pops automatically.
    let env = reset_mark env_mark in
    let _, st'' = run_pop ({ st' with repl_env = env }) in
    ((QueryNOK, JsonList errors), st'')

let run_lookup st symbol pos_opt requested_info =
  let dsenv, tcenv = st.repl_env in

  let info_of_lid_str lid_str =
    let lid = Ident.lid_of_ids (List.map Ident.id_of_text (Util.split lid_str ".")) in
    let lid = Util.dflt lid <| DsEnv.resolve_to_fully_qualified_name dsenv lid in
    try_lookup_lid tcenv lid |> Util.map_option (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  let docs_of_lid lid =
    DsEnv.try_lookup_doc dsenv lid |> Util.map_option fst in

  let info_at_pos_opt =
    Util.bind_opt pos_opt (fun (file, row, col) ->
      FStar.TypeChecker.Err.info_at_pos tcenv file row col) in

  let info_opt =
    match info_at_pos_opt with
    | Some _ -> info_at_pos_opt
    | None -> if symbol = "" then None else info_of_lid_str symbol in

  let response = match info_opt with
    | None -> (QueryNOK, JsonNull)
    | Some (name_or_lid, typ, rng) ->
      let name =
        match name_or_lid with
        | Inl name -> name
        | Inr lid -> Ident.string_of_lid lid in
      let typ_str =
        if List.mem "type" requested_info then
          Some (FStar.TypeChecker.Normalize.term_to_string tcenv typ)
        else None in
      let doc_str =
        match name_or_lid with
        | Inr lid when List.mem "documentation" requested_info -> docs_of_lid lid
        | _ -> None in
      let def_range =
        if List.mem "defined-at" requested_info then Some rng else None in

      let result = { lr_name = name; lr_def_range = def_range;
                     lr_typ = typ_str; lr_doc = doc_str } in
      (QueryOK, json_of_lookup_result result) in

  (response, Inl st)

let run_completions st search_term =
  let dsenv, tcenv = st.repl_env in
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
    let stripped_ns, shortened = ToSyntax.Env.shorten_module_path dsenv prefix naked_match in
    (str_of_ids shortened, str_of_ids matched, str_of_ids stripped_ns, match_len) in
  let prepare_candidate (prefix, matched, stripped_ns, match_len) =
    if prefix = "" then
      (matched, stripped_ns, match_len)
    else
      (prefix ^ "." ^ matched, stripped_ns, String.length prefix + match_len + 1) in
  let needle = Util.split search_term "." in
  let all_lidents_in_env = FStar.TypeChecker.Env.lidents tcenv in
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
          let exported_names = DsEnv.transitive_exported_ids dsenv m in
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
                          (DsEnv.resolve_to_fully_qualified_name dsenv lid)
          else None)
      in
      let case_b_find_matches_in_env ()
        : list<(list<ident> * list<ident> * int)>
        = let matches = List.filter_map (match_lident_against needle) all_lidents_in_env in
          //Retain only the ones that can be resolved that are resolvable to themselves in dsenv
          matches |> List.filter (fun (ns, id, _) ->
            match DsEnv.resolve_to_fully_qualified_name dsenv (Ident.lid_of_ids id) with
            | None -> false
            | Some l -> Ident.lid_equals l (Ident.lid_of_ids (ns@id)))
      in
      let ns, id = Util.prefix needle in
      let matched_ids =
          match ns with
          | [] -> case_b_find_matches_in_env ()
          | _ ->
            let l = Ident.lid_of_path ns Range.dummyRange in
            match FStar.ToSyntax.Env.resolve_module_name dsenv l true with
            | None ->
              case_b_find_matches_in_env ()
            | Some m ->
              case_a_find_transitive_includes ns m id
      in
      matched_ids |>
      List.map (fun x -> prepare_candidate (shorten_namespace x))
  in
  let json_candidates =
    List.map (fun (candidate, ns, match_len) ->
              JsonList [JsonInt match_len; JsonStr ns; JsonStr candidate])
             (Util.sort_with (fun (cd1, ns1, _) (cd2, ns2, _) ->
                              match String.compare cd1 cd2 with
                              | 0 -> String.compare ns1 ns2
                              | n -> n)
                             matches) in
  ((QueryOK, JsonList json_candidates), Inl st)

let run_query st : query' -> (query_status * json) * either<repl_state,int> = function
  | Exit -> run_exit st
  | DescribeProtocol -> run_describe_protocol st
  | Pop -> run_pop st
  | Push (kind, text, l, c) -> run_push st kind text l c
  | AutoComplete search_term -> run_completions st search_term
  | Lookup (symbol, pos_opt, rqi) -> run_lookup st symbol pos_opt rqi
  | ProtocolViolation query -> run_protocol_violation st query

let rec go st : unit =
  let query = read_interactive_query st.repl_stdin in
  let (status, response), state_opt = run_query st query.qq in
  write_response query.qid status response;
  match state_opt with
  | Inl st' -> go st'
  | Inr exitcode -> exit exitcode

let interactive_error_handler = // No printing here — collect everything for future use
  let issues : ref<list<issue>> = Util.mk_ref [] in
  let add_one (e: issue) = issues := e :: !issues in
  let count_errors () = List.length (List.filter (fun e -> e.issue_level = EError) !issues) in
  let report () = List.sortWith compare_issues !issues in
  let clear () = issues := [] in
  { eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear }

let interactive_printer =
  { printer_prinfo = write_message "info";
    printer_prwarning = write_message "warning";
    printer_prerror = write_message "error" }

// filename is the name of the file currently edited
let interactive_mode' (filename:string): unit =
  write_hello ();
  //type check prims and the dependencies
  let filenames, maybe_intf = deps_of_our_file filename in
  let env = tc_prims () in
  let stack, env, ts = tc_deps None [] env filenames [] in
  let initial_range = Range.mk_range "<input>" (Range.mk_pos 1 0) (Range.mk_pos 1 0) in
  let env = fst env, FStar.TypeChecker.Env.set_range (snd env) initial_range in
  let env =
    match maybe_intf with
    | Some intf ->
        // We found an interface: record its contents in the desugaring environment
        // to be interleaved with the module implementation on-demand
        FStar.Universal.load_interface_decls env intf
    | None ->
        env
  in

  let init_st = { repl_line = 1; repl_column = 0; repl_fname = filename;
                  repl_stack = stack; repl_curmod = None;
                  repl_env = env; repl_ts = ts; repl_stdin = open_stdin () } in

  if FStar.Options.record_hints() || FStar.Options.use_hints() then //and if we're recording or using hints
    FStar.SMTEncoding.Solver.with_hints_db (List.hd (Options.file_list ())) (fun () -> go init_st)
  else
    go init_st

let interactive_mode (filename:string): unit =
  FStar.Util.set_printer interactive_printer;
  FStar.Errors.set_handler interactive_error_handler;

  if Option.isSome (Options.codegen())
  then Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag";

  try
    interactive_mode' filename
  with
  | e -> (// Revert to default handler since we won't have an opportunity to
          // print errors ourselves.
          FStar.Errors.set_handler FStar.Errors.default_handler;
          raise e)
