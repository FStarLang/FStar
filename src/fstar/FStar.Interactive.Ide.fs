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
module FStar.Interactive.Ide
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Range
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Errors

open FStar.Universal
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Interactive

module SS = FStar.Syntax.Syntax
module DsEnv = FStar.ToSyntax.Env
module TcEnv = FStar.TypeChecker.Env

// A custom version of the function that's in FStar.Universal.fs just for the
// sake of the interactive mode
let tc_one_file (remaining:list<string>) (uenv:uenv) = //:((string option * string) * uenv * modul option * string list) =
  let dsenv, env = uenv in
  let (intf, impl), dsenv, env, remaining =
    match remaining with
    | intf :: impl :: remaining when needs_interleaving intf impl ->
      let _, dsenv, env = tc_one_file dsenv env (Some intf) impl in
      (Some intf, impl), dsenv, env, remaining
    | intf_or_impl :: remaining ->
      let _, dsenv, env = tc_one_file dsenv env None intf_or_impl in
      (None, intf_or_impl), dsenv, env, remaining
    | [] -> failwith "Impossible"
  in
  (intf, impl), (dsenv, env), remaining

// Ibid.
let tc_prims env = //:uenv =
  let _, dsenv, env = tc_prims env in
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
// pop).

let push env msg =
  let res = push_context env msg in
  Options.push();
  res

let pop env msg =
  pop_context (snd env) msg;
  Options.pop()

type push_kind = | SyntaxCheck | LaxCheck | FullCheck

let push_with_kind ((dsenv: DsEnv.env), tcenv) kind restore_cmd_line_options msg =
  let tcenv = { tcenv with lax = (kind = LaxCheck) } in
  let dsenv = DsEnv.set_syntax_only dsenv (kind = SyntaxCheck) in
  let res = push (dsenv, tcenv) msg in
  if restore_cmd_line_options then Options.restore_cmd_line_options false |> ignore;
  res

let cleanup (dsenv, env) = TcEnv.cleanup_interactive env

let check_frag (dsenv, (env:TcEnv.env)) curmod frag =
  try
    match tc_one_fragment curmod dsenv env frag with
    | Some (m, dsenv, env) ->
      Some (m, (dsenv, env), FStar.Errors.get_err_count())
    | _ -> None
  with
  | Failure (msg) when not (Options.trace_error ()) ->
    let msg = "ASSERTION FAILURE: " ^ msg ^ "\n" ^
              "F* may be in an inconsistent state.\n" ^
              "Please file a bug report, ideally with a " ^
              "minimized version of the program that triggered the error." in
    FStar.TypeChecker.Err.add_errors env [(msg, TcEnv.get_range env)];
    // Make sure the user sees the error, even if it happened transiently while
    // running an automatic syntax checker like FlyCheck.
    Util.print_error msg;
    None

  | FStar.Errors.Error(msg, r) when not (Options.trace_error ()) ->
    FStar.TypeChecker.Err.add_errors env [(msg, r)];
    None

  | FStar.Errors.Err msg when not (Options.trace_error ()) ->
    FStar.TypeChecker.Err.add_errors env [(msg, TcEnv.get_range env)];
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
      let env = push_with_kind env (if Options.lax () then LaxCheck else FullCheck) true "typecheck_modul" in
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
let js_list k = function
  | JsonList l -> List.map k l
  | other -> js_fail "list" other
let js_assoc = function
  | JsonAssoc a -> a
  | other -> js_fail "dictionary" other

let js_pushkind s : push_kind = match js_str s with
  | "syntax" -> SyntaxCheck
  | "lax" -> LaxCheck
  | "full" -> FullCheck
  | _ -> js_fail "push_kind" s

let js_reductionrule s = match js_str s with
  | "beta" -> FStar.TypeChecker.Normalize.Beta
  | "delta" -> FStar.TypeChecker.Normalize.UnfoldUntil SS.Delta_constant
  | "iota" -> FStar.TypeChecker.Normalize.Iota
  | "zeta" -> FStar.TypeChecker.Normalize.Zeta
  | "reify" -> FStar.TypeChecker.Normalize.Reify
  | "pure-subterms" -> FStar.TypeChecker.Normalize.PureSubtermsWithinComputations
  | _ -> js_fail "reduction rule" s

type completion_context =
| CKCode
| CKOption of bool (* #set-options (false) or #reset-options (true) *)
| CKModuleOrNamespace of bool (* modules *) * bool (* namespaces *)

let js_optional_completion_context k =
  match k with
  | None -> CKCode
  | Some k ->
    match js_str k with
    | "symbol" // Backwards compatibility
    | "code" -> CKCode
    | "set-options" -> CKOption false
    | "reset-options" -> CKOption true
    | "open"
    | "let-open" -> CKModuleOrNamespace (true, true)
    | "include"
    | "module-alias" -> CKModuleOrNamespace (true, false)
    | _ ->
      js_fail "completion context (code, set-options, reset-options, \
open, let-open, include, module-alias)" k
open, let-open, include, module-alias)" k

type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Pop
| Push of push_kind * string * int * int * bool
| AutoComplete of string * completion_context
| Lookup of string * option<(string * int * int)> * list<string>
| Compute of string * option<list<FStar.TypeChecker.Normalize.step>>
| Search of string
| MissingCurrentModule
| ProtocolViolation of string
and query = { qq: query'; qid: string }

let query_needs_current_module = function
  | Exit | DescribeProtocol | DescribeRepl | Pop
  | Push _ | MissingCurrentModule | ProtocolViolation _ -> false
  | AutoComplete _ | Lookup _ | Compute _ | Search _ -> true

let interactive_protocol_vernum = 2

let interactive_protocol_features =
  ["autocomplete";
   "compute"; "compute/reify"; "compute/pure-subterms";
   "describe-protocol"; "describe-repl"; "exit";
   "lookup"; "lookup/documentation"; "lookup/definition";
   "peek"; "pop"; "push"; "search"]

exception InvalidQuery of string
type query_status = | QueryOK | QueryNOK | QueryViolatesProtocol

let try_assoc key a =
  Util.map_option snd (Util.try_find (fun (k, _) -> k = key) a)

let wrap_js_failure qid expected got =
  { qid = qid;
    qq = ProtocolViolation (Util.format2 "JSON decoding failed: expected %s, got %s"
                            expected (json_to_str got)) }

let unpack_interactive_query json =
  let assoc errloc key a =
    match try_assoc key a with
    | Some v -> v
    | None -> raise (InvalidQuery (Util.format2 "Missing key [%s] in %s." key errloc)) in

  let request = json |> js_assoc in

  let qid = assoc "query" "query-id" request |> js_str in
  try
    let query = assoc "query" "query" request |> js_str in
    let args = assoc "query" "args" request |> js_assoc in

    let arg k = assoc "[args]" k args in
    let try_arg k =
      match try_assoc k args with
      | Some JsonNull -> None
      | other -> other in

    { qid = qid;
      qq = match query with
           | "exit" -> Exit
           | "pop" -> Pop
           | "describe-protocol" -> DescribeProtocol
           | "describe-repl" -> DescribeRepl
           | "peek" | "push" -> Push (arg "kind" |> js_pushkind,
                                     arg "code" |> js_str,
                                     arg "line" |> js_int,
                                     arg "column" |> js_int,
                                     query = "peek")
           | "autocomplete" -> AutoComplete (arg "partial-symbol" |> js_str,
                                            try_arg "context" |> js_optional_completion_context)
           | "lookup" -> Lookup (arg "symbol" |> js_str,
                                try_arg "location"
                                  |> Util.map_option js_assoc
                                  |> Util.map_option (fun loc ->
                                      (assoc "[location]" "filename" loc |> js_str,
                                       assoc "[location]" "line" loc |> js_int,
                                       assoc "[location]" "column" loc |> js_int)),
                                arg "requested-info" |> js_list js_str)
           | "compute" -> Compute (arg "term" |> js_str,
                                  try_arg "rules"
                                    |> Util.map_option (js_list js_reductionrule))
           | "search" -> Search (arg "terms" |> js_str)
           | _ -> ProtocolViolation (Util.format1 "Unknown query '%s'" query) }
  with
  | InvalidQuery msg -> { qid = qid; qq = ProtocolViolation msg }
  | UnexpectedJsonType (expected, got) -> wrap_js_failure qid expected got

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
  | UnexpectedJsonType (expected, got) -> wrap_js_failure "?" expected got

let rec json_of_fstar_option_value = function
  | Options.Bool b -> JsonBool b
  | Options.String s
  | Options.Path s -> JsonStr s
  | Options.Int n -> JsonInt n
  | Options.List vs -> JsonList (List.map json_of_fstar_option_value vs)
  | Options.Unset -> JsonNull

let json_of_opt json_of_a opt_a =
  Util.dflt JsonNull (Util.map_option json_of_a opt_a)

let json_of_pos pos =
  JsonList [JsonInt (Range.line_of_pos pos); JsonInt (Range.col_of_pos pos)]

let json_of_range_fields file b e =
  JsonAssoc [("fname", JsonStr file);
             ("beg", json_of_pos b);
             ("end", json_of_pos e)]

let json_of_use_range r =
    json_of_range_fields
            (Range.file_of_use_range r)
            (Range.start_of_use_range r)
            (Range.end_of_use_range r)

let json_of_def_range r =
    json_of_range_fields
            (Range.file_of_range r)
            (Range.start_of_range r)
            (Range.end_of_range r)

let json_of_issue_level i =
  JsonStr (match i with
           | ENotImplemented -> "not-implemented"
           | EInfo -> "info"
           | EWarning -> "warning"
           | EError -> "error")

let json_of_issue issue =
  JsonAssoc [("level", json_of_issue_level issue.issue_level);
             ("message", JsonStr issue.issue_message);
             ("ranges", JsonList
                          ((match issue.issue_range with
                            | None -> []
                            | Some r -> [json_of_use_range r]) @
                           (match issue.issue_range with
                            | Some r when r.def_range <> r.use_range ->
                              [json_of_def_range r]
                            | _ -> [])))]

type lookup_result = { lr_name: string;
                       lr_def_range: option<Range.range>;
                       lr_typ: option<string>;
                       lr_doc: option<string>;
                       lr_def: option<string> }

let json_of_lookup_result lr =
  JsonAssoc [("name", JsonStr lr.lr_name);
             ("defined-at", json_of_opt json_of_def_range lr.lr_def_range);
             ("type", json_of_opt JsonStr lr.lr_typ);
             ("documentation", json_of_opt JsonStr lr.lr_doc);
             ("definition", json_of_opt JsonStr lr.lr_def)]

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
                         ("contents", contents)])

let write_hello () =
  let js_version = JsonInt interactive_protocol_vernum in
  let js_features = JsonList (List.map JsonStr interactive_protocol_features) in
  write_json (JsonAssoc (("kind", JsonStr "protocol-info") :: json_of_protocol_info))

(******************************************************************************************)
(* The main interactive loop *)
(******************************************************************************************)
open FStar.Parser.ParseIt

// FIXME: Store repl_names in the stack, too
type repl_state = { repl_line: int; repl_column: int; repl_fname: string;
                    repl_stack: stack_t; repl_curmod: modul_t;
                    repl_env: env_t; repl_ts: m_timestamps;
                    repl_stdin: stream_reader; repl_names: CompletionTable.table }

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly

let string_of_option_permission_level = function
  | OptSet -> "#set-options"
  | OptReset -> "#reset-options"
  | OptReadOnly -> "--read-only--"

type fstar_option =
  { opt_name: string;
    opt_value: Options.option_val;
    opt_default: Options.option_val;
    opt_type: Options.opt_type;
    opt_snippets: list<string>;
    opt_documentation: option<string>;
    opt_permission_level: fstar_option_permission_level }

let rec kind_of_fstar_option_type = function
  | Options.Const _ -> "flag"
  | Options.IntStr _ -> "int"
  | Options.BoolStr -> "bool"
  | Options.PathStr _ -> "path"
  | Options.SimpleStr _ -> "string"
  | Options.EnumStr _ -> "enum"
  | Options.OpenEnumStr _ -> "open enum"
  | Options.PostProcessed (_, typ)
  | Options.Accumulated typ
  | Options.ReverseAccumulated typ
  | Options.WithSideEffect (_, typ) -> kind_of_fstar_option_type typ

let rec snippets_of_fstar_option name typ =
  let mk_field field_name =
    "${" ^ field_name ^ "}" in
  let mk_snippet name argstring =
    "--" ^ name ^ (if argstring <> "" then " " ^ argstring else "") in
  let rec arg_snippets_of_type typ =
    match typ with
    | Options.Const _ -> [""]
    | Options.BoolStr -> ["true"; "false"]
    | Options.IntStr desc
    | Options.PathStr desc
    | Options.SimpleStr desc -> [mk_field desc]
    | Options.EnumStr strs -> strs
    | Options.OpenEnumStr (strs, desc) -> strs @ [mk_field desc]
    | Options.PostProcessed (_, elem_spec)
    | Options.Accumulated elem_spec
    | Options.ReverseAccumulated elem_spec
    | Options.WithSideEffect (_, elem_spec) -> arg_snippets_of_type elem_spec in
  List.map (mk_snippet name) (arg_snippets_of_type typ)

let json_of_fstar_option opt =
  JsonAssoc [("name", JsonStr opt.opt_name);
             ("value", json_of_fstar_option_value opt.opt_value);
             ("default", json_of_fstar_option_value opt.opt_default);
             ("documentation", json_of_opt JsonStr opt.opt_documentation);
             ("type", JsonStr (kind_of_fstar_option_type opt.opt_type));
             ("permission-level", JsonStr (string_of_option_permission_level opt.opt_permission_level))]

let fstar_options_static_cache =
  let defaults = Util.smap_of_list Options.defaults in
  Options.all_specs_with_types
  |> List.filter_map (fun (_shortname, name, typ, doc) ->
       Util.smap_try_find defaults name // Keep only options with a default value
       |> Util.map_option (fun default_value ->
             { opt_name = name;
               opt_value = Options.Unset;
               opt_default = default_value;
               opt_type = typ;
               opt_snippets = snippets_of_fstar_option name typ;
               opt_documentation = if doc = "" then None else Some doc;
               opt_permission_level = if Options.settable name then OptSet
                                      else if Options.resettable name then OptReset
                                      else OptReadOnly }))
  |> List.sortWith (fun o1 o2 ->
        String.compare (String.lowercase (o1.opt_name))
                       (String.lowercase (o2.opt_name)))

let collect_fstar_options (filter: fstar_option -> bool) =
  let filter_update opt =
    if filter opt then
      Some ({ opt with opt_value = Options.get_option opt.opt_name })
    else
      None in
  List.filter_map filter_update fstar_options_static_cache

let json_of_repl_state st =
  [("loaded-dependencies",
    JsonList (List.map (fun (_, fstname, _, _) -> JsonStr fstname) st.repl_ts));
   ("options",
    JsonList (List.map json_of_fstar_option (collect_fstar_options (fun _ -> true))))]

let with_printed_effect_args k =
  Options.with_saved_options
    (fun () -> Options.set_option "print_effect_args" (Options.Bool true); k ())

let term_to_string tcenv t =
  with_printed_effect_args (fun () -> FStar.TypeChecker.Normalize.term_to_string tcenv t)

let sigelt_to_string se =
  with_printed_effect_args (fun () -> Syntax.Print.sigelt_to_string se)

let run_exit st =
  ((QueryOK, JsonNull), Inr 0)

let run_describe_protocol st =
  ((QueryOK, JsonAssoc json_of_protocol_info), Inl st)

let run_describe_repl st =
  ((QueryOK, JsonAssoc (json_of_repl_state st)), Inl st)

let run_protocol_violation st message =
  ((QueryViolatesProtocol, JsonStr message), Inl st)

let run_missing_current_module st message =
  ((QueryNOK, JsonStr "Current module unset"), Inl st)

let nothing_left_to_pop st =
  (* The initial dependency check creates [n] entries in [st.repl_ts] and [n]
     entries in [st.repl_stack].  Subsequent pushes do not grow [st.repl_ts]
     (only [st.repl_stack]), so [length st.repl_stack <= length st.repl_ts]
     indicates that there's nothing left to pop. *)
  List.length st.repl_stack <= List.length st.repl_ts

let run_pop st = // This shrinks all internal stacks by 1
  if nothing_left_to_pop st then
    ((QueryNOK, JsonStr "Too many pops"), Inl st)
  else
    match st.repl_stack with
    | [] -> failwith "impossible"
    | (env, curmod) :: stack ->
      pop st.repl_env "#pop";
      let st' = { st with repl_env = env; repl_curmod = curmod; repl_stack = stack } in
      // Clean up if all the fragments from the current buffer have been popped
      if nothing_left_to_pop st' then cleanup env;
      ((QueryOK, JsonNull), Inl st')

type name_tracking_event =
| NTAlias of lid (* host *) * ident (* alias *) * lid (* aliased *)
| NTOpen of lid (* host *) * DsEnv.open_module_or_namespace (* opened *)
| NTInclude of lid (* host *) * lid (* included *)
| NTBinding of binding

let query_of_ids (ids: list<ident>) : CompletionTable.query =
  List.map text_of_id ids

let query_of_lid (lid: lident) : CompletionTable.query =
  query_of_ids (lid.ns @ [lid.ident])

let update_names_from_event cur_mod_str table evt =
  let is_cur_mod lid = lid.str = cur_mod_str in
  match evt with
  | NTAlias (host, id, included) ->
    if is_cur_mod host then
      CompletionTable.register_alias
        table (text_of_id id) [] (query_of_lid included)
    else
      table
  | NTOpen (host, (included, kind)) ->
    if is_cur_mod host then
      CompletionTable.register_open
        table (kind = DsEnv.Open_module) [] (query_of_lid included)
    else
      table
  | NTInclude (host, included) ->
    CompletionTable.register_include
      table (if is_cur_mod host then [] else query_of_lid host) (query_of_lid included)
  | NTBinding binding ->
    let lids =
      match binding with
      | Binding_lid (lid, _) -> [lid]
      | Binding_sig (lids, _) -> lids
      | Binding_sig_inst (lids, _, _) -> lids
      | _ -> [] in
    List.fold_left
      (fun tbl lid ->
         let ns_query = if lid.nsstr = cur_mod_str then []
                        else query_of_ids lid.ns in
         CompletionTable.insert
           tbl ns_query (text_of_id lid.ident) (CompletionTable.Lid lid))
      table lids

let commit_name_tracking (cur_mod: modul_t) names name_events =
  let cur_mod_str = match cur_mod with
                    | None -> "" | Some md -> (SS.mod_name md).str in
  let updater = update_names_from_event cur_mod_str in
  List.fold_left updater names name_events

let fresh_name_tracking_hooks () =
  let events = Util.mk_ref [] in
  let push_event evt = events := evt :: !events in
  events,
  { DsEnv.ds_push_module_abbrev_hook =
      (fun dsenv x l -> push_event (NTAlias (DsEnv.current_module dsenv, x, l)));
    DsEnv.ds_push_include_hook =
      (fun dsenv ns -> push_event (NTInclude (DsEnv.current_module dsenv, ns)));
    DsEnv.ds_push_open_hook =
      (fun dsenv op -> push_event (NTOpen (DsEnv.current_module dsenv, op))) },
  { TcEnv.tc_push_in_gamma_hook =
      (fun _ s -> push_event (NTBinding s)) }

let track_name_changes ((dsenv, tcenv): env_t)
    : env_t * (env_t -> env_t * list<name_tracking_event>) =
  let dsenv_old_hooks, tcenv_old_hooks = DsEnv.ds_hooks dsenv, TcEnv.tc_hooks tcenv in
  let events, dsenv_new_hooks, tcenv_new_hooks = fresh_name_tracking_hooks () in
  ((DsEnv.set_ds_hooks dsenv dsenv_new_hooks,
    TcEnv.set_tc_hooks tcenv tcenv_new_hooks),
   (fun (dsenv, tcenv) ->
      (DsEnv.set_ds_hooks dsenv dsenv_old_hooks,
       TcEnv.set_tc_hooks tcenv tcenv_old_hooks),
      List.rev !events))

let run_push st kind text line column peek_only =
  let stack, env, ts = st.repl_stack, st.repl_env, st.repl_ts in

  let env, finish_name_tracking = track_name_changes env in // begin name tracking…

  // If we are at a stage where we have not yet pushed a fragment from the
  // current buffer, see if some dependency is stale. If so, update it. Also
  // if this is the first chunk, we need to restore the command line options.
  let restore_cmd_line_options, (stack, env, ts) =
    if nothing_left_to_pop st
    then true, update_deps st.repl_fname st.repl_curmod stack env ts
    else false, (stack, env, ts) in

  let stack = (env, st.repl_curmod) :: stack in
  let env = push_with_kind env kind restore_cmd_line_options "#push" in

  let frag = { frag_text = text; frag_line = line; frag_col = column } in
  let res = check_frag env st.repl_curmod (frag, false) in

  let errors = FStar.Errors.report_all() |> List.map json_of_issue in
  FStar.Errors.clear ();

  let st' = { st with repl_stack = stack; repl_ts = ts;
                      repl_line = line; repl_column = column } in

  match res with
  | Some (curmod, env, nerrs) when nerrs = 0 && peek_only = false ->
    let env, name_events = finish_name_tracking env in // …end name tracking
    ((QueryOK, JsonList errors),
     Inl ({ st' with repl_curmod = curmod; repl_env = env;
                     repl_names = commit_name_tracking curmod st'.repl_names name_events }))
  | _ ->
    // The previous version of the protocol required the client to send a #pop
    // immediately after failed pushes; this version pops automatically.
    let env, _ = finish_name_tracking env in // …end name tracking
    let _, st'' = run_pop ({ st' with repl_env = env }) in
    let status = if peek_only then QueryOK else QueryNOK in
    ((status, JsonList errors), st'')

let run_lookup st symbol pos_opt requested_info =
  let dsenv, tcenv = st.repl_env in

  let info_of_lid_str lid_str =
    let lid = Ident.lid_of_ids (List.map Ident.id_of_text (Util.split lid_str ".")) in
    let lid = Util.dflt lid <| DsEnv.resolve_to_fully_qualified_name dsenv lid in
    try_lookup_lid tcenv lid |> Util.map_option (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  let docs_of_lid lid =
    DsEnv.try_lookup_doc dsenv lid |> Util.map_option fst in

  let def_of_lid lid =
    Util.bind_opt (TcEnv.lookup_qname tcenv lid) (function
      | (Inr (se, _), _) -> Some (sigelt_to_string se)
      | _ -> None) in

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
          Some (term_to_string tcenv typ)
        else None in
      let doc_str =
        match name_or_lid with
        | Inr lid when List.mem "documentation" requested_info -> docs_of_lid lid
        | _ -> None in
      let def_str =
        match name_or_lid with
        | Inr lid when List.mem "definition" requested_info -> def_of_lid lid
        | _ -> None in
      let def_range =
        if List.mem "defined-at" requested_info then Some rng else None in

      let result = { lr_name = name; lr_def_range = def_range;
                     lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str } in
      (QueryOK, json_of_lookup_result result) in

  (response, Inl st)

let run_autocomplete' st search_term filter =
  let needle = Util.split search_term "." in
  let results = CompletionTable.autocomplete st.repl_names needle filter in
  let json = List.map CompletionTable.json_of_completion_result results in
  ((QueryOK, JsonList json), Inl st)

let run_symbol_autocomplete st search_term =
  let filter path symb = match path, symb with
    | _,   CompletionTable.Module true -> None // Exclude loaded modules
    | [_], CompletionTable.Namespace _ -> None // Exclude (...) at root
    | path_and_symb -> Some path_and_symb in
  run_autocomplete' st search_term filter

let run_module_autocomplete st search_term namespaces modules =
  let dsenv, tcenv = st.repl_env in

  let rec split_last = function
    | [] -> failwith "split_last on empty list"
    | [h] -> h, []
    | h :: t -> let last, butlast = split_last t in last, h :: butlast in

  let mod_filter pred loaded path symb =
    if pred then
      let last_elem, path_but_last = split_last path in
      match CompletionTable.matched_prefix_of_path_elem last_elem with
      | Some _ -> None // Exclude matches that reach the final ‘.’
      | _ -> Some (path_but_last, symb)
    else None in

  let filter path symb =
    match symb with
    | CompletionTable.Lid _ -> None
    | CompletionTable.Module loaded -> mod_filter modules loaded path symb
    | CompletionTable.Namespace loaded -> mod_filter namespaces loaded path symb in

  run_autocomplete' st search_term filter

let candidates_of_fstar_option match_len is_reset opt =
  let may_set, explanation =
    match opt.opt_permission_level with
    | OptSet -> true, ""
    | OptReset -> is_reset, "#reset-only"
    | OptReadOnly -> false, "read-only" in
  let opt_kind =
    kind_of_fstar_option_type opt.opt_type in
  let annot =
    if may_set then opt_kind else "(" ^ explanation ^ " " ^ opt_kind ^ ")" in
  opt.opt_snippets
  |> List.map (fun snippet ->
        { CompletionTable.completion_match_length = match_len;
          CompletionTable.completion_candidate = snippet;
          CompletionTable.completion_annotation = annot })

let run_option_autocomplete st search_term is_reset =
  let opt_prefix = "--" in
  if Util.starts_with search_term opt_prefix then
    let __len = String.length opt_prefix in
    let search_term = Util.substring_from search_term __len in
    let matcher opt = Util.starts_with opt.opt_name search_term in
    let options = collect_fstar_options matcher in

    let match_len = __len + String.length search_term in
    let collect_candidates = candidates_of_fstar_option match_len is_reset in
    let results = List.concatMap collect_candidates options in

    let json = List.map CompletionTable.json_of_completion_result results in
    ((QueryOK, JsonList json), Inl st)
  else
    ((QueryNOK, JsonStr "Options should start with '--'"), Inl st)

let run_autocomplete st search_term context =
  match context with
  | CKCode ->
    run_code_autocomplete st search_term
  | CKOption is_reset ->
    run_option_autocomplete st search_term is_reset
  | CKModuleOrNamespace (modules, namespaces) ->
    run_module_autocomplete st search_term modules namespaces

let run_compute st term rules =
  let run_and_rewind st task =
    let env' = push st.repl_env "#compute" in
    let results = task st in
    pop env' "#compute";
    (results, Inl st) in

  let dummy_let_fragment term =
    let dummy_decl = Util.format1 "let __compute_dummy__ = (%s)" term in
    { frag_text = dummy_decl; frag_line = 0; frag_col = 0 } in

  let normalize_term tcenv rules t =
    FStar.TypeChecker.Normalize.normalize rules tcenv t in

  let find_let_body ses =
    match ses with
    | [{ SS.sigel = SS.Sig_let((_, [{ SS.lbunivs = univs; SS.lbdef = def }]), _) }] ->
      Some (univs, def)
    | _ -> None in

  let parse frag =
    match FStar.Parser.ParseIt.parse (Inr frag) with
    | Inl (Inr decls, _) -> Some decls
    | _ -> None in

  let desugar dsenv decls =
    snd (FStar.ToSyntax.ToSyntax.desugar_decls dsenv decls) in

  let typecheck tcenv decls =
    let ses, _, _ = FStar.TypeChecker.Tc.tc_decls tcenv decls in
    ses in

  let rules =
    (match rules with
     | Some rules -> rules
     | None -> [FStar.TypeChecker.Normalize.Beta;
               FStar.TypeChecker.Normalize.Iota;
               FStar.TypeChecker.Normalize.Zeta;
               FStar.TypeChecker.Normalize.UnfoldUntil SS.Delta_constant])
    @ [FStar.TypeChecker.Normalize.Inlining;
       FStar.TypeChecker.Normalize.Eager_unfolding;
       FStar.TypeChecker.Normalize.Primops] in

  run_and_rewind st (fun st ->
    let dsenv, tcenv = st.repl_env in
    let frag = dummy_let_fragment term in
    match st.repl_curmod with
    | None -> (QueryNOK, JsonStr "Current module unset")
    | _ ->
      match parse frag with
      | None -> (QueryNOK, JsonStr "Could not parse this term")
      | Some decls ->
        let aux () =
          let decls = desugar dsenv decls in
          let ses = typecheck tcenv decls in
          match find_let_body ses with
          | None -> (QueryNOK, JsonStr "Typechecking yielded an unexpected term")
          | Some (univs, def) ->
            let univs, def = Syntax.Subst.open_univ_vars univs def in
            let tcenv = TcEnv.push_univ_vars tcenv univs in
            let normalized = normalize_term tcenv rules def in
            (QueryOK, JsonStr (term_to_string tcenv normalized)) in
        if Options.trace_error () then
          aux ()
        else
          try aux ()
          with | e -> (QueryNOK, (match FStar.Errors.issue_of_exn e with
                                  | Some issue -> JsonStr (FStar.Errors.format_issue issue)
                                  | None -> raise e)))

type search_term' =
| NameContainsStr of string
| TypeContainsLid of lid
and search_term = { st_negate: bool;
                    st_term: search_term' }

let st_cost = function
| NameContainsStr str -> - (String.length str)
| TypeContainsLid lid -> 1

type search_candidate = { sc_lid: lid; sc_typ:
                          ref<option<Syntax.Syntax.typ>>;
                          sc_fvars: ref<option<set<lid>>> }

let sc_of_lid lid = { sc_lid = lid;
                      sc_typ = Util.mk_ref None;
                      sc_fvars = Util.mk_ref None }

let sc_typ tcenv sc = // Memoized version of sc_typ
   match !sc.sc_typ with
   | Some t -> t
   | None -> let typ = match try_lookup_lid tcenv sc.sc_lid with
                       | None -> SS.mk SS.Tm_unknown None Range.dummyRange
                       | Some ((_, typ), _) -> typ in
             sc.sc_typ := Some typ; typ

let sc_fvars tcenv sc = // Memoized version of fc_vars
   match !sc.sc_fvars with
   | Some fv -> fv
   | None -> let fv = Syntax.Free.fvars (sc_typ tcenv sc) in
             sc.sc_fvars := Some fv; fv

let json_of_search_result dsenv tcenv sc =
  let typ_str = term_to_string tcenv (sc_typ tcenv sc) in
  JsonAssoc [("lid", JsonStr (DsEnv.shorten_lid dsenv sc.sc_lid).str);
             ("type", JsonStr typ_str)]

exception InvalidSearch of string

let run_search st search_str =
  let dsenv, tcenv = st.repl_env in
  let empty_fv_set = SS.new_fv_set () in

  let st_matches candidate term =
    let found =
      match term.st_term with
      | NameContainsStr str -> Util.contains candidate.sc_lid.str str
      | TypeContainsLid lid -> set_mem lid (sc_fvars tcenv candidate) in
    found <> term.st_negate in

  let parse search_str =
    let parse_one term =
      let negate = Util.starts_with term "-" in
      let term = if negate then Util.substring_from term 1 else term in
      let beg_quote = Util.starts_with term "\"" in
      let end_quote = Util.ends_with term "\"" in
      let strip_quotes str =
        if String.length str < 2 then
          raise (InvalidSearch "Empty search term")
        else
          Util.substring str 1 (String.length term - 2) in
      let parsed =
        if beg_quote <> end_quote then
          raise (InvalidSearch (Util.format1 "Improperly quoted search term: %s" term))
        else if beg_quote then
          NameContainsStr (strip_quotes term)
        else
          let lid = Ident.lid_of_str term in
          match DsEnv.resolve_to_fully_qualified_name dsenv lid with
          | None -> raise (InvalidSearch (Util.format1 "Unknown identifier: %s" term))
          | Some lid -> TypeContainsLid lid in
      { st_negate = negate; st_term = parsed } in

    let terms = List.map parse_one (Util.split search_str " ") in
    let cmp = fun x y -> st_cost x.st_term - st_cost y.st_term in
    Util.sort_with cmp terms in

  let pprint_one term =
    (if term.st_negate then "-" else "")
    ^ (match term.st_term with
       | NameContainsStr s -> Util.format1 "\"%s\"" s
       | TypeContainsLid l -> Util.format1 "%s" l.str) in

  let results =
    try
      let terms = parse search_str in
      let all_lidents = TcEnv.lidents tcenv in
      let all_candidates = List.map sc_of_lid all_lidents in
      let matches_all candidate = List.for_all (st_matches candidate) terms in
      let cmp r1 r2 = Util.compare r1.sc_lid.str r2.sc_lid.str in
      let results = List.filter matches_all all_candidates in
      let sorted = Util.sort_with cmp results in
      let js = List.map (json_of_search_result dsenv tcenv) sorted in
      match results with
      | [] -> let kwds = Util.concat_l " " (List.map pprint_one terms) in
              raise (InvalidSearch (Util.format1 "No results found for query [%s]" kwds))
      | _ -> (QueryOK, JsonList js)
    with InvalidSearch s -> (QueryNOK, JsonStr s) in
  (results, Inl st)

let run_query st : query' -> (query_status * json) * either<repl_state,int> = function
  | Exit -> run_exit st
  | DescribeProtocol -> run_describe_protocol st
  | DescribeRepl -> run_describe_repl st
  | Pop -> run_pop st
  | Push (kind, text, l, c, peek) -> run_push st kind text l c peek
  | AutoComplete (search_term, context) -> run_autocomplete st search_term context
  | Lookup (symbol, pos_opt, rqi) -> run_lookup st symbol pos_opt rqi
  | Compute (term, rules) -> run_compute st term rules
  | Search term -> run_search st term
  | MissingCurrentModule -> run_missing_current_module st query
  | ProtocolViolation query -> run_protocol_violation st query

let validate_query st (q: query) : query =
  match q.qq with
  | Push (SyntaxCheck, _, _, _, false) ->
    { qid = q.qid; qq = ProtocolViolation "Cannot use 'kind': 'syntax' with 'query': 'push'" }
  | _ -> match st.repl_curmod with
        | None when query_needs_current_module q.qq ->
          { qid = q.qid; qq = MissingCurrentModule }
        | _ -> q

let rec go st : unit =
  let query = validate_query st (read_interactive_query st.repl_stdin) in
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
  { printer_prinfo = (fun s -> write_message "info" (JsonStr s));
    printer_prwarning = (fun s -> write_message "warning" (JsonStr s));
    printer_prerror = (fun s -> write_message "error" (JsonStr s));
    printer_prgeneric = (fun label get_string get_json -> write_message label (get_json ()) )}

open FStar.TypeChecker.Common

let add_module_completions deps table =
  let mods = FStar.Parser.Dep.build_inclusion_candidates_list () in
  let deps_set =
    List.fold_left
      (fun acc dep -> psmap_add acc (Parser.Dep.lowercase_module_name dep) true)
      (psmap_empty ()) deps in
  let loaded modname =
    psmap_find_default deps_set (String.lowercase modname) false in
  List.fold_left (fun table (modname, _path) ->
      let ns_query = Util.split modname "." in
      CompletionTable.register_module_path table (loaded modname) ns_query)
    table mods

// filename is the name of the file currently edited
let interactive_mode' (filename:string): unit =
  write_hello ();

  //type check prims and the dependencies
  let deps, maybe_intf = deps_of_our_file filename in
  let env = init_env () in
  let env, finish_name_tracking = track_name_changes env in // begin name tracking…
  let env = tc_prims env in
  let stack, env, ts = tc_deps None [] env deps [] in
  let initial_range = Range.mk_range "<input>" (Range.mk_pos 1 0) (Range.mk_pos 1 0) in
  let env = fst env, FStar.TypeChecker.Env.set_range (snd env) initial_range in
  let env =
    match maybe_intf with
    | Some intf ->
        // We found an interface: record its contents in the desugaring environment
        // to be interleaved with the module implementation on-demand
        FStar.Universal.load_interface_decls env intf
    | None ->
        env in
  let env, name_events = finish_name_tracking env in // …end name tracking

  TcEnv.toggle_id_info (snd env) true;

  let names = add_module_completions deps CompletionTable.empty in
  let init_st =
    { repl_line = 1; repl_column = 0; repl_fname = filename;
      repl_stack = stack; repl_curmod = None;
      repl_env = env; repl_ts = ts; repl_stdin = open_stdin ();
      repl_names = commit_name_tracking None names name_events } in

  if FStar.Options.record_hints() || FStar.Options.use_hints() then
    FStar.SMTEncoding.Solver.with_hints_db (List.hd (Options.file_list ())) (fun () -> go init_st)
  else
    go init_st

let interactive_mode (filename:string): unit =
  FStar.Util.set_printer interactive_printer;

  if Option.isSome (Options.codegen())
  then Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag";

  if Options.trace_error () then
    // This prevents the error catcher below from swallowing backtraces
    interactive_mode' filename
  else
    try
      FStar.Errors.set_handler interactive_error_handler;
      interactive_mode' filename
    with
    | e -> (// Revert to default handler since we won't have an opportunity to
           // print errors ourselves.
           FStar.Errors.set_handler FStar.Errors.default_handler;
           raise e)
