(*
   Copyright 2008-2020 Microsoft Research

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
module FStarC.Errors

open FStar.Pervasives
open FStar.String
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Range
open FStarC.Options
module List = FStarC.List
module BU = FStarC.Util
module PP = FStarC.Pprint

open FStarC.Class.Monad
open FStarC.Class.Show
open FStarC.Errors.Codes
open FStarC.Errors.Msg
open FStarC.Json

let fallback_range : ref (option range) = BU.mk_ref None

let error_range_bound : ref (option range) = BU.mk_ref None

let with_error_bound (r:range) (f : unit -> 'a) : 'a =
  let old = !error_range_bound in
  error_range_bound := Some r;
  let res = f () in
  error_range_bound := old;
  res

let maybe_bound_range (r : Range.range) : Range.range =
  match !error_range_bound with
  | Some r' -> Range.bound_range r r'
  | None -> r

(** This exception is raised in FStar.Error
    when a warn_error string could not be processed;
    The exception is handled in FStarC.Options as part of
    option parsing. *)
exception Invalid_warn_error_setting of string

let lookup_error settings e =
  match
    BU.try_find (fun (v, _, i) -> e=v) settings
  with
  | Some i -> i
  | None -> failwith "Impossible: unrecognized error"

(** Find a (potentially empty) set of issues whose numbers
    are in the interval [l,h].

    Note: We intentionally do not warn on the use of non-existent
    issue number *)
let lookup_error_range settings (l, h) =
  let matches, _ =
    List.partition (fun (_, _, i) -> l <= i && i <= h) settings
  in
  matches

let error_number (_, _, i) = i
let errno (e:error_code) : int = error_number (lookup_error default_settings e)

(* Exported *)
let warn_on_use_errno    = errno Warning_WarnOnUse
let defensive_errno      = errno Warning_Defensive
let call_to_erased_errno = errno Error_CallToErased

let update_flags (l:list (error_flag & string))
  : list error_setting
  = let set_one_flag i flag default_flag =
      match flag, default_flag with
      | (CWarning, CAlwaysError)
      | (CError, CAlwaysError) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot turn error %s into warning"
                             (BU.string_of_int i)))
      | (CSilent, CAlwaysError) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot silence error %s"
                             (BU.string_of_int i)))
      | (CSilent, CFatal)
      | (CWarning, CFatal)
      | (CError, CFatal) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot change the error level of fatal error %s"
                             (BU.string_of_int i)))
      | (CAlwaysError, CFatal) ->
        CFatal
      | _ -> flag
   in
   let set_flag_for_range (flag, range) =
    let errs = lookup_error_range default_settings range in
    List.map (fun (v, default_flag, i) -> v, set_one_flag i flag default_flag, i) errs
   in
   let compute_range (flag, s) =
     let r = BU.split s ".." in
     let (l,h) =
         match r with
         | [r1; r2] -> (int_of_string r1, int_of_string r2)
         | _ -> raise (Invalid_warn_error_setting
                       (BU.format1 "Malformed warn-error range %s" s))
     in
     flag, (l, h)
  in
  // NOTE: Rev below so when we handle things like '@0..100-50'
  // the -50 overrides the @0..100.
  let error_range_settings = List.map compute_range (List.rev l) in
  List.collect set_flag_for_range error_range_settings
  @ default_settings

exception Error   of error
exception Warning of error
exception Stop
exception Empty_frag

let json_of_issue_level level
  = JsonStr ( match level with
            | ENotImplemented -> "NotImplemented"
            | EInfo           -> "Info"
            | EWarning        -> "Warning"
            | EError          -> "Error")

let json_of_issue issue =
    JsonAssoc [
        "msg",    json_of_error_message issue.issue_msg;
        "level",  json_of_issue_level issue.issue_level;
        "range",  dflt JsonNull (json_of_range <$> issue.issue_range);
        "number", dflt JsonNull (JsonInt <$> issue.issue_number);
        "ctx",    JsonList (JsonStr <$> issue.issue_ctx);
    ]


let ctx_doc (ctx : list string) : PP.document =
  let open FStarC.Pprint in
  if Options.error_contexts ()
  then
    ctx
      |> List.map (fun s -> hardline ^^ doc_of_string "> " ^^ doc_of_string s)
      |> Pprint.concat
  else empty

(* No newline at the end *)
(* Only used externally *)
let issue_message (i:issue) : list PP.document =
  let open FStarC.Pprint in
  i.issue_msg @ [ctx_doc i.issue_ctx]

let string_of_issue_level il =
    match il with
    | EInfo -> "Info"
    | EWarning -> "Warning"
    | EError -> "Error"
    | ENotImplemented -> "Feature not yet implemented: "
let issue_level_of_string =
  function
  | "Info" -> EInfo
  | "Warning" -> EWarning
  | "Error" -> EError
  | _ -> ENotImplemented

let optional_def (f : 'a -> PP.document) (def : PP.document) (o : option 'a) : PP.document =
  match o with
  | Some x -> f x
  | None -> def

let issue_to_doc' (print_hdr:bool) (issue:issue) : PP.document =
  let open FStarC.Pprint in
  let r = issue.issue_range in
  let hdr : document =
    if print_hdr then (
      let level_header = doc_of_string (string_of_issue_level issue.issue_level) in
      let num_opt =
        if issue.issue_level = EError || issue.issue_level = EWarning
        then blank 1 ^^ optional_def (fun n -> doc_of_string (string_of_int n)) (doc_of_string "<unknown>") issue.issue_number
        else empty
      in
      let atrng : document =
        match r with
        | Some r when r <> Range.dummyRange ->
          blank 1 ^^ doc_of_string "at" ^^ blank 1 ^^ doc_of_string (Range.string_of_use_range r)
        | _ ->
          empty
      in
      doc_of_string "*" ^^ blank 1 ^^ level_header ^^ num_opt ^^
        atrng ^^
        doc_of_string ":" ^^ hardline
    ) else empty
  in
  let seealso : document =
    match r with
    | Some r when def_range r <> use_range r && def_range r <> def_range dummyRange ->
      doc_of_string "See also" ^^ blank 1 ^^ doc_of_string (Range.string_of_range r)
    | _ -> empty
  in
  let ctx : document =
    match issue.issue_ctx with
    | h::t when Options.error_contexts () ->
      let d1 s = doc_of_string "> " ^^ doc_of_string s in
      List.fold_left (fun l r -> l ^^ hardline ^^ d1 r) (d1 h) t
    | _ -> empty
  in
  (* We only indent if we are are printing the header. I.e., only ident for batch errors,
  not for VS code diagnostics window. *)
  let subdoc = subdoc' print_hdr in
  let mainmsg : document =
    concat (List.map (fun d -> subdoc (group d)) issue.issue_msg)
  in
  (* This ends in a hardline to get a 1-line spacing between errors *)
  hdr ^^
  mainmsg ^^
  subdoc seealso ^^
  subdoc ctx

let format_issue' (print_hdr:bool) (issue:issue) : string =
  issue_to_doc' print_hdr issue |> renderdoc

let format_issue issue : string = format_issue' true issue

let print_issue_json issue =
    json_of_issue issue |> string_of_json |> BU.print1_error "%s\n"

(*
  Printing for nicer display in github actions runs. See
    https://docs.github.com/en/actions/writing-workflows/choosing-what-your-workflow-does/workflow-commands-for-github-actions
  for more info. The idea here is basically render it as text and then
  add a github header. Also we replace newlines by %0A which become
  newlines in the rendered github annotation, though that does not seem
  to be very well documented (https://github.com/orgs/community/discussions/26736)
*)
let print_issue_github issue =
  match issue.issue_level with
  | ENotImplemented
  | EInfo -> ()
  | EError
  | EWarning ->
    let level = if EError? issue.issue_level then "error" else "warning" in
    let rng = dflt dummyRange issue.issue_range in
    let msg = format_issue' true issue in
    let msg = msg |> BU.splitlines |> String.concat "%0A" in
    let num =
      match issue.issue_number with
      | None -> ""
      | Some n -> BU.format1 "(%s) " (show n)
    in
    BU.print_warning <|
      BU.format6 "::%s file=%s,line=%s,endLine=%s::%s%s\n"
        level
        (Range.file_of_range rng)
        (show (rng |> Range.start_of_range |> Range.line_of_pos))
        (show (rng |> Range.end_of_range   |> Range.line_of_pos))
        num
        msg

let print_issue_rendered issue =
    let printer =
        match issue.issue_level with
        | EInfo -> (fun s -> BU.print_string (colorize_cyan s))
        | EWarning -> BU.print_warning
        | EError -> BU.print_error
        | ENotImplemented -> BU.print_error in
    printer (format_issue issue ^ "\n")

let print_issue issue =
    match FStarC.Options.message_format () with
    | Human -> print_issue_rendered issue
    | Json -> print_issue_json issue
    | Github -> print_issue_github issue

let compare_issues i1 i2 =
    match i1.issue_range, i2.issue_range with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some r1, Some r2 -> FStarC.Range.compare_use_range r1 r2

let dummy_ide_rng : Range.rng =
  mk_rng "<input>" (mk_pos 1 0) (mk_pos 1 0)

(* Attempts to set a decent range (no dummy, no dummy ide) relying
on the fallback_range reference. *)
let fixup_issue_range (rng:option Range.range) : option Range.range =
  let rng =
    match rng with
    | None ->
      (* No range given, just rely on the fallback. NB: the
      fallback could also be set to None if it's too early. *)
      !fallback_range
    | Some range ->
      let use_rng = use_range range in
      let use_rng' =
        if use_rng <> dummy_rng && use_rng <> dummy_ide_rng then
          (* Looks good, use it *)
          use_rng
        else if Some? (!fallback_range) then
          (* Or take the use range from the fallback *)
          use_range (Some?.v (!fallback_range))
        else
          (* Doesn't look good, but no fallback, oh well *)
          use_rng
      in
      Some (set_use_range range use_rng')
  in
  map_opt rng maybe_bound_range

let mk_default_handler print =
    let issues : ref (list issue) = BU.mk_ref [] in
    (* This number may be greater than the amount of 'EErrors'
     * in the list above due to errors that were immediately
     * printed (if debug_any()) *)
    let err_count : ref int = BU.mk_ref 0 in

    let add_one (e: issue) =
        (if e.issue_level = EError then
           err_count := 1 + !err_count);
        begin match e.issue_level with
          | EInfo when print -> print_issue e
          | _ when print && Debug.any () -> print_issue e
          | _ -> issues := e :: !issues
        end;
        if Options.defensive_abort () && e.issue_number = Some defensive_errno then
          failwith "Aborting due to --defensive abort";
        ()
    in
    let count_errors () = !err_count in
    let report () =
        let unique_issues = BU.remove_dups (fun i0 i1 -> i0=i1) !issues in
        let sorted_unique_issues = List.sortWith compare_issues unique_issues in
        if print then List.iter print_issue sorted_unique_issues;
        sorted_unique_issues
    in
    let clear () = issues := []; err_count := 0 in
    { eh_name = "default handler (print=" ^ string_of_bool print ^ ")";
      eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear }

let default_handler = mk_default_handler true

let current_handler =
    BU.mk_ref default_handler

let mk_issue level range msg n ctx = {
  issue_level = level;
  issue_range = range;
  issue_msg = msg;
  issue_number = n;
  issue_ctx = ctx;
}

let get_err_count () = (!current_handler).eh_count_errors ()

let wrapped_eh_add_one (h : error_handler) (issue : issue) : unit =
    (* Try to set a good use range if we got an empty/dummy one *)
    h.eh_add_one issue;
    if issue.issue_level <> EInfo then begin
      Options.abort_counter := !Options.abort_counter - 1;
      if !Options.abort_counter = 0 then
        failwith "Aborting due to --abort_on"
    end

let add_one issue =
    atomically (fun () -> wrapped_eh_add_one (!current_handler) issue)

let add_many issues =
    atomically (fun () -> List.iter (wrapped_eh_add_one (!current_handler)) issues)

let add_issues issues = add_many issues

let report_all () =
    (!current_handler).eh_report ()

let clear () =
    (!current_handler).eh_clear ()

let set_handler handler =
    let issues = report_all () in
    clear (); current_handler := handler; add_many issues

type error_context_t = {
    push  : string -> unit;
    pop   : unit -> string;
    clear : unit -> unit;
    get   : unit -> list string;
    set   : list string -> unit;
}

let error_context : error_context_t =
    let ctxs = BU.mk_ref [] in
    let push s = ctxs := s :: !ctxs in
    let pop s =
        match !ctxs with
        | h::t -> (ctxs := t; h)
        | _ -> failwith "cannot pop error prefix..."
    in
    let clear () = ctxs := [] in
    let get () = !ctxs in
    let set c = ctxs := c in
    { push  = push
    ; pop   = pop
    ; clear = clear
    ; get   = get
    ; set   = set
    }

let get_ctx () : list string =
  error_context.get ()

let maybe_add_backtrace (msg : error_message) : error_message =
  if Options.trace_error () then
    msg @ [backtrace_doc ()]
  else
    msg

let warn_unsafe_options rng_opt msg =
  match Options.report_assumes () with
  | Some "warn" ->
    add_one (mk_issue EWarning rng_opt (mkmsg ("Every use of this option triggers a warning: " ^ msg)) (Some warn_on_use_errno) [])
  | Some "error" ->
    add_one (mk_issue EError rng_opt (mkmsg ("Every use of this option triggers an error: " ^ msg)) (Some warn_on_use_errno) [])
  | _ -> ()

let set_option_warning_callback_range (ropt:option FStarC.Range.range) =
    Options.set_option_warning_callback (warn_unsafe_options ropt)

let t_set_parse_warn_error,
    error_flags =
    (* To parse a warn_error string we expect a callback to be set in FStarC.Main.setup_hooks *)
    let parser_callback : ref (option (string -> list error_setting)) = mk_ref None in
    (* The reporting of errors, particularly errors in the warn_error string itself
       is delicate.
       We keep a map from warn_error strings to their parsed results,
         - Some list error_setting in case it parses and is interpreted successfully
         - None in case it does not parse or is not intepretable
    *)
    let error_flags : BU.smap (option (list error_setting)) = BU.smap_create 10 in
    (* set_error_flags is called by Options.set_options, parse_cmd_line etc,
       upon parsing the options.
       It parses the current warn_error string and sets the result in the
       error_flags map above. In case it fails, it reports an Getopt error
       for Options to report. Options may, in turn, report that error
       back using the functionality of this module, e.g., log_issue *)
    let set_error_flags () =
        let parse (s:string) =
          match !parser_callback with
          | None -> failwith "Callback for parsing warn_error strings is not set"
          | Some f -> f s
        in
        let we = Options.warn_error () in
        try let r = parse we in
            BU.smap_add error_flags we (Some r);
            Getopt.Success
        with Invalid_warn_error_setting msg ->
            (BU.smap_add error_flags we None;
             Getopt.Error ("Invalid --warn_error setting: " ^ msg ^ "\n", "warn_error"))
    in
    (* get_error_flags is called when logging an issue to figure out
       which error level to report a particular issue at (Warning, Error etc.)
       It is important that this function itself never raises an exception:
       raising an error when trying to report an error is bad news, e.g., it
       crashes the ide mode since it causes F* to exit abruptly.
       So, we don't do any parsing here ... just look up the result of a
       prior parse, falling back to the default settings in case the
       parse didn't succeed *)
    let get_error_flags () =
      let we = Options.warn_error () in
      match BU.smap_try_find error_flags we with
      | Some (Some w) -> w
      | _ -> default_settings
    in
    (* Setting the parser callback received from setup_hooks
       and installing, in turn, callbacks in Options for
       parsing warn_error settings and also for warning on the use of
       unsafe options. *)
    let set_callbacks (f:string -> list error_setting) =
        parser_callback := Some f;
        Options.set_error_flags_callback set_error_flags;
        Options.set_option_warning_callback (warn_unsafe_options None)
    in
    set_callbacks, get_error_flags

(* Work around bug *)
let set_parse_warn_error = t_set_parse_warn_error

let lookup err =
  let flags = error_flags () in
  let v, level, i = lookup_error flags err in
  let with_level level = v, level, i in
  match v with
  | Warning_Defensive when Options.defensive_error () || Options.defensive_abort () ->
    with_level CAlwaysError

  | Warning_WarnOnUse ->
    let level' =
      //the level of warn_on_use is the
      //max severity of the report_assumes setting (none, warn, error)
      //and whatever the level is by default (e.g., due to a --warn_error setting)
      match Options.report_assumes () with
      | None -> level
      | Some "warn" ->
        (match level with
         | CSilent -> CWarning
         | _ -> level)
      | Some "error" ->
        (match level with
         | CWarning
         | CSilent -> CError
         | _ -> level)
      | Some _ ->
        level
    in
    with_level level'

  | _ ->
    with_level level

let log_issue_ctx r (e, msg) ctx =
  let msg = maybe_add_backtrace msg in
  let r = fixup_issue_range (Some r) in
  match lookup e with
  | (_, CAlwaysError, errno)
  | (_, CError, errno)  ->
     add_one (mk_issue EError r msg (Some errno) ctx)
  | (_, CWarning, errno) ->
     add_one (mk_issue EWarning r msg (Some errno) ctx)
  | (_, CSilent, _) -> ()
  // We allow using log_issue to report a Fatal error in interactive mode
  | (_, CFatal, errno) ->
    let i = mk_issue EError r msg (Some errno) ctx in
    if Options.ide()
    then add_one i
    else failwith ("don't use log_issue to report fatal error, should use raise_error: " ^ format_issue i)

let info r msg =
  let open FStarC.Class.HasRange in
  let rng = pos r in
  let rng = fixup_issue_range (Some rng) in
  let msg = to_doc_list msg in
  let msg = maybe_add_backtrace msg in
  let ctx = get_ctx () in
  add_one (mk_issue EInfo rng msg None ctx)

let diag r msg =
  if Debug.any() then
    info r msg

let raise_error r e msg =
  let open FStarC.Class.HasRange in
  let rng = pos r in
  let Some rng = fixup_issue_range (Some rng) in
  let msg = to_doc_list msg in
  raise (Error (e, maybe_add_backtrace msg, rng, error_context.get ()))

let log_issue r e msg =
  let open FStarC.Class.HasRange in
  let rng = pos r in
  let msg = to_doc_list msg in
  let ctx = error_context.get () in
  log_issue_ctx rng (e, msg) ctx

let raise_error0 e msg = raise_error dummyRange e msg
let log_issue0 e msg = log_issue dummyRange e msg
let diag0 msg = diag dummyRange msg

let add_errors (errs : list error) : unit =
    atomically (fun () -> List.iter (fun (e, msg, r, ctx) -> log_issue_ctx r (e, msg) ctx) errs)

let issue_of_exn (e:exn) : option issue =
  match e with
  | Error(e, msg, r, ctx) ->
    let errno = error_number (lookup e) in
    let r = fixup_issue_range (Some r) in
    Some (mk_issue EError r msg (Some errno) ctx)
  | _ -> None

let err_exn exn =
    if exn = Stop then ()
    else
    match issue_of_exn exn with
    | Some issue -> add_one issue
    | None -> raise exn

let handleable = function
  | Error _
  | Stop -> true
  | _ -> false

let stop_if_err () =
    if get_err_count () > 0
    then raise Stop

let with_ctx (s:string) (f : unit -> 'a) : 'a =
  error_context.push s;
  let r =
    (* If we're debugging the failure, don't do anything,
     * since catching and rethrowing the exception will change
     * the stack trace. We still push the context though. *)
    if Options.trace_error ()
    then Inr (f ())
    else
    try
      Inr (f ())
    with
      (* Adding context to `failwith`, though it will be printed badly.
       * TODO: deprecate failwith and use F* exceptions, which we can
       * then catch and print sensibly. *)
      | Failure msg ->
        Inl (Failure (msg ^ rendermsg [ctx_doc (error_context.get ())]))
      | ex -> Inl ex
  in
  ignore (error_context.pop ());
  match r with
  | Inr r -> r
  | Inl e -> raise e

let with_ctx_if (b:bool) (s:string) (f : unit -> 'a) : 'a =
  if b then
    with_ctx s f
  else
    f ()

//
// returns errors, other issues, result if any
// restores handler back
//
let catch_errors_aux (f : unit -> 'a) : list issue & list issue & option 'a =
  let newh = mk_default_handler false in
  let old = !current_handler in
  current_handler := newh;
  let finally_restore () =
    let all_issues = newh.eh_report() in //de-duplicated already
    current_handler := old;
    let errs, rest = List.partition (fun i -> i.issue_level = EError) all_issues in
    errs, rest
  in
  let r = try Some (f ())
          with
          | ex when handleable ex ->
            err_exn ex;
            None
          | ex ->
            let _ = finally_restore() in
            raise ex
  in
  let errs, rest = finally_restore() in
  errs, rest, r
 
let no_ctx (f : unit -> 'a) : 'a =
  let save = error_context.get () in
  error_context.clear ();
  let res = f () in
  error_context.set save;
  res

let catch_errors (f : unit -> 'a) : list issue & option 'a =
  let errs, rest, r = catch_errors_aux f in
  List.iter (!current_handler).eh_add_one rest;
  errs, r

//
// Similar to catch_errors, except the warnings are not added to the old handler
//
let catch_errors_and_ignore_rest (f:unit -> 'a) : list issue & option 'a =
  let errs, rest, r = catch_errors_aux f in
  List.iter (!current_handler).eh_add_one <| List.filter (fun i -> i.issue_level = EInfo) rest;
  (* ^ We print diagnostics anyway, which are usually debugging messages to be rendered
  in the editor. *)
  errs, r

(* Finds a discrepancy between two multisets of ints. Result is (elem, amount1, amount2)
 * eg. find_multiset_discrepancy [1;1;3;5] [1;1;3;3;4;5] = Some (3, 1, 2)
 *     since 3 appears 1 time in l1, but 2 times in l2. *)
let find_multiset_discrepancy (l1 : list int) (l2 : list int) : option (int & int & int) =
    let sort = List.sortWith (fun x y -> x - y) in
    let rec collect (l : list 'a) : list ('a & int) =
        match l with
        | [] -> []
        | hd :: tl ->
            begin match collect tl with
            | [] -> [(hd, 1)]
            | (h, n) :: t ->
                if h = hd
                then (h, n+1) :: t
                else (hd, 1) :: (h, n) :: t
            end
    in
    let l1 = collect (sort l1) in
    let l2 = collect (sort l2) in
    let rec aux l1 l2 =
        match l1, l2 with
        | [], [] -> None

        | (e, n) :: _, [] ->
            Some (e, n, 0)

        | [], (e, n) :: _ ->
            Some (e, 0, n)

        | (hd1, n1) :: tl1, (hd2, n2) :: tl2 ->
            if hd1 < hd2 then
                Some (hd1, n1, 0)
            else if hd1 > hd2 then
                Some (hd2, 0, n2)
            else if n1 <> n2 then
                Some (hd1, n1, n2)
            else aux tl1 tl2
    in
    aux l1 l2

let raise_error_doc rng code msg = raise_error rng code msg
let log_issue_doc rng code msg = log_issue rng code msg
let raise_error_text rng code msg = raise_error rng code msg
let log_issue_text rng code msg = log_issue rng code msg
