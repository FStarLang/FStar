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
module FStar.Errors

open FStar.Pervasives
open FStar.String
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Compiler.Util
open FStar.Compiler.Range
open FStar.Options
module List = FStar.Compiler.List
module BU = FStar.Compiler.Util

open FStar.Errors.Codes

(** This exception is raised in FStar.Error
    when a warn_error string could not be processed;
    The exception is handled in FStar.Options as part of
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
let errno (e:raw_error) : int = error_number (lookup_error default_settings e)

(* Exported *)
let warn_on_use_errno    = errno Warning_WarnOnUse
let defensive_errno      = errno Warning_Defensive
let call_to_erased_errno = errno Error_CallToErased

let update_flags (l:list (error_flag * string))
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
      | (_, CFatal) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot change the error level of fatal error %s"
                             (BU.string_of_int i)))
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
  let error_range_settings = List.map compute_range l in
  List.collect set_flag_for_range error_range_settings
  @ default_settings

exception Error   of error
exception Err     of raw_error * string * list string
exception Warning of error
exception Stop
exception Empty_frag

let ctx_string (ctx : list string) : string =
  if Options.error_contexts ()
  then
    ctx
      |> List.map (fun s -> "\n> " ^ s)
      |> String.concat ""
  else ""

(* No newline at the end *)
let issue_message (i:issue) : string =
  i.issue_msg ^ ctx_string i.issue_ctx

(* No newline at the end *)
let format_issue issue =
  let level_header =
      match issue.issue_level with
      | EInfo -> "Info"
      | EWarning -> "Warning"
      | EError -> "Error"
      | ENotImplemented -> "Feature not yet implemented: "
  in
  let range_str, see_also_str =
      match issue.issue_range with
      | None -> "", ""
      | Some r when r = dummyRange ->
          "", (if def_range r = def_range dummyRange then ""
               else BU.format1 " (see also %s)" (FStar.Compiler.Range.string_of_range r))
      | Some r ->
        (BU.format1 "%s: " (FStar.Compiler.Range.string_of_use_range r),
         (if use_range r = def_range r || def_range r = def_range dummyRange
          then ""
          else BU.format1 " (see also %s)" (FStar.Compiler.Range.string_of_range r)))
  in
  let issue_number =
      match issue.issue_number with
      | None -> ""
      | Some n -> BU.format1 " %s" (string_of_int n)
  in
  BU.format5 "%s(%s%s) %s%s" range_str level_header issue_number (issue_message issue) see_also_str

let print_issue issue =
    let printer =
        match issue.issue_level with
        | EInfo -> BU.print_string
        | EWarning -> BU.print_warning
        | EError -> BU.print_error
        | ENotImplemented -> BU.print_error in
    printer (format_issue issue ^ "\n")

let compare_issues i1 i2 =
    match i1.issue_range, i2.issue_range with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some r1, Some r2 -> FStar.Compiler.Range.compare_use_range r1 r2

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
          | EInfo -> print_issue e
          | _ when print && Options.debug_any () -> print_issue e
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
    { eh_add_one = add_one;
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

let diag r msg =
  if Options.debug_any()
  then add_one (mk_issue EInfo (Some r) msg None [])

let warn_unsafe_options rng_opt msg =
  match Options.report_assumes () with
  | Some "warn" ->
    add_one (mk_issue EWarning rng_opt ("Every use of this option triggers a warning: " ^msg) (Some warn_on_use_errno) [])
  | Some "error" ->
    add_one (mk_issue EError rng_opt ("Every use of this option triggers an error: " ^msg) (Some warn_on_use_errno) [])
  | _ -> ()

let set_option_warning_callback_range (ropt:option FStar.Compiler.Range.range) =
    Options.set_option_warning_callback (warn_unsafe_options ropt)

let t_set_parse_warn_error,
    error_flags =
    (* To parse a warn_error string we expect a callback to be set in FStar.Main.setup_hooks *)
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
             Getopt.Error ("Invalid --warn_error setting: " ^ msg ^ "\n"))
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
  match lookup e with
  | (_, CAlwaysError, errno)
  | (_, CError, errno)  ->
     add_one (mk_issue EError (Some r) msg (Some errno) ctx)
  | (_, CWarning, errno) ->
     add_one (mk_issue EWarning (Some r) msg (Some errno) ctx)
  | (_, CSilent, _) -> ()
  // We allow using log_issue to report a Fatal error in interactive mode
  | (_, CFatal, errno) ->
    let i = mk_issue EError (Some r) msg (Some errno) ctx in
    if Options.ide()
    then add_one i
    else failwith ("don't use log_issue to report fatal error, should use raise_error: " ^format_issue i)

let log_issue r (e, msg) =
  let ctx = error_context.get () in
  log_issue_ctx r (e, msg) ctx

let add_errors (errs : list error) : unit =
    atomically (fun () -> List.iter (fun (e, msg, r, ctx) -> log_issue_ctx r (e, msg) ctx) errs)

let issue_of_exn (e:exn) : option issue =
  match e with
  | Error(e, msg, r, ctx) ->
    let errno = error_number (lookup e) in
    Some (mk_issue EError (Some r) msg (Some errno) ctx)
  | Err (e, msg, ctx) ->
    let errno = error_number (lookup e) in
    Some (mk_issue EError None msg (Some errno) ctx)
  | _ -> None

let err_exn exn =
    if exn = Stop then ()
    else
    match issue_of_exn exn with
    | Some issue -> add_one issue
    | None -> raise exn

let handleable = function
  | Error _
  | Stop
  | Err _ -> true
  | _ -> false

let stop_if_err () =
    if get_err_count () > 0
    then raise Stop

let raise_error (e, msg) r =
  raise (Error (e, msg, r, error_context.get ()))

let raise_err (e, msg) =
  raise (Err (e, msg, error_context.get ()))

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
        Inl (Failure (msg ^ ctx_string (error_context.get ())))
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
  let r = try Some (f ())
          with | ex -> err_exn ex; None
  in
  let all_issues = newh.eh_report() in //de-duplicated already
  current_handler := old;
  let errs, rest = List.partition (fun i -> i.issue_level = EError) all_issues in
  errs, rest, r

let no_ctx (f : unit -> 'a) : 'a =
  let save = error_context.get () in
  error_context.clear ();
  let res = f () in
  error_context.set save;
  res

let catch_errors (f : unit -> 'a) : list issue * option 'a =
  let errs, rest, r = catch_errors_aux f in
  List.iter (!current_handler).eh_add_one rest;
  errs, r

//
// Similar to catch_errors, except the warnings are not added to the old handler
//
let catch_errors_and_ignore_rest (f:unit -> 'a) : list issue & option 'a =
  let errs, _, r = catch_errors_aux f in
  errs, r

(* Finds a discrepancy between two multisets of ints. Result is (elem, amount1, amount2)
 * eg. find_multiset_discrepancy [1;1;3;5] [1;1;3;3;4;5] = Some (3, 1, 2)
 *     since 3 appears 1 time in l1, but 2 times in l2. *)
let find_multiset_discrepancy (l1 : list int) (l2 : list int) : option (int * int * int) =
    let sort = List.sortWith (fun x y -> x - y) in
    let rec collect (l : list 'a) : list ('a * int) =
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
    let summ l =
        collect l
    in
    let l1 = summ (sort l1) in
    let l2 = summ (sort l2) in
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
