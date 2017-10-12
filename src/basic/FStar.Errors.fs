#light "off"
module FStar.Errors
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Util
open FStar.Range

exception Err of string
exception Error of string * Range.range
exception Warning of string * Range.range
exception Stop

(* Raised when an empty fragment is parsed *)
exception Empty_frag

module BU = FStar.Util

type issue_level =
| ENotImplemented
| EInfo
| EWarning
| EError

type issue = {
    issue_message: string;
    issue_level: issue_level;
    issue_range: option<Range.range>
}

type error_handler = {
    eh_add_one: issue -> unit;
    eh_count_errors: unit -> int;
    eh_report: unit -> list<issue>;
    eh_clear: unit -> unit
}

let format_issue issue =
    let level_header =
        match issue.issue_level with
        | EInfo -> "(Info) "
        | EWarning -> "(Warning) "
        | EError -> "(Error) "
        | ENotImplemented -> "Feature not yet implemented: " in
    let range_str, see_also_str =
        match issue.issue_range with
        | None -> "", ""
        | Some r ->
          (BU.format1 "%s: " (Range.string_of_use_range r),
           (if use_range r = def_range r then ""
            else BU.format1 " (see also %s)" (Range.string_of_range r))) in
    BU.format4 "%s%s%s%s\n" range_str level_header issue.issue_message see_also_str

let print_issue issue =
    BU.print_error (format_issue issue)

let compare_issues i1 i2 =
    match i1.issue_range, i2.issue_range with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some r1, Some r2 -> Range.compare_use_range r1 r2

let default_handler =
    let errs : ref<list<issue>> = BU.mk_ref [] in
    let add_one (e: issue) =
        match e.issue_level with
        | EError -> errs := e :: !errs
        | _ -> print_issue e in
    let count_errors () =
        List.length !errs in
    let report () =
        let sorted = List.sortWith compare_issues !errs in
        List.iter print_issue sorted;
        sorted in
    let clear () =
        errs := [] in
    { eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear }

let current_handler =
    BU.mk_ref default_handler

let mk_issue level range msg =
    { issue_level = level; issue_range = range; issue_message = msg }

let get_err_count () = (!current_handler).eh_count_errors ()

let add_one issue =
    atomically (fun () -> (!current_handler).eh_add_one issue)

let add_many issues =
    atomically (fun () -> List.iter (!current_handler).eh_add_one issues)

let report_all () =
    (!current_handler).eh_report ()

let clear () =
    (!current_handler).eh_clear ()

let set_handler handler =
    let issues = report_all () in
    clear (); current_handler := handler; add_many issues

let diag r msg = if Options.debug_any() then add_one (mk_issue EInfo (Some r) msg)

let warn r msg = add_one (mk_issue EWarning (Some r) msg)

let err r msg = add_one (mk_issue EError (Some r) msg)

type error_message_prefix = {
    set_prefix: string -> unit;
    append_prefix: string -> string;
    clear_prefix: unit -> unit;
}

let message_prefix =
    let pfx = BU.mk_ref None in
    let set_prefix s = pfx := Some s in
    let clear_prefix () = pfx := None in
    let append_prefix s = match !pfx with
        | None -> s
        | Some p -> p ^ ": " ^ s in
    {set_prefix=set_prefix;
     clear_prefix=clear_prefix;
     append_prefix=append_prefix}

let add_errors errs =
    atomically (fun () -> List.iter (fun (msg, r) -> err r (message_prefix.append_prefix msg)) errs)

let issue_of_exn = function
    | Error(msg, r) ->
      Some (mk_issue EError (Some r) (message_prefix.append_prefix msg))
    | NYI msg ->
      Some (mk_issue ENotImplemented None (message_prefix.append_prefix msg))
    | Err msg ->
      Some (mk_issue EError None (message_prefix.append_prefix msg))
    | _ -> None

let err_exn exn =
    if exn = Stop then ()
    else
    match issue_of_exn exn with
    | Some issue -> add_one issue
    | None -> raise exn

let handleable = function
  | Error _
  | NYI _
  | Stop
  | Err _ -> true
  | _ -> false

let stop_if_err () =
    if get_err_count () > 0
    then raise Stop
