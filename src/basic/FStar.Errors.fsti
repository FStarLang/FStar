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

module Range = FStar.Compiler.Range

include FStar.Errors.Codes
include FStar.Errors.Msg
open FStar.Errors.Msg

(* This is a fallback to be used if an error is raised/logged
with a dummy range. It is set by TypeChecker.Tc.process_one_decl to
the range of the sigelt being checked. *)
val fallback_range : FStar.Compiler.Effect.ref (option Range.range)

(* Get the error number for a particular code. Useful for creating error
messages mentioning --warn_error. *)
val errno : error_code -> int

(* Particular errors code numbers, useful to build helpful error messages *)
val warn_on_use_errno    : int
val defensive_errno      : int
val call_to_erased_errno : int

val update_flags : list (error_flag & string) -> list error_setting

(* error code, message, source position, and error context *)
type error = error_code & error_message & FStar.Compiler.Range.range & list string

exception Error   of error
exception Warning of error
exception Stop
exception Empty_frag

type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError

type issue = {
    issue_msg: error_message;
    issue_level: issue_level;
    issue_range: option Range.range;
    issue_number: option int;
    issue_ctx: list string;
}

type error_handler = {
    eh_name: string; (* just for debugging purposes *)
    eh_add_one: issue -> unit;
    eh_count_errors: unit -> int;
    eh_report: unit -> list issue;
    eh_clear: unit -> unit
}

val string_of_issue_level : issue_level -> string
val issue_level_of_string : string -> issue_level
val issue_message : issue -> error_message
val format_issue' : bool -> issue -> string
val format_issue : issue -> string
val error_number : error_setting -> int
val print_issue : issue -> unit
val compare_issues : issue -> issue -> int // for sorting.. weird

val add_errors : list error -> unit
val issue_of_exn : exn -> option issue

val default_handler : error_handler

val get_err_count : unit -> int
val report_all : unit -> list issue
val clear : unit -> unit
val set_handler : error_handler -> unit
val get_ctx : unit -> list string

val diag_doc : Range.range -> error_message -> unit
val diag : Range.range -> string -> unit

val diag0 : string -> unit
val diag1 : string -> string -> unit
val diag2 : string -> string -> string -> unit
val diag3 : string -> string -> string -> string -> unit
val diag4 : string -> string -> string -> string -> string -> unit
val diag5 : string -> string -> string -> string -> string -> string -> unit

val set_option_warning_callback_range : ropt:option FStar.Compiler.Range.range -> unit
val set_parse_warn_error : (string -> list error_setting) -> unit

val lookup : error_code -> error_setting

val err_exn : exn -> unit
val handleable : exn -> bool

(* If any error was logged, then stop the program (raising a Stop
exception). This is useful, for instance, to not run tactics in a given
top-level definition if a typechecking error was already logged, since
that may imply that the tactic will crash or loop. *)
val stop_if_err : unit -> unit

(* Log an error/warning/etc. This does not raise an exception. Do not
use this for any CFatal error. *)

(* Log an issue directly, rather than converting it from a error_code etc.
   This does not raise an exception. Do not use this for any CFatal error. *)
val add_issues : list issue -> unit

val raise_error  : Range.range -> error_code -> #t:_ -> {| is_error_message t |} -> t -> 'a
val log_issue    : Range.range -> error_code -> #t:_ -> {| is_error_message t |} -> t -> unit

val raise_error0 : error_code -> #t:_ -> {| is_error_message t |} -> t -> 'a
val log_issue0   : error_code -> #t:_ -> {| is_error_message t |} -> t -> unit

(* Run a function f inside an extended "error context", so its errors
are prefixed by the messages of each enclosing with_ctx. Only visible
when --error_contexts true is given. *)
val with_ctx : ctx:string -> (f : unit -> 'a) -> 'a

(* As above, but only add the context conditionally. *)
val with_ctx_if : cond:bool -> ctx:string -> (f : unit -> 'a) -> 'a

(* Delete all error contexts for this comp. *)
val no_ctx : (f : unit -> 'a) -> 'a

(* Run a given function and return its result (if any) and the full list of
issues it logged/raised. *)
val catch_errors : (unit -> 'a) -> list issue & option 'a


(* Similar to catch_errors, except the warnings are not added to the old handler *)
val catch_errors_and_ignore_rest (f:unit -> 'a) : list issue & option 'a










(* TODO: Find a better home? *)
(* Finds a discrepancy between two multisets of ints. Result is (elem, amount1, amount2)
 * eg. find_multiset_discrepancy [1;1;3;5] [1;1;3;3;4;5] = Some (3, 1, 2)
 *     since 3 appears 1 time in l1, but 2 times in l2. *)
val find_multiset_discrepancy : list int -> list int -> option (int & int & int)



(* Specialized variants, only useful for OCaml code. Not to be used from F* sources. *)
val raise_error_doc  : Range.range -> error_code -> error_message -> 'a
val log_issue_doc    : Range.range -> error_code -> error_message -> unit
val raise_error_text : Range.range -> error_code -> string -> 'a
val log_issue_text   : Range.range -> error_code -> string -> unit
