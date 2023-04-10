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

(* Get the error number for a particular code. Useful for creating error
messages mentioning --warn_error. *)
val errno : raw_error -> int

(* Particular errors code numbers, useful to build helpful error messages *)
val warn_on_use_errno    : int
val defensive_errno      : int
val call_to_erased_errno : int

val update_flags : list (error_flag * string) -> list error_setting

(* error code, message, source position, and error context *)
type error = raw_error * string * FStar.Compiler.Range.range * list string

exception Error   of error
exception Err     of raw_error * string * list string
exception Warning of error
exception Stop
exception Empty_frag

type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError

type issue = {
    issue_msg: string;
    issue_level: issue_level;
    issue_range: option Range.range;
    issue_number: option int;
    issue_ctx: list string;
}

type error_handler = {
    eh_add_one: issue -> unit;
    eh_count_errors: unit -> int;
    eh_report: unit -> list issue;
    eh_clear: unit -> unit
}

val issue_message : issue -> string
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
val diag : Range.range -> string -> unit

val set_option_warning_callback_range : ropt:option FStar.Compiler.Range.range -> unit
val set_parse_warn_error : (string -> list error_setting) -> unit

val lookup : raw_error -> error_setting

val err_exn : exn -> unit
val handleable : exn -> bool

(* If any error was logged, then stop the program (raising a Stop
exception). This is useful, for instance, to not run tactics in a given
top-level definition if a typechecking error was already logged, since
that may imply that the tactic will crash or loop. *)
val stop_if_err : unit -> unit

(* Log an error/warning/etc. This does not raise an exception. Do not
use this for any CFatal error. *)
val log_issue   : Range.range -> raw_error & string -> unit

(* Raise an error. This raises an exception and does not return. *)
val raise_error : (raw_error & string) -> Range.range -> 'a
val raise_err   : (raw_error & string) -> 'a

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
val catch_errors : (unit -> 'a) -> list issue * option 'a


(* Similar to catch_errors, except the warnings are not added to the old handler *)
val catch_errors_and_ignore_rest (f:unit -> 'a) : list issue & option 'a










(* TODO: Find a better home? *)
(* Finds a discrepancy between two multisets of ints. Result is (elem, amount1, amount2)
 * eg. find_multiset_discrepancy [1;1;3;5] [1;1;3;3;4;5] = Some (3, 1, 2)
 *     since 3 appears 1 time in l1, but 2 times in l2. *)
val find_multiset_discrepancy : list int -> list int -> option (int * int * int)
