(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.Format

(* Formatting/printing utils *)

open FStarC.Effect
open FStarC.Json

type printer = {
  printer_prinfo: string -> unit;
  printer_prwarning: string -> unit;
  printer_prerror: string -> unit;
  printer_prgeneric: string -> (unit -> string) -> (unit -> json) -> unit
}

val default_printer : printer
val set_printer : printer -> unit

val print_raw : string -> unit
val print_generic: string -> ('a -> string) -> ('a -> json) -> 'a -> unit
val print_any : 'a -> unit

val print_string (s : string) : unit

val fmt
  (spec : string)
  (args : list string)
  : string

val fmt1
  (spec : string)
  (arg1 : string)
  : string

val fmt2
  (spec : string)
  (arg1 arg2 : string)
  : string

val fmt3
  (spec : string)
  (arg1 arg2 arg3 : string)
  : string

val fmt4
  (spec : string)
  (arg1 arg2 arg3 arg4 : string)
  : string

val fmt5
  (spec : string)
  (arg1 arg2 arg3 arg4 arg5 : string)
  : string

val fmt6
  (spec : string)
  (arg1 arg2 arg3 arg4 arg5 arg6 : string)
  : string

val print
  (spec : string)
  (args : list string)
  : unit

val print1
  (spec : string)
  (arg1 : string)
  : unit

val print2
  (spec : string)
  (arg1 arg2 : string)
  : unit

val print3
  (spec : string)
  (arg1 arg2 arg3 : string)
  : unit

val print4
  (spec : string)
  (arg1 arg2 arg3 arg4 : string)
  : unit

val print5
  (spec : string)
  (arg1 arg2 arg3 arg4 arg5 : string)
  : unit

val print6
  (spec : string)
  (arg1 arg2 arg3 arg4 arg5 arg6 : string)
  : unit

val print_error: string -> unit
val print1_error: string -> string -> unit
val print2_error: string -> string -> string -> unit
val print3_error: string -> string -> string -> string -> unit

val print_warning: string -> unit
val print1_warning: string -> string -> unit
val print2_warning: string -> string -> string -> unit
val print3_warning: string -> string -> string -> string -> unit

val flush_stdout () : unit

val stdout_isatty () : option bool

// These functions have no effect
val colorize : string -> (string & string) -> string
val colorize_bold : string -> string
val colorize_red : string -> string
val colorize_yellow : string -> string
val colorize_cyan : string -> string
val colorize_green : string -> string
val colorize_magenta : string -> string
