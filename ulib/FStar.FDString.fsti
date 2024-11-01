(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes
*)

module FStar.FDString

(* Although this works nicely, one must thread the non-mutable fd_strings
 through the code. A mutable one would be much nicer.
*)

open FStar.All

new val fd_string : eqtype 
new val fd_string_read  : eqtype
new val fd_string_write : eqtype

val open_read_file : unit -> fd_string_read
val open_write_file : unit -> fd_string_write
val close_read_file : fd_string_read -> unit
val close_write_file : fd_string_write -> unit

val print_newline : fd_string_write -> fd_string_write
val print_string  : fd_string_write -> string -> fd_string_write

val input_line    : fd_string_read -> ML (string & fd_string_read)
val read_line     : fd_string_read -> ML (string & fd_string_read)
val write_string  : fd_string_write -> string -> fd_string_write

val fd_write_to_fd_read : fd_string_write -> fd_string_read
val fd_write_to_string : fd_string_write -> string

