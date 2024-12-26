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

(* Wrapper of OCaml in_channel.mli minimized code, see the OCaml 4.14 library for docs. *)
module FStar.In_Channel
open FStar.Char
open FStar.Bytes
open FStar.All

assume new type t

type open_flag = | Open_rdonly | Open_wronly | Open_append | Open_creat | Open_trunc   
  | Open_excl | Open_binary    | Open_text   | Open_nonblock

// Where OCaml specifies int, we send an int and F* annoying converts it to Z.t
// Where OCaml specifies int64, we and an UInt64 and OCaml gets it as an int64.
// Strings match nicely. Single chars may be being corrupted.

val stdin : t
val open_bin : string -> ML t
val open_text : string -> ML t
val open_gen : list open_flag -> FStar.UInt64.t -> string -> ML t
val with_open_bin : string -> (t -> 'a) -> ML 'a
val with_open_text : string -> (t -> 'a) -> ML 'a
val with_open_gen : list open_flag -> FStar.UInt64.t -> string -> (t -> 'a) -> ML 'a
val seek : t -> FStar.UInt64.t -> ML unit
val pos : t -> ML FStar.UInt64.t
val length : t -> ML FStar.UInt64.t
val close : t -> ML unit
val close_noerr : t -> ML unit
val input_char : t -> ML (option char)
val input_byte : t -> ML (option byte)
val input_line : t -> ML (option string)
val input : t -> int -> int -> ML (int & FStar.Bytes.bytes)
val really_input : t -> bytes -> FStar.UInt64.t -> FStar.UInt64.t -> ML (option unit)
val really_input_string : t -> FStar.UInt64.t -> ML (option string)
val input_all : t -> ML string
val set_binary_mode : t -> bool -> ML unit
