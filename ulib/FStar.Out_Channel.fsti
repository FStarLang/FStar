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

(* Wrapper of OCaml out_channel.mli minimized code, see the OCaml library for docs. *)
module FStar.Out_Channel
open FStar.Char
open FStar.Bytes
open FStar.All

type int64 = FStar.Int64.t

assume new type t 
type open_flag = | Open_rdonly | Open_wronly | Open_append  | Open_creat  | Open_trunc       
  | Open_excl | Open_binary | Open_text | Open_nonblock    

val stdout : t
val stderr : t
val open_bin : string -> ML t
val open_text : string -> ML t
val open_gen : list open_flag -> int -> string -> ML t
val with_open_bin : string -> (t -> 'a) -> ML 'a
val with_open_text : string -> (t -> 'a) -> ML 'a
val with_open_gen : list open_flag -> int -> string -> (t -> 'a) -> ML 'a
val close : t -> ML unit
val close_noerr : t -> ML unit
val output_char : t -> int -> ML unit
val output_byte : t -> int -> ML unit
val output_string : t -> string -> ML unit
val output_bytes : t -> bytes -> ML unit
val output : t -> bytes -> int -> int -> ML unit
val output_substring : t -> string -> int -> int -> ML unit
val flush : t -> ML unit
val flush_all : unit -> ML unit
val seek : t -> int64 -> ML unit
val pos : t -> ML int64
val length : t -> ML int64
val set_binary_mode : t -> bool -> ML unit
val set_buffered : t -> bool -> ML unit
val is_buffered : t -> ML bool

(* Not in this OCaml revision amazingly.
val isatty : t -> bool
val is_binary_mode : t -> bool
*)
