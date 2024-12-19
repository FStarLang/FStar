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

(* OCaml Input channels 4.14.0 *)

type t = In_channel.t
type open_flag = | Open_rdonly | Open_wronly | Open_append | Open_creat | Open_trunc   
  | Open_excl | Open_binary    | Open_text   | Open_nonblock

val stdin : t
val open_bin : string -> t
val open_text : string -> t
val open_gen : open_flag list -> int -> string -> t
val with_open_bin : string -> (t -> 'a) -> 'a
val with_open_text : string -> (t -> 'a) -> 'a
val with_open_gen : open_flag list -> int -> string -> (t -> 'a) -> 'a
val seek : t -> int64 -> unit
val pos : t -> int64
val length : t -> int64
val close : t -> unit
val close_noerr : t -> unit
val input_char : t -> FStar_Char.char option
val input_byte : t -> int option
val input_line : t -> string option

(* This type is modified as we don't take back mutated data from OCaml.
  We could put in an input buffer but did not do that. 
  F* translates int into Z.t (unfortunately) but not intXs.
*)
val input : t -> Z.t -> Z.t -> (Z.t * FStar_Bytes.bytes)
val really_input : t -> int -> int -> (unit option * FStar_Bytes.bytes)
val really_input_string : t -> int -> string option
val input_all : t -> string
val set_binary_mode : t -> bool -> unit

