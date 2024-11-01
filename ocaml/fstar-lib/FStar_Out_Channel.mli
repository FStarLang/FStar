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
open Out_channel
type t = out_channel

type open_flag = Stdlib.open_flag =
  | Open_rdonly | Open_wronly | Open_append  | Open_creat
  | Open_trunc  | Open_excl   | Open_binary  | Open_text
  | Open_nonblock

val stdout : t
val stderr : t
val open_bin : string -> t
val open_text : string -> t
val with_open_bin : string -> (t -> 'a) -> 'a
val with_open_text : string -> (t -> 'a) -> 'a
val open_gen : open_flag list -> Z.t -> string -> t
val with_open_gen : open_flag list -> Z.t -> string -> (t -> 'a) -> 'a
val close : t -> unit
val close_noerr : t -> unit
val output_char : t -> Z.t -> unit
val output_byte : t -> Z.t -> unit
val output_string : t -> string -> unit
val output_bytes : t -> FStar_Bytes.bytes -> unit
val output : t -> FStar_Bytes.bytes -> Z.t -> Z.t -> unit
val output_substring : t -> string -> Z.t -> Z.t -> unit

(*
val output_bigarray :
  t -> (_, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  int -> int -> unit
*)

val flush : t -> unit
val flush_all : unit -> unit
val seek : t -> int64 -> unit
val pos : t -> int64
val length : t -> int64
val set_binary_mode : t -> bool -> unit
val set_buffered : t -> bool -> unit
val is_buffered : t -> bool

(* Not in this OCaml revision.
val is_binary_mode : t -> bool
val isatty : t -> bool
*)
