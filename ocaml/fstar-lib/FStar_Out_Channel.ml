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

open Out_channel
type t = out_channel
open FStar_Wrap_OCaml

(*
   As Out_channel.t are the subtypes here:
   of_t maps Out_channel t to t        - used on the outputs
   to_t maps t      to Out_channel.t   - used on the inputs
*)

type open_flag = Stdlib.open_flag =
  | Open_rdonly | Open_wronly | Open_append  | Open_creat
  | Open_trunc  | Open_excl   | Open_binary  | Open_text
  | Open_nonblock

let stdout = Out_channel.stdout
let stderr = Out_channel.stderr

let open_bin  = open_bin
let open_text = open_text

let open_gen fl perm s =
  let perm' = Z.to_int perm in
   open_gen fl perm' s

let with_open_gen fl perm s fn =
  let perm' = Z.to_int perm in
   with_open_gen fl perm' s fn 

let with_open_bin : string -> (t -> 'a) -> 'a       = with_open_bin
let with_open_text : string -> (t -> 'a) -> 'a      = with_open_text

let close : t -> unit                   = close
let close_noerr : t -> unit             = close_noerr
let output_char : t -> Z.t -> unit      = 
  wrapIawbOc output_char (fun z -> (Char.chr (Z.to_int z)))

let output_byte t i =
  let i' = Z.to_int i in
   output_byte t i'

let output_string : t -> string -> unit = output_string

let output_bytes t bs = 
  output_bytes t (Bytes.of_string bs)

let output t bs pos len =
  let pos' = Z.to_int pos       in
  let len' = Z.to_int len       in
  let bs'  = Bytes.of_string bs in
   output t bs' pos' len'

let output_substring t s pos len =
  let pos' = Z.to_int pos in
  let len' = Z.to_int len in  
   output_substring t s pos' len'

(*  No big arrays in F*.
 let output_bigarray : 
  t -> (_, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t ->
  int -> int -> unit
*)

let flush     : t -> unit           = flush
let flush_all : unit -> unit        = flush_all
let seek      : t -> int64 -> unit  = seek
let pos       : t -> int64          = pos
let length    : t -> int64          = length 

let set_binary_mode : t -> bool -> unit = set_binary_mode
let set_buffered    : t -> bool -> unit = set_buffered
let is_buffered     : t -> bool         = is_buffered

(* Are not in this revision of OCaml. *)
(* let is_binary_mode  : t -> bool         = Out_channel.is_binary_mode *)
(* let isatty          : t -> bool         = isatty *)
