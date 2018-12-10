(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.IO

open FStar.All

exception EOF
assume new type fd_read : Type0
assume new type fd_write : Type0

assume val print_newline : unit -> ML unit
assume val print_string : string -> ML unit

(* assume val print_nat_hex : nat -> ML unit *)
(* assume val print_nat_dec : nat -> ML unit *)

assume val print_uint8 : FStar.UInt8.t -> ML unit
assume val print_uint8_dec : FStar.UInt8.t -> ML unit
assume val print_uint32 : FStar.UInt32.t -> ML unit
assume val print_uint32_dec : FStar.UInt32.t -> ML unit
assume val print_uint64 : FStar.UInt64.t -> ML unit
assume val print_uint64_dec : FStar.UInt64.t -> ML unit

assume val print_uint8_hex_pad : FStar.UInt8.t -> ML unit
assume val print_uint8_dec_pad : FStar.UInt8.t -> ML unit
assume val print_uint32_hex_pad : FStar.UInt32.t -> ML unit
assume val print_uint32_dec_pad : FStar.UInt32.t -> ML unit
assume val print_uint64_hex_pad : FStar.UInt64.t -> ML unit
assume val print_uint64_dec_pad : FStar.UInt64.t -> ML unit

assume val print_any : 'a -> ML unit
assume val input_line : unit -> ML string
assume val input_int : unit -> ML int
assume val input_float : unit -> ML FStar.Float.float
assume val open_read_file : string -> ML fd_read
assume val open_write_file : string -> ML fd_write
assume val close_read_file : fd_read -> ML unit
assume val close_write_file : fd_write -> ML unit
assume val read_line : fd_read -> ML string
assume val write_string : fd_write -> string -> ML unit

(*
   An UNSOUND escape hatch for printf-debugging;
   Although it always returns false, we mark it
   as returning a bool, so that extraction doesn't
   erase this call.

   Note: no guarantees are provided regarding the order
   of eassume valuation of this function; since it is marked as pure,
   the compiler may re-order or replicate it.
*)
assume val debug_print_string : string -> Tot bool
