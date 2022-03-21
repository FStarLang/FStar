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
module JSONParser.Impl

module Spec = JSONParser.Spec

type char = Spec.char
type string = Spec.string

type string_ptr_field =
| StringLength
| StringPtr

type bstring = Buffer.buffer char

type string_ptr_struct = DependentMap.t _ (function
  | StringLength -> UInt32.t
  | StringPtr -> bstring
)

type string_ptr = Pointer.pointer string_ptr_struct

let string_ptr_struct_valid (h: HyperStack.mem) (s: string_ptr_struct) : GTot Type0 =
  let b: Buffer.buffer char = DependentMap.sel s StringPtr in
    Buffer.live h b /\
    UInt32.v (DependentMap.sel s StringLength) <= Buffer.length b

let string_ptr_struct_value (h: HyperStack.mem) (s: string_ptr_struct {string_ptr_struct_valid h s}) : GTot string =
  Seq.slice (Buffer.as_seq h (DependentMap.sel s StringPtr)) 0 (UInt32.v (DependentMap.sel s StringLength))

let string_ptr_valid (h: HyperStack.mem) (s: string_ptr) : GTot Type0 =
  Pointer.live h s /\
  string_ptr_struct_valid h (Pointer.gread h s)

let string_ptr_value (h: HyperStack.mem) (s: string_ptr {string_ptr_valid h s}): GTot string =
  string_ptr_struct_value h (Pointer.gread h s)

(* NOTE: an out-of-date version of the code is in KreMLin branch taramana_json_parser *)

(*
inline_for_extraction
let parse_exact_char
  (c: char)
  (b: bstring)
  (length: UInt32.t)
: ST.ST (option (bstring * UInt32.t))
  (requires (fun h -> Buffer.live h b /\ length <= Buffer.length b))
  (ensures (fun h res h' ->
    h' == h /\
    Buffer.live h b /\
    n <= Buffer.length b /\
    match Spec.gparse_exact_char c (Seq.slice (Buffer.as_seq b) 0 n) with
    | None -> res == None
    | Some s' -> begin match res with
      | None -> False
      | Some (b', n') ->
	n > 0 /\
	n' == n - 1 /\
        b' == Buffer.sub b 1 n' /\
	Seq.slice (Buffer.as_seq b)
*)
