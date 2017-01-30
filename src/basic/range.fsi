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
#light "off"
module FStar.Range

open FStar.BaseTypes

type range = {
    def_range:int64;
    use_range:int64
}
type file_idx = int32
type pos = int32

val zeroPos : pos
val dummyRange: range

val set_use_range: range -> range -> range

val mk_pos: int -> int -> pos
val mk_file_idx_range:file_idx -> pos -> pos -> range
val mk_range: string -> pos -> pos -> range
val encode_file:string -> string
val decode_file_idx:string -> int
val file_of_file_idx:file_idx -> string
val union_ranges: range -> range -> range
val string_of_range: range -> string
val string_of_use_range: range -> string
val file_of_range: range -> string
val string_of_pos: pos -> string
val start_of_range: range -> pos
val end_of_range: range -> pos
val line_of_pos: pos -> int
val pos_eq : pos -> pos -> bool
val pos_geq : pos -> pos -> bool
val end_range: range -> range
val compare: range -> range -> int
val compare_use_range: range -> range -> int
val set_file_of_range: range -> string -> unit
val range_contains_range: range -> range -> bool
val range_contains_pos: range -> pos -> bool
val range_before_pos : range -> pos -> bool
val range_before_range : range -> range -> bool
val end_of_line : pos -> pos
val extend_to_end_of_line : range -> range
