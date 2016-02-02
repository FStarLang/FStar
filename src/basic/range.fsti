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
module FStar.Range
type range = int64
type file_idx = int32
type pos = int32

val dummyRange : range
val mk_pos: int -> int -> pos
val mk_file_idx_range:file_idx -> int -> int -> range
val mk_range: string -> int -> int -> range
val encode_file:string -> string
val decode_file_idx:string -> int
val file_of_file_idx:file_idx -> string
val union_ranges: range -> range -> range
val string_of_range: range -> string
val file_of_range: range -> string
val string_of_pos: pos -> string
val start_of_range: range -> pos
val line_of_pos: pos -> int
val end_range: range -> range
val compare: range -> range -> int
