(*
   Copyright 2008-2023 Nikhil Swamy and Microsoft Research

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
module FStar.Compiler.Range.Ops

open FStar.Compiler.Range.Type
open FStar.Compiler.Effect

val union_rng: rng -> rng -> rng
val union_ranges: range -> range -> range

val rng_included: rng -> rng -> bool
val string_of_pos: pos -> string
val string_of_range: range -> string
val string_of_def_range: range -> string
val string_of_use_range: range -> string
val file_of_range: range -> string
val set_file_of_range: range -> string -> range
val start_of_range: range -> pos
val end_of_range: range -> pos
val file_of_use_range: range -> string
val start_of_use_range: range -> pos
val end_of_use_range: range -> pos
val line_of_pos: pos -> int
val col_of_pos: pos -> int
val end_range: range -> range
val compare: range -> range -> int
val compare_use_range: range -> range -> int
val range_before_pos : range -> pos -> bool
val end_of_line: pos -> pos
val extend_to_end_of_line: range -> range

val json_of_pos : pos -> Json.json
val json_of_use_range : range -> Json.json
val json_of_def_range : range -> Json.json
