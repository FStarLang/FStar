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
module Microsoft.FStar.Range

type range = int64
type file_idx = int32
type pos = int32

assume val mk_pos: int -> int -> pos
assume val mk_file_idx_range:file_idx -> int -> int -> range
assume val mk_range: string -> int -> int -> range
assume val encode_file:string -> string
assume val decode_file_idx:string -> int
assume val file_of_file_idx:file_idx -> string
assume val union_ranges: range -> range -> range
assume val string_of_range: range -> string
assume val file_of_range: range -> string
assume val string_of_pos: pos -> string
assume val start_of_range: range -> pos
assume val line_of_pos: pos -> int
assume val end_range: range -> range
