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
module Microsoft.FStar.Util

exception Impos
exception NYI of string
exception Failure of string

val lift_all: 'a -> 'a

(* generic utils *)
type smap<'value> = HashMultiMap<string,'value> (* not relying on representation *)
val smap_create: int -> smap<'value>
val smap_add: smap<'value> -> string -> 'value -> unit
val smap_try_find: smap<'value> -> string -> option<'value>
val smap_fold: smap<'value> -> (string -> 'value -> 'a -> 'a) -> 'a -> 'a
val smap_remove: smap<'value> -> string -> unit

val format: string -> list<string> -> string
val format1: string -> string -> string
val format2: string -> string -> string -> string
val format3: string -> string -> string -> string -> string
val format4: string -> string -> string -> string -> string -> string
val print_string : string -> unit
val print_any : 'a -> unit
val strcat : string -> string -> string
val concat_l : string -> list<string> -> string
val write_file: string -> string -> unit

val int_of_string:   string -> int
val int_of_char:   char -> int
val char_of_int:   int -> char
val uint16_of_int: int -> uint16
val string_of_int:   int -> string
val string_of_float: float -> string
val string_of_char:  char -> string
val string_of_bytes: byte[] -> string
val substring: string -> int -> int -> string
val starts_with: string -> string -> bool
val ends_with: string -> string -> bool
val char_at: string -> int -> char
val is_upper: char -> bool

type either<'a,'b> =
  | Inl of 'a
  | Inr of 'b
 
val left: either<'a,'b> -> 'a
val right: either<'a,'b> -> 'b    
val nodups: ('a -> 'a -> bool) -> list<'a> -> bool
val sort_with: ('a -> 'a -> int) -> list<'a> -> list<'a>
val set_eq: ('a -> 'a -> int) -> list<'a> -> list<'a> -> bool
val remove_dups: ('a -> 'a -> bool) -> list<'a> -> list<'a>
val add_unique: ('a -> 'a -> bool) -> 'a -> list<'a> -> list<'a>
val find_map: list<'a> -> ('a -> option<'b>) -> option<'b>
val fold_map: ('a -> 'b -> 'a * 'c) -> 'a -> list<'b> -> 'a * list<'c>
val choose_map: ('a -> 'b -> 'a * 'c option) -> 'a -> list<'b> -> 'a * list<'c>
val for_all: ('a -> bool) -> list<'a> -> bool
val for_some: ('a -> bool) -> list<'a> -> bool
val forall_exists: ('a -> 'b -> bool) -> list<'a> -> list<'b> -> bool
val multiset_equiv: ('a -> 'b -> bool) -> list<'a> -> list<'b> -> bool

val is_some: option<'a> -> bool
val must: option<'a> -> 'a
val find_opt: ('a -> bool) -> list<'a> -> option<'a>
val bind_opt: option<'a> -> ('a -> option<'b>) -> option<'b>
val map_opt: option<'a> -> ('a -> 'b) -> option<'b>

val first_N: int -> list<'a> -> (list<'a> * list<'a>)
val prefix: list<'a> -> (list<'a> * 'a)

val string_of_unicode: byte[] -> string
val unicode_of_string: string -> byte[] 
val incr: ref<int> -> unit
val geq: int -> int -> bool
val for_range: int -> int -> (int -> unit) -> unit

(* A simple state monad *)
type state<'s,'a> = ('s -> 'a * 's) (* not relying on definition *)
val get: state<'s,'s> 
val put: 's -> state<'s,unit>
val upd: ('s -> 's) -> state<'s,unit>
val ret: 'a -> state<'s,'a>
val bind: state<'s,'a> -> ('a -> state<'s,'b>) -> state<'s,'b>
val stmap: list<'a> -> ('a -> state<'s,'b>) -> state<'s, list<'b>>
val stiter: list<'a> -> ('a -> state<'s,unit>) -> state<'s,unit>
val stfold: 'b -> list<'a> -> ('b -> 'a -> state<'s,'b>) -> state<'s,'b>
val run_st: 's -> state<'s,'a> -> ('a * 's)
val mk_ref: 'a -> ref<'a>

(* query log *)
val bump_query_count: (unit -> int)
val query_count: (unit -> int)

val expand_environment_variable: string -> string

