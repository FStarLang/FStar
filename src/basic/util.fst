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

(* generic utils *)
type smap : Type => Type
assume val smap_create: int -> smap 'value
assume val smap_add: smap 'value -> string -> 'value -> unit
assume val smap_try_find: smap<'value> -> string -> option<'value>
assume val smap_fold: smap<'value> -> (string -> 'value -> 'a -> 'a) -> 'a -> 'a

assume val format: string -> list<string> -> string
assume val format1: string -> string -> string
assume val format2: string -> string -> string -> string
assume val format3: string -> string -> string -> string -> string
assume val format4: string -> string -> string -> string -> string -> string
assume val print_string : string -> unit
assume val print_any: 'a -> unit
assume val strcat : string -> string -> string
assume val concat_l : string -> list<string> -> string
assume val write_file: string -> string -> unit

assume val int_of_string:   string -> int
assume val int_of_char:   char -> int
assume val char_of_int:   int -> char
assume val uint16_of_int: int -> uint16
assume val string_of_int:   int -> string
assume val string_of_float: float -> string
assume val string_of_char:  char -> string
assume val string_of_bytes: array byte -> string
assume val substring: string -> int -> int -> string
assume val char_at: string -> int -> char
assume val starts_with: string -> string -> bool

type either<'a,'b> =
  | Inl of 'a
  | Inr of 'b

assume val physical_eq: 'a -> 'a -> bool 
assume val nodups: ('a -> 'a -> bool) -> list<'a> -> bool
assume val sort_with: ('a -> 'a -> int) -> list<'a> -> list<'a>
assume val set_eq: ('a -> 'a -> int) -> list<'a> -> list<'a> -> bool
assume val remove_dups: ('a -> 'a -> bool) -> list<'a> -> list<'a>
assume val find_map: list<'a> -> ('a -> option<'b>) -> option<'b>
assume val for_all: ('a -> bool) -> list<'a> -> bool
assume val for_some: ('a -> bool) -> list<'a> -> bool
assume val forall_exists: ('a -> 'b -> bool) -> list<'a> -> list<'b> -> bool
assume val multiset_equiv: ('a -> 'b -> bool) -> list<'a> -> list<'b> -> bool

assume val must: option<'a> -> 'a
assume val find_opt: ('a -> bool) -> list<'a> -> option<'a>
assume val bind_opt: option<'a> -> ('a -> option<'b>) -> option<'b>
assume val map_opt: option<'a> -> ('a -> 'b) -> option<'b>

assume val first_N: int -> list<'a> -> (list<'a> * list<'a>)
assume val prefix: list<'a> -> (list<'a> * 'a)

assume val string_of_unicode: array byte -> string
assume val unicode_of_string: string -> array byte
assume val incr: ref int -> unit
assume val geq: int -> int -> bool
assume val for_range: int -> int -> (int -> unit) -> unit

(* A simple state monad *)
type state<'s,'a> = ('s -> 'a * 's) (* not relying on definition *)
assume val get: state<'s,'s> 
assume val put: 's -> state<'s,unit>
assume val upd: ('s -> 's) -> state<'s,unit>
assume val ret: 'a -> state<'s,'a>
assume val bind: state<'s,'a> -> ('a -> state<'s,'b>) -> state<'s,'b>
assume val stmap: list<'a> -> ('a -> state<'s,'b>) -> state<'s, list<'b>>
assume val stiter: list<'a> -> ('a -> state<'s,unit>) -> state<'s,unit>
assume val stfold: 'b -> list<'a> -> ('b -> 'a -> state<'s,'b>) -> state<'s,'b>
assume val run_st: 's -> state<'s,'a> -> ('a * 's)
assume val mk_ref: 'a -> ref<'a>

(* query log *)
assume val bump_query_count: (unit -> int)
assume val query_count: (unit -> int)

assume val expand_environment_variable: string -> string
