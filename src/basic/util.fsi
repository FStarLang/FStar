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
module FStar.Util
open FStar.All
open System.IO

open FStar.BaseTypes

exception Impos
exception NYI of string
exception Failure of string

val max_int: int
val return_all: 'a -> 'a

type time = System.DateTime
val now : unit -> time
val time_diff: time -> time -> float*int
val record_time: (unit -> 'a) -> ('a * int)
val is_before: time -> time -> bool
val get_file_last_modification_time: string -> time
val string_of_time: time -> string

(* generic utils *)
(* Functional sets *)
type set<'a> = (list<'a> * ('a -> 'a -> bool))
val new_set: ('a -> 'a -> int) -> ('a -> int) -> set<'a>
val set_is_empty: set<'a> -> bool
val set_add: 'a -> set<'a> -> set<'a>
val set_remove: 'a -> set<'a> -> set<'a>
val set_mem: 'a -> set<'a> -> bool
val set_union: set<'a> -> set<'a> -> set<'a>
val set_intersect: set<'a> -> set<'a> -> set<'a>
val set_is_subset_of: set<'a> -> set<'a> -> bool
val set_count: set<'a> -> int
val set_difference: set<'a> -> set<'a> -> set<'a>
val set_elements: set<'a> -> list<'a>

(* A fifo_set is a set preserving the insertion order *)
type fifo_set<'a> = set<'a>
val new_fifo_set: ('a -> 'a -> int) -> ('a -> int) -> fifo_set<'a>
val fifo_set_is_empty: fifo_set<'a> -> bool
(* [fifo_set_add x s] pushes an element [x] at the end of the set [s] *)
val fifo_set_add: 'a -> fifo_set<'a> -> fifo_set<'a>
(* [fifo_set_remove x s] removes [x]from [s] *)
val fifo_set_remove: 'a -> fifo_set<'a> -> fifo_set<'a>
val fifo_set_mem: 'a -> fifo_set<'a> -> bool
(* [fifo_set s1 s2] is the set with all elements in [s1] inserted before those of [s2] *)
val fifo_set_union: fifo_set<'a> -> fifo_set<'a> -> fifo_set<'a>
val fifo_set_count: fifo_set<'a> -> int
val fifo_set_difference: fifo_set<'a> -> fifo_set<'a> -> fifo_set<'a>
val fifo_set_elements: fifo_set<'a> -> list<'a>

type smap<'value> = System.Collections.Generic.Dictionary<string,'value> (* not relying on representation *)
val smap_create: int -> smap<'value>
val smap_clear:smap<'value> -> unit
val smap_add: smap<'value> -> string -> 'value -> unit
val smap_of_list: list<(string*'value)> -> smap<'value>
val smap_try_find: smap<'value> -> string -> option<'value>
val smap_fold: smap<'value> -> (string -> 'value -> 'a -> 'a) -> 'a -> 'a
val smap_remove: smap<'value> -> string -> unit
(* The list may contain duplicates. *)
val smap_keys: smap<'value> -> list<string>
val smap_copy: smap<'value> -> smap<'value>
val smap_size: smap<'value> -> int

type imap<'value> = System.Collections.Generic.Dictionary<int,'value> (* not relying on representation *)
val imap_create: int -> imap<'value>
val imap_clear:imap<'value> -> unit
val imap_add: imap<'value> -> int -> 'value -> unit
val imap_of_list: list<(int*'value)> -> imap<'value>
val imap_try_find: imap<'value> -> int -> option<'value>
val imap_fold: imap<'value> -> (int -> 'value -> 'a -> 'a) -> 'a -> 'a
val imap_remove: imap<'value> -> int -> unit
(* The list may contain duplicates. *)
val imap_keys: imap<'value> -> list<int>
val imap_copy: imap<'value> -> imap<'value>

val format: string -> list<string> -> string
val format1: string -> string -> string
val format2: string -> string -> string -> string
val format3: string -> string -> string -> string -> string
val format4: string -> string -> string -> string -> string -> string
val format5: string -> string -> string -> string -> string -> string -> string

val print: string -> list<string> -> unit
val print1: string -> string -> unit
val print2: string -> string -> string -> unit
val print3: string -> string -> string -> string -> unit
val print4: string -> string -> string -> string -> string -> unit
val print5: string -> string -> string -> string -> string -> string -> unit
val print6: string -> string -> string -> string -> string -> string -> string -> unit

val print_error: string -> unit
val print1_error: string -> string -> unit
val print2_error: string -> string -> string -> unit
val print3_error: string -> string -> string -> string -> unit

val print_warning: string -> unit
val print1_warning: string -> string -> unit
val print2_warning: string -> string -> string -> unit
val print3_warning: string -> string -> string -> string -> unit

val stdout_isatty: unit -> option<bool>

// These functions have no effect
val colorize: string -> (string * string) -> string
val colorize_bold: string -> string
val colorize_red: string -> string
val colorize_cyan: string -> string


(* Clients of this module should *NOT* rely on this representation *)
type out_channel = TextWriter
val stderr: out_channel
val stdout: out_channel
val fprint: out_channel -> string -> list<string> -> unit

type printer = {
  printer_prinfo: string -> unit;
  printer_prwarning: string -> unit;
  printer_prerror: string -> unit;
}

val default_printer : printer
val set_printer : printer -> unit

val print_raw : string -> unit
val print_string : string -> unit
val print_any : 'a -> unit
val strcat : string -> string -> string
val concat_l : string -> list<string> -> string

type file_handle = System.IO.TextWriter (* not relying representation *)
val open_file_for_writing: string -> file_handle
val append_to_file: file_handle -> string -> unit
val close_file: file_handle -> unit
val write_file: string -> string -> unit
val flush_file: file_handle -> unit
val file_get_contents: string -> string
val mkdir: bool-> string -> unit (* [mkdir clean d] a new dir with user read/write; else delete content of [d] if it exists && clean *)
val concat_dir_filename: string -> string -> string

type stream_reader = System.IO.StreamReader (* not relying on representation *)
val open_stdin : unit -> stream_reader
val read_line: stream_reader -> option<string>

type string_builder = System.Text.StringBuilder (* not relying on representation *)
val new_string_builder: unit -> string_builder
val clear_string_builder: string_builder -> unit
val string_of_string_builder: string_builder -> string
val string_builder_append: string_builder -> string -> unit

val message_of_exn: exn -> string
val trace_of_exn: exn -> string

type proc = {m:System.Object; outbuf:System.Text.StringBuilder; proc:System.Diagnostics.Process; killed:ref<bool>; id:string}  (* not relying on representation; this needs to be defined on one line for a sed script *)
val launch_process: string -> string -> string -> string -> (string -> string -> bool) -> string
val start_process: string -> string -> string -> (string -> string -> bool) -> proc
val ask_process: proc -> string -> string
val kill_process: proc -> unit
val kill_all: unit -> unit

val run_proc : string -> string -> string -> (bool * string * string)

val get_file_extension: string -> string
val is_path_absolute: string -> bool
val join_paths: string -> string -> string
val normalize_file_path: string -> string
val basename: string -> string
val getcwd: unit -> string
val readdir: string -> list<string>

open Prims
val file_exists: string -> Tot<bool>

val int_of_string: string -> int
val int_of_char:   char -> Tot<int>
val int_of_byte:   byte -> Tot<int>
val byte_of_char: char -> Tot<byte>
val char_of_int:   int -> Tot<char>
val int_of_uint8: uint8 -> Tot<int>
val uint16_of_int: int -> Tot<uint16>
val float_of_byte: byte -> Tot<float>
val float_of_int32: int32 -> Tot<float>
val float_of_int64: int64 -> Tot<float>
val float_of_string: string -> Tot<float>
val int_of_int32: int32 -> Tot<int>
val int32_of_int:   int -> int32 //potentially failing int32 coercion
val string_of_int:   int -> string
val string_of_bool:   bool -> string
val string_of_int64: int64 -> Tot<string>
val string_of_int32: int32 -> Tot<string>
val string_of_float: float -> Tot<string>
val string_of_char:  char -> Tot<string>
val hex_string_of_byte:  byte -> Tot<string>
val string_of_bytes: array<byte> -> Tot<string>
val bytes_of_string: string -> Tot<array<byte>>
val starts_with: string -> string -> Tot<bool>
val trim_string: string -> Tot<string>
val ends_with: string -> string -> Tot<bool>
val char_at: string -> int -> char
val is_upper: char -> Tot<bool>
val contains: string -> string -> Tot<bool>
val substring_from: string -> int -> string
(* Second argument is a length, not an index. *)
val substring: string -> int -> int -> string
val replace_char: string -> char -> char -> Tot<string>
val replace_chars: string -> char -> string -> Tot<string>
val hashcode: string -> Tot<int>
val compare: string -> string -> Tot<int>
val splitlines: string -> Tot<list<string>>
val split: string -> string -> Tot<list<string>>

type either<'a,'b> =
  | Inl of 'a
  | Inr of 'b

val is_left: either<'a,'b> -> bool
val is_right: either<'a,'b> -> bool
val left: either<'a,'b> -> 'a
val right: either<'a,'b> -> 'b
val find_dup: ('a -> 'a -> bool) -> list<'a> -> option<'a>
val nodups: ('a -> 'a -> bool) -> list<'a> -> bool
val sort_with: ('a -> 'a -> int) -> list<'a> -> list<'a>
val set_eq: ('a -> 'a -> int) -> list<'a> -> list<'a> -> bool
val remove_dups: ('a -> 'a -> bool) -> list<'a> -> list<'a>
val add_unique: ('a -> 'a -> bool) -> 'a -> list<'a> -> list<'a>
val try_find: ('a -> bool) -> list<'a> -> option<'a>
val try_find_i: (int -> 'a -> bool) -> list<'a> -> option<(int * 'a)>
val find_map: list<'a> -> ('a -> option<'b>) -> option<'b>
val try_find_index: ('a -> bool) -> list<'a> -> option<int>
val fold_map: ('a -> 'b -> 'a * 'c) -> 'a -> list<'b> -> 'a * list<'c>
val choose_map: ('a -> 'b -> 'a * option<'c>) -> 'a -> list<'b> -> 'a * list<'c>
val for_all: ('a -> bool) -> list<'a> -> bool
val for_some: ('a -> bool) -> list<'a> -> bool
val forall_exists: ('a -> 'b -> bool) -> list<'a> -> list<'b> -> bool
val multiset_equiv: ('a -> 'b -> bool) -> list<'a> -> list<'b> -> bool
val take: ('a -> bool) -> list<'a> -> list<'a> * list<'a>

(* Variation on fold_left which pushes the list returned by the functional *)
(* on top of the leftover input list *)
val fold_flatten:('a -> 'b -> 'a * list<'b>) -> 'a -> list<'b> -> 'a

val is_some: option<'a> -> Tot<bool>
val must: option<'a> -> 'a
val dflt: 'a -> option<'a> -> Tot<'a>
val find_opt: ('a -> bool) -> list<'a> -> option<'a>
(* FIXME: these functions have the wrong argument order when compared to
 List.map, List.iter, etc. *)
val bind_opt: option<'a> -> ('a -> option<'b>) -> option<'b>
val map_opt: option<'a> -> ('a -> 'b) -> option<'b>
val iter_opt: option<'a> -> ('a -> unit) -> unit

val first_N: int -> list<'a> -> (list<'a> * list<'a>)
val nth_tail: int -> list<'a> -> list<'a>
val prefix_until: ('a -> bool) -> list<'a> -> option<(list<'a> * 'a * list<'a>)>
val prefix: list<'a> -> Tot<(list<'a> * 'a)>

val string_of_unicode: array<byte> -> Tot<string>
val unicode_of_string: string -> Tot<array<byte>>
val incr: ref<int> -> unit
val decr: ref<int> -> unit
val geq: int -> int -> Tot<bool>
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

val get_exec_dir: unit -> string
val expand_environment_variable: string -> string

val physical_equality: 'a -> 'a -> bool
val check_sharing: 'a -> 'a -> string -> unit

val is_letter_or_digit: char -> bool
val is_punctuation: char -> bool
val is_symbol: char -> bool

(* serialization of compiled modules *)
type oWriter = {
    write_byte: byte -> unit;
    write_bool: bool -> unit;
    write_int: int -> unit;
    write_int32: int32 -> unit;
    write_int64: int64 -> unit;
    write_char: char -> unit;
    write_double: double -> unit;
    write_bytearray: array<byte> -> unit;
    write_string: string -> unit;

    close: unit -> unit
}

type oReader = {
    read_byte: unit -> byte;
    read_bool: unit -> bool;
    read_int: unit -> int;
    read_int32: unit -> int32;
    read_int64: unit -> int64;
    read_char: unit -> char;
    read_double: unit -> double;
    read_bytearray: unit -> array<byte>;
    read_string: unit -> string;

    close: unit -> unit
}

val get_owriter: string -> oWriter
val get_oreader: string -> oReader

val monitor_enter: 'a -> unit
val monitor_exit:  'a -> unit
val monitor_wait: 'a -> unit
val monitor_pulse:  'a -> unit
val current_tid: unit -> int
val sleep: int -> unit
val atomically: (unit -> 'a) -> 'a
val spawn: (unit -> unit) -> unit
val print_endline: string -> unit

val map_option: ('a -> 'b) -> option<'a> -> option<'b>

val save_value_to_file: string -> 'a -> unit
val load_value_from_file: string -> option<'a>
val print_exn: exn -> string
val digest_of_file: string -> string
val digest_of_string: string -> string

val ensure_decimal: string -> string

(** Hints. *)
type hint = {
    hint_name: string; //name associated to the top-level term in the source program
    hint_index: int;   //the nth query associated with that top-level term
    fuel:int;  //fuel for unrolling recursive functions
    ifuel:int; //fuel for inverting inductive datatypes
    unsat_core:option<(list<string>)>; //unsat core, if requested
    query_elapsed_time:int //time in milliseconds taken for the query, to decide if a fresh replay is worth it
}

type hints = list<(option<hint>)>

type hints_db = {
    module_digest:string;
    hints: hints
}

val write_hints: string -> hints_db -> unit
val read_hints: string -> option<hints_db>

type json =
| JsonNull
| JsonBool of bool
| JsonInt of int
| JsonStr of string
| JsonList of list<json>
| JsonAssoc of list<(string * json)>

val json_of_string : string -> option<json>
val string_of_json : json -> string

(* Common interface between F#, Ocaml and F* to read and write references *)
(* F# uses native references, while OCaml uses both native references (Pervasives) and FStar_Heap ones *)
val read : ref<'a> -> 'a
val write : ref<'a> -> 'a -> unit
