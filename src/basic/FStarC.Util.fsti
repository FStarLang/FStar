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
module FStarC.Util

(* generic utils *)

open FStarC.Effect
open FStarC.Json
open FStarC.BaseTypes
open FStarC.Array

exception Impos

val max_int: int

type out_channel

val stderr: out_channel
val stdout: out_channel

val open_file_for_writing : string -> ML out_channel
val open_file_for_appending : string -> ML out_channel
val close_out_channel : out_channel -> ML unit

val flush: out_channel -> ML unit

val fprint: out_channel -> string -> list string -> ML unit

(* Adds a newline and flushes *)
val append_to_file: out_channel -> string -> ML unit

val strcat : string -> string -> string
val concat_l : string -> list string -> string

val write_file: fn:string -> contents:string -> ML unit
val copy_file: string -> string -> ML unit
val delete_file: string -> ML unit
val file_get_contents: string -> ML string
val file_get_lines: string -> ML (list string)

(** [mkdir clean mkparents d] a new dir with user read/write.
If clean is set and the directory exists, its contents are deleted and nothing else is done.
If clean is not set and the directory exists, do nothing.
If mkparents is true, the needed parents of the path will be created too, as mkdir -p does.
*)
val mkdir: bool-> bool -> string -> ML unit

val concat_dir_filename: string -> string -> string

type stream_reader
val open_stdin : unit -> ML stream_reader
val read_line: stream_reader -> ML (option string)
val nread : stream_reader -> int -> ML (option string)
val poll_stdin : float -> ML bool

val message_of_exn: exn -> ML string
val trace_of_exn: exn -> ML string
val stack_dump : unit -> ML string

(* Always run finally(), even if work() raises an exception. *)
val finally (finally: unit -> ML unit) (work: unit -> ML 'a) : ML 'a

exception SigInt
type sigint_handler
val sigint_handler_f : (int -> ML unit) -> sigint_handler
val sigint_ignore: sigint_handler
val sigint_raise: sigint_handler
val get_sigint_handler: unit -> ML sigint_handler
val set_sigint_handler: sigint_handler -> ML unit
val with_sigint_handler: sigint_handler -> (unit -> ML 'a) -> ML 'a

type proc
val run_process : string -> string -> list string -> option string -> ML string
val start_process: string -> string -> list string -> (string -> ML bool) -> ML proc
val ask_process: proc -> string -> (*err_handler:*)(unit -> ML string) -> (*stderr_handler:*)(string -> ML unit) -> ML string
val kill_process: proc -> ML unit
val kill_all: unit -> ML unit
val proc_prog : proc -> string
val system_run : string -> ML int (* a less refined launching, implemented by Sys.command *)

val getcwd: unit -> ML string

val int_of_string: string -> ML int
val safe_int_of_string: string -> option int
val int_of_char:   char -> Tot int
val int_of_byte:   byte -> Tot int
val byte_of_char: char -> Tot byte
val char_of_int:   int -> Tot char
val int_of_uint8: uint8 -> Tot int
val uint16_of_int: int -> Tot uint16
val float_of_byte: byte -> Tot float
val float_of_int32: int32 -> Tot float
val float_of_int64: int64 -> Tot float
val float_of_string: string -> Tot float
val int_of_int32: int32 -> Tot int
val int32_of_int:   int -> ML int32 //potentially failing int32 coercion
val show64: int64 -> Tot string
val show32: int32 -> Tot string
val string_of_float: float -> Tot string
val string_of_char:  char -> Tot string
val hex_string_of_byte:  byte -> Tot string
val string_of_bytes: array byte -> Tot string
val bytes_of_string: string -> Tot (array byte)
val base64_encode: string -> ML string
val base64_decode: string -> ML string
val starts_with: long:string -> short:string -> Tot bool
val trim_string: string -> Tot string
val ends_with: long:string -> short:string -> Tot bool
val char_at: string -> int -> ML char
val is_upper: char -> Tot bool
val contains: string -> string -> Tot bool
val substring_from: string -> int -> ML string
val substring: string -> start:int -> len:int -> ML string
val replace_char: string -> char -> char -> Tot string
val replace_chars: string -> char -> string -> Tot string
val hashcode: string -> Tot int
val compare: string -> string -> Tot int
val splitlines: string -> Tot (list string)
val split: str:string -> sep:string -> Tot (list string)

val find_dup: ('a -> 'a -> ML bool) -> list 'a -> ML (option 'a)
val nodups: ('a -> 'a -> ML bool) -> list 'a -> ML bool
val sort_with: ('a -> 'a -> ML int) -> list 'a -> ML (list 'a)

// Removes duplicates according to the given equivalence relation.
// The order is preserved, and the function keeps the *first* duplicate.
val remove_dups: ('a -> 'a -> ML bool) -> list 'a -> ML (list 'a)

val add_unique: ('a -> 'a -> ML bool) -> 'a -> list 'a -> ML (list 'a)
val try_find: ('a -> ML bool) -> list 'a -> ML (option 'a)
val try_find_i: (int -> 'a -> ML bool) -> list 'a -> ML (option (int & 'a))
val find_map: list 'a -> ('a -> ML (option 'b)) -> ML (option 'b)
val try_find_index: ('a -> ML bool) -> list 'a -> ML (option int)
val fold_map: ('a -> 'b -> ML ('a & 'c)) -> 'a -> list 'b -> ML ('a & list 'c)
val choose_map: ('a -> 'b -> ML ('a & option 'c)) -> 'a -> list 'b -> ML ('a & list 'c)
val for_all: ('a -> ML bool) -> list 'a -> ML bool
val for_some: ('a -> ML bool) -> list 'a -> ML bool
val forall_exists: ('a -> 'b -> ML bool) -> list 'a -> list 'b -> ML bool
val multiset_equiv: ('a -> 'b -> ML bool) -> list 'a -> list 'b -> ML bool
val take: ('a -> ML bool) -> list 'a -> ML (list 'a & list 'a)

(* Variation on fold_left which pushes the list returned by the functional *)
(* on top of the leftover input list *)
val fold_flatten:('a -> 'b -> ML ('a & list 'b)) -> 'a -> list 'b -> ML 'a

val first_N: int -> list 'a -> (list 'a & list 'a)
val nth_tail: int -> list 'a -> list 'a
val prefix_until: ('a -> ML bool) -> list 'a -> ML (option (list 'a & 'a & list 'a))
val prefix: list 'a -> Tot (list 'a & 'a)

val string_of_unicode: array byte -> Tot string
val unicode_of_string: string -> Tot (array byte)
val incr: ref int -> ML unit
val decr: ref int -> ML unit
val geq: int -> int -> Tot bool
val for_range: int -> int -> (int -> ML unit) -> ML unit

// Use FStarC.Effect.mk_ref instead
// val mk_ref: 'a -> ref 'a

val exec_name : string
val argv0     : string
val get_exec_dir: unit -> ML string
val get_cmd_args : unit -> ML (list string)
val expand_environment_variable: string -> ML (option string)

val physical_equality: 'a -> 'a -> bool
val check_sharing: 'a -> 'a -> string -> ML unit

val is_letter: char -> bool
val is_digit: char -> bool
val is_letter_or_digit: char -> bool
val is_punctuation: char -> bool
val is_symbol: char -> bool

(* serialization of compiled modules *)
type oWriter = {
    write_byte: byte -> ML unit;
    write_bool: bool -> ML unit;
    write_int: int -> ML unit;
    write_int32: int32 -> ML unit;
    write_int64: int64 -> ML unit;
    write_char: char -> ML unit;
    write_double: double -> ML unit;
    write_bytearray: array byte -> ML unit;
    write_string: string -> ML unit;

    close: unit -> ML unit
}

type oReader = {
    read_byte: unit -> ML byte;
    read_bool: unit -> ML bool;
    read_int: unit -> ML int;
    read_int32: unit -> ML int32;
    read_int64: unit -> ML int64;
    read_char: unit -> ML char;
    read_double: unit -> ML double;
    read_bytearray: unit -> ML (array byte);
    read_string: unit -> ML string;

    close: unit -> ML unit
}

val get_owriter: string -> ML oWriter
val get_oreader: string -> ML oReader

val monitor_enter: 'a -> ML unit
val monitor_exit:  'a -> ML unit
val monitor_wait: 'a -> ML unit
val monitor_pulse:  'a -> ML unit
val with_monitor: 'a -> ('b -> ML 'c) -> 'b -> ML 'c
val current_tid: unit -> ML int
val sleep: int -> ML unit
val atomically: (unit -> ML 'a) -> ML 'a
val spawn: (unit -> ML unit) -> ML unit
val print_endline: string -> ML unit

(* for a filepath, create the parent directory if it doesn't exist (and leading directories too) *)
val maybe_create_parent : string -> ML unit
val save_value_to_file: string -> 'a -> ML unit
val load_value_from_file: string -> ML (option 'a)
val save_2values_to_file: string -> 'a -> 'b -> ML unit
val load_2values_from_file: string -> ML (option ('a & 'b))
val print_exn: exn -> ML string
val digest_of_file: string -> ML string
val digest_of_string: string -> ML string
val touch_file: string -> ML unit (* Precondition: file exists *)

val ensure_decimal: string -> string
val measure_execution_time: string -> (unit -> ML 'a) -> ML 'a
val return_execution_time: (unit -> ML 'a) -> ML ('a & float)

(* Common interface between F#, Ocaml and F* to read and write references *)
(* F# uses native references, while OCaml uses both native references (Pervasives) and FStar_Heap ones *)
val read : ref 'a -> ML 'a
val write : ref 'a -> 'a -> ML unit

(* Marshaling to and from strings *)
val marshal: 'a -> ML string
val unmarshal: string -> ML 'a

val print_array (f: 'a -> string) (s:FStar.ImmutableArray.Base.t 'a) : string 
val array_length (s:FStar.ImmutableArray.Base.t 'a) : int
val array_index (s:FStar.ImmutableArray.Base.t 'a) (i : int) : ML 'a

(* From OCaml's Unix module (simplified).
NOTE: execv and friends are evil on Windows, do not use them. *)
val putenv : string -> string -> ML unit
val create_process : prog:string -> args:(list string) -> ML (*pid:*)int
val waitpid : pid:int -> ML (either int int) // Inl: exited, Inr: killed by signal

val exn_is_enoent (e:exn) : bool
