(*
   Copyright 2008-2026 Microsoft Research

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

(* The Cherry implementation.  The operating system is reached through the
   helpers in ulib/c/cherry.c.  An external cannot raise, so one that fails
   records a message, which [check] raises as [Failure].

   Differences from the OCaml build (see doc/ref/cherry.md):
   - there are no threads: [spawn] fails, the monitors do nothing, and
     [ask_process] writes its input before reading the answer;
   - a handler set with [sigint_handler_f] or [sigint_raise] cannot run, since
     F* code cannot run in a C signal handler: SIGINT gets its default
     behaviour and ends the program;
   - values cannot be marshalled: the [save_*] functions and [marshal] fail,
     the [load_*] functions return [None];
   - [hashcode] is FNV-1a, [trace_of_exn] and [stack_dump] are empty, and
     [physical_equality] compares the bits of its arguments, so it may say
     [false] for two copies of the same unboxed value;
   - [waitpid] reports a signal by its POSIX number. *)

open FStarC.Effect
open FStarC.Json
open FStarC.BaseTypes
module A = FStarC.Array
module I = FStarC.SmallInt
module L = FStarC.List
module S = FStarC.String
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
module I64 = FStar.Int64
module F = FStar.Float64
module IA = FStar.ImmutableArray

(* The total functions are not defined on every input ([float_of_string] on
   a malformed float, [prefix] on an empty list, ...).  Outside their domain
   they have no case, or an unreachable one, which F* accepts because the
   compiler is not verified; Cherry's debug mode reports such a call
   (cherry.md, "Debug mode"). *)
#set-options "--admit_smt_queries true"

private let unsupported (#a:Type) (what:string) : ML a =
  failwith ("FStarC.Util." ^ what ^ " is not supported by the Cherry backend")

(* In ulib/c/cherry.c. *)
[@@custard_extern "cherry_io_error"]
private assume val io_error : unit -> ML string
[@@custard_extern "cherry_argc"]
private assume val c_argc : unit -> int
[@@custard_extern "cherry_argv"]
private assume val c_argv : int -> string
[@@custard_extern "cherry_chan_open"]
private assume val chan_open : string -> U32.t -> ML U64.t
[@@custard_extern "cherry_chan_close"]
private assume val chan_close : U64.t -> ML unit
[@@custard_extern "cherry_chan_close_fd"]
private assume val chan_close_fd : U64.t -> ML unit
[@@custard_extern "cherry_chan_flush"]
private assume val chan_flush : U64.t -> ML unit
[@@custard_extern "cherry_chan_output"]
private assume val chan_output : U64.t -> string -> ML unit
[@@custard_extern "cherry_chan_input_line"]
private assume val chan_input_line : U64.t -> ML string
[@@custard_extern "cherry_chan_eof"]
private assume val chan_eof : U64.t -> ML bool
[@@custard_extern "cherry_chan_read"]
private assume val chan_read : U64.t -> U64.t -> ML string
[@@custard_extern "cherry_chan_read_nonblock"]
private assume val chan_read_nonblock : U64.t -> U64.t -> ML string
[@@custard_extern "cherry_poll_stdin"]
private assume val c_poll_stdin : float -> ML bool
[@@custard_extern "cherry_mkdir"]
private assume val c_mkdir : string -> ML int
[@@custard_extern "cherry_set_umask"]
private assume val set_umask : unit -> ML unit
[@@custard_extern "cherry_remove_all_in_dir"]
private assume val c_remove_all_in_dir : string -> ML unit
[@@custard_extern "cherry_file_exists"]
private assume val file_exists : string -> ML bool
[@@custard_extern "cherry_is_directory"]
private assume val is_directory : string -> ML bool
[@@custard_extern "cherry_dirname"]
private assume val dirname : string -> string
[@@custard_extern "cherry_copy_file"]
private assume val c_copy_file : string -> string -> ML unit
[@@custard_extern "cherry_remove_file"]
private assume val c_remove_file : string -> ML unit
[@@custard_extern "cherry_rename_file"]
private assume val c_rename_file : string -> string -> ML unit
[@@custard_extern "cherry_file_get_contents"]
private assume val c_file_get_contents : string -> ML string
[@@custard_extern "cherry_touch_file"]
private assume val c_touch_file : string -> ML unit
[@@custard_extern "cherry_getcwd"]
private assume val c_getcwd : unit -> ML string
[@@custard_extern "cherry_exec_name"]
private assume val c_exec_name : unit -> string
[@@custard_extern "cherry_has_env"]
private assume val has_env : string -> ML bool
[@@custard_extern "cherry_getenv"]
private assume val getenv : string -> ML string
[@@custard_extern "cherry_setenv"]
private assume val setenv : string -> string -> ML unit
[@@custard_extern "cherry_proc_arg"]
private assume val proc_arg : string -> ML unit
[@@custard_extern "cherry_spawn"]
private assume val c_spawn : string -> bool -> ML int
[@@custard_extern "cherry_spawned_chan"]
private assume val spawned_chan : U32.t -> ML U64.t
[@@custard_extern "cherry_kill"]
private assume val c_kill : int -> ML unit
[@@custard_extern "cherry_waitpid"]
private assume val c_waitpid : int -> ML int
[@@custard_extern "cherry_system"]
private assume val c_system : string -> ML int
[@@custard_extern "cherry_set_sigint"]
private assume val c_set_sigint : U32.t -> ML unit
[@@custard_extern "cherry_sleep_ms"]
private assume val c_sleep_ms : int -> ML unit
[@@custard_extern "cherry_cpu_time"]
private assume val cpu_time : unit -> ML float
[@@custard_extern "cherry_string_of_float"]
private assume val c_string_of_float : float -> string
[@@custard_extern "cherry_float_of_string_ok"]
private assume val c_float_of_string_ok : string -> bool
[@@custard_extern "cherry_float_of_string"]
private assume val c_float_of_string : string -> float
[@@custard_extern "cherry_exn_to_string"]
private assume val exn_to_string : exn -> string
[@@custard_extern "cherry_base64_encode"]
private assume val c_base64_encode : string -> string
[@@custard_extern "cherry_base64_ok"]
private assume val c_base64_ok : string -> bool
[@@custard_extern "cherry_base64_decode"]
private assume val c_base64_decode : string -> string
[@@custard_extern "cherry_md5_hex"]
private assume val md5_hex : string -> string
[@@custard_extern "cherry_md5_hex_file"]
private assume val md5_hex_file : string -> ML string

(* A macro in ulib/c/cherry.h comparing the bits of its arguments. *)
[@@custard_extern "cherry_physical_equality"; custard_c_header "cherry.h"]
private assume val phys_eq (#a:Type) : a -> a -> bool

(* Raises the error the last external recorded, if any. *)
private let check () : ML unit =
  let e = io_error () in
  if e <> "" then failwith e

(* Forgets it. *)
private let clear () : ML unit = let _ = io_error () in ()

(* Bytes of strings. *)
private let blen (s:string) : int = I.to_int (S.byte_length s)
private let byte (s:string) (i:int) : int = I.to_int (S.byte_at s (I.of_int i))
private let bsub (s:string) (i j:int) : string = S.byte_substring s (I.of_int i) (I.of_int j)

(* Whether [sub] occurs in [s] at [i]. *)
private let rec matches_from (s sub:string) (i j n:int) : Tot bool (decreases (n - j)) =
  if j >= n then true
  else if byte s (i + j) <> byte sub j then false
  else matches_from s sub i (j + 1) n

private let matches_at (s sub:string) (i:int) : bool =
  let n = blen sub in
  0 <= i && i + n <= blen s && matches_from s sub i 0 n

let max_int = 4611686018427387903

type out_channel = U64.t

let stderr = 2UL
let stdout = 1UL

private let not_a_channel = 0xFFFFFFFFFFFFFFFFUL

private let open_chan (fn:string) (mode:U32.t) : ML U64.t =
  let h = chan_open fn mode in
  if h = not_a_channel then failwith (io_error ()) else h

let open_file_for_writing fn = open_chan fn 1ul

let open_file_for_appending fn = open_chan fn 2ul

let close_out_channel h = chan_close h; check ()

let flush h = chan_flush h; check ()

private let output_string (h:out_channel) (s:string) : ML unit = chan_output h s; check ()

private let pr (s:string) : ML unit = output_string stdout s

let fprint oc fmt args = output_string oc (FStarC.Format.fmt fmt args)

let append_to_file c s =
  output_string c s;
  output_string c "\n";
  flush c

let strcat s1 s2 = s1 ^ s2

let concat_l sep l = S.concat sep l

private type in_channel = U64.t

private let open_in (fn:string) : ML in_channel = open_chan fn 0ul

private let close_in (h:in_channel) : ML unit = chan_close h; check ()

private let input_line_opt (h:in_channel) : ML (option string) =
  let l = chan_input_line h in
  check ();
  if chan_eof h then None else Some l

private
let rec init (#a:Type) (l:list a) : ML (list a) =
  match l with
  | [] -> failwith "init: empty list"
  | [_] -> []
  | h :: t -> h :: init t

private
let rec drop_while (f:string -> bool) (xs:list string) : list string =
  match xs with
  | [] -> []
  | x :: xs -> if f x then drop_while f xs else x :: xs

private
let path_parent (fn:string) : ML string =
  (* Components of the path, without empty trailing ones, so that we
     interpret a/b/c/ as a/b/c *)
  let cs = List.Tot.rev (drop_while (fun s -> s = "") (List.Tot.rev (S.split ['/'] fn))) in
  (* Remove the last component to get the parent *)
  S.concat "/" (init cs)

(* 0 if [nm] was created, 1 if it exists already, 2 if its parent does not *)
private let try_mkdir (nm:string) : ML int =
  let r = c_mkdir nm in
  if r = 3 then failwith (io_error ()) else r

private let unix_mkdir (nm:string) : ML unit =
  match try_mkdir nm with
  | 0 -> ()
  | 1 -> failwith (nm ^ ": File exists")
  | _ -> failwith (nm ^ ": No such file or directory")

private let remove_all_in_dir (nm:string) : ML unit = c_remove_all_in_dir nm; check ()

private
let rec mkdir' (clean mkparents:bool) (nm:string) : ML unit =
  set_umask ();
  match try_mkdir nm with
  | 0 -> ()
  | 1 -> if clean then remove_all_in_dir nm
  | _ ->
    (* The parent does not exist: create it, if allowed, and retry *)
    if mkparents && S.index_of nm '/' <> -1 then
      mkdir' false true (path_parent nm);
    unix_mkdir nm

private let is_existing_dir (d:string) : ML bool = file_exists d && is_directory d

private
let create_parent (fname:string) : ML unit =
  let d = dirname fname in
  if is_existing_dir d then () else mkdir' false true d

let write_file fn s =
  create_parent fn;
  let fh = open_file_for_writing fn in
  append_to_file fh s;
  close_out_channel fh

let copy_file a b = c_copy_file a b; check ()

let delete_file f = c_remove_file f; check ()

let file_get_contents f =
  let s = c_file_get_contents f in
  check ();
  s

let file_get_lines f =
  let ic = open_in f in
  let rec aux (acc:list string) : ML (list string) =
    match input_line_opt ic with
    | None -> acc
    | Some l -> aux (l :: acc)
  in
  let l = aux [] in
  close_in ic;
  List.Tot.rev l

let mkdir clean mkparents nm = mkdir' clean mkparents nm

(* As OCaml's Filename.concat. *)
let concat_dir_filename d f =
  let n = blen d in
  if n = 0 || byte d (n - 1) = 47 then d ^ f else d ^ "/" ^ f

type stream_reader = U64.t

let open_stdin () = 0UL

let read_line s =
  let l = chan_input_line s in
  clear ();
  if chan_eof s then None else Some l

let nread s n =
  if n < 0 then None else
  let r = chan_read s (U64.uint_to_t n) in
  clear ();
  if chan_eof s then None else Some r

let poll_stdin f = c_poll_stdin f

(* [Name("message")], with OCaml's name for [Failure]. *)
private let exn_message (e:exn) : string =
  let s = exn_to_string e in
  let eff = "FStarC.Effect.Failure" in
  if matches_at s eff 0 then bsub s 14 (blen s) else s

let message_of_exn e = exn_message e

let trace_of_exn _ = ""

let stack_dump () = ""

let finally h f =
  let r = try f () with | e -> h (); raise e in
  h ();
  r

private noeq
type sig_behavior =
  | SigDefault
  | SigIgnore
  | SigHandle of (int -> ML unit)

type sigint_handler = sig_behavior

let sigint_handler_f f = SigHandle f

let sigint_ignore = SigIgnore

private
let sigint_delay : ref I.t = mk_ref I.zero

private
let sigint_pending : ref bool = mk_ref false

private
let raise_sigint () : ML unit =
  sigint_pending := false;
  raise SigInt

private
let raise_sigint_maybe_delay (_:int) : ML unit =
  if !sigint_delay = I.zero
  then raise_sigint ()
  else sigint_pending := true

let sigint_raise = SigHandle raise_sigint_maybe_delay

private
let cur_sigint_handler : ref sigint_handler = mk_ref SigDefault

(* A handler cannot run (see the top of this file): SIGINT keeps its default
   behaviour. *)
private let set_sigint_behavior (h:sigint_handler) : ML unit =
  match h with
  | SigIgnore -> c_set_sigint 1ul
  | _ -> c_set_sigint 0ul

let get_sigint_handler () = !cur_sigint_handler

let set_sigint_handler h =
  cur_sigint_handler := h;
  set_sigint_behavior h

let with_sigint_handler handler f =
  let original_handler = !cur_sigint_handler in
  finally
    (fun () -> set_sigint_behavior original_handler)
    (fun () -> set_sigint_handler handler; f ())

private noeq
type proc_rec = {
  pid : int;
  inc : in_channel;  (* where we read from, so the process's stdout *)
  errc : in_channel; (* the process's stderr *)
  outc : out_channel; (* the process's stdin *)
  killed : ref bool;
  stop_marker : option (string -> ML bool);
  id : string;
  prog : string;
}

type proc = proc_rec

private
let all_procs : ref (list proc) = mk_ref []

(* Starts [prog] with pipes for its stdin, stdout and stderr *)
private
let create_piped_process (prog:string) (args:list string) : ML (int & in_channel & in_channel & out_channel) =
  proc_arg prog;
  L.iter proc_arg args;
  let pid = c_spawn prog true in
  if pid < 0 then failwith (io_error ());
  (pid, spawned_chan 0ul, spawned_chan 1ul, spawned_chan 2ul)

private
let start_process' (id prog:string) (args:list string) (stop_marker:option (string -> ML bool)) : ML proc =
  let pid, inc, errc, outc = create_piped_process prog args in
  let proc = {
    pid; inc; errc; outc;
    killed = mk_ref false;
    stop_marker;
    id = prog ^ ":" ^ id;
    prog;
  } in
  all_procs := proc :: !all_procs;
  proc

private
let kill_process' (p:proc) : ML unit =
  if not !p.killed then begin
    (* Close the fds directly, without flushing, which could wait for p to
       read again. *)
    chan_close_fd p.inc;
    chan_close_fd p.errc;
    chan_close_fd p.outc;
    (* The process may be gone already. *)
    c_kill p.pid;
    (* Avoid zombie processes. *)
    let _ = c_waitpid p.pid in
    clear ();
    p.killed := true
  end

(* The process must have finished without reading its input if this fails *)
private let try_output_string (oc:out_channel) (s:string) : ML unit =
  chan_output oc s; clear ()

private let try_flush_and_close (oc:out_channel) : ML unit =
  chan_flush oc; clear ();
  chan_close oc; clear ()

private let read_all (ic:in_channel) : ML string =
  let s = chan_read ic not_a_channel in
  clear ();
  s

let run_process id prog args stdin =
  let p = start_process' id prog args None in
  (match stdin with
   | None -> ()
   | Some str -> try_output_string p.outc str);
  try_flush_and_close p.outc;
  let s = read_all p.inc in
  kill_process' p;
  s

let start_process id prog args stop_marker =
  start_process' id prog args (Some stop_marker)

private let channel_read_all_nonblock (c:in_channel) : ML string =
  chan_read_nonblock c 1024UL

(* As BatString.trim: ' ', '\t', '\n', '\r' and '\012'. *)
private let is_space (b:int) : bool = b = 32 || b = 9 || b = 10 || b = 13 || b = 12

private let rec skip_space (s:string) (i n:int) : Tot int (decreases (n - i)) =
  if i < n && is_space (byte s i) then skip_space s (i + 1) n else i

private let rec skip_space_back (s:string) (i j:int) : Tot int (decreases (j - i)) =
  if i < j && is_space (byte s (j - 1)) then skip_space_back s i (j - 1) else j

private let trim (s:string) : string =
  let n = blen s in
  let i = skip_space s 0 n in
  bsub s i (skip_space_back s i n)

(* Read stderr and call the handler if anything is in there. *)
private
let handle_stderr (p:proc) (h:string -> ML unit) : ML unit =
  let se = channel_read_all_nonblock p.errc in
  if se <> "" then h (trim se)

(* Without threads, the input is written in full before [reader_fn] reads
   the answer: a process that answers before it has read all of its input
   can fill the pipe and deadlock us. *)
private
let process_read_async (outc:out_channel) (stdin:string) (reader_fn:(unit -> ML unit) -> ML unit) : ML unit =
  output_string outc stdin;
  flush outc;
  reader_fn (fun () -> ())

private
type read_result = | EOF | SIGINT

let ask_process p stdin exn_handler stderr_handler =
  let result : ref (option read_result) = mk_ref None in
  let out : ref (list string) = mk_ref [] in
  let stop_marker (s:string) : ML bool = match p.stop_marker with Some f -> f s | None -> false in
  let reader_fn (signal_fn:unit -> ML unit) : ML unit =
    let rec loop () : ML unit =
      match input_line_opt p.inc with
      | None -> result := Some EOF
      | Some line ->
        let line = trim line in
        if not (stop_marker line) then begin
          out := (line ^ "\n") :: !out;
          loop ()
        end
    in
    (try loop () with | SigInt -> result := Some SIGINT);
    signal_fn ()
  in
  try
    handle_stderr p stderr_handler;
    process_read_async p.outc stdin reader_fn;
    handle_stderr p stderr_handler;
    (match !result with
     | Some EOF -> kill_process' p; out := exn_handler () :: !out
     | Some SIGINT -> raise SigInt
     | None -> ());
    S.concat "" (List.Tot.rev !out)
  with
  | e ->
    kill_process' p;
    raise e

let kill_process p = kill_process' p

let kill_all () = L.iter kill_process' !all_procs

let proc_prog p = p.prog

let system_run cmd = c_system cmd

let getcwd () =
  let s = c_getcwd () in
  check ();
  s

(* As Zarith's Z.of_string: an optional sign, an optional 0x, 0o or 0b
   prefix, and digits, possibly separated by underscores. *)
private let digit_value (b:int) : int =
  if 48 <= b && b <= 57 then b - 48
  else if 97 <= b && b <= 122 then b - 87
  else if 65 <= b && b <= 90 then b - 55
  else 99

private let rec parse_digits (s:string) (i n base acc:int) : Tot (option int) (decreases (n - i)) =
  if i >= n then Some acc
  else
    let b = byte s i in
    if b = 95 then parse_digits s (i + 1) n base acc
    else
      let d = digit_value b in
      if d < base then parse_digits s (i + 1) n base (acc * base + d) else None

private let parse_int (s:string) : option int =
  let n = blen s in
  let at (i:int) : int = if i < n then byte s i else -1 in
  let neg, i = if at 0 = 45 then true, 1 else if at 0 = 43 then false, 1 else false, 0 in
  let base, i =
    if at i <> 48 then 10, i
    else
      let p = at (i + 1) in
      if p = 120 || p = 88 then 16, i + 2
      else if p = 111 || p = 79 then 8, i + 2
      else if p = 98 || p = 66 then 2, i + 2
      else 10, i
  in
  match parse_digits s i n base 0 with
  | Some k -> Some (if neg then - k else k)
  | None -> None

let int_of_string s =
  match parse_int s with
  | Some k -> k
  | None -> failwith "Z.of_string: invalid digit"

let safe_int_of_string x = if x = "" then None else parse_int x

let int_of_char c = U32.v (FStar.Char.u32_of_char c)

let int_of_byte b = U8.v b

let byte_of_char c = U8.uint_to_t (int_of_char c % 256)

(* U+FFFD if [n] is not a code point. *)
let char_of_int n =
  if (0 <= n && n < 0xd7ff) || (0xe000 <= n && n <= 0x10ffff)
  then FStar.Char.char_of_u32 (U32.uint_to_t n)
  else FStar.Char.char_of_u32 0xFFFDul

let int_of_uint8 x = U8.v x

let uint16_of_int n = U16.uint_to_t (n % 65536)

let float_of_byte b = float_of_float64 (F.of_int (I64.int_to_t (U8.v b)))

let float_of_int32 x = float_of_float64 (F.of_int (I64.int_to_t (I32.v x)))

let float_of_int64 x = float_of_float64 (F.of_int x)

let float_of_string s =
  if c_float_of_string_ok s then c_float_of_string s
  else false_elim ()

let int_of_int32 x = I32.v x

(* Wraps around, as OCaml's Int32.of_int. *)
let int32_of_int n =
  let m = n % 0x100000000 in
  I32.int_to_t (if m >= 0x80000000 then m - 0x100000000 else m)

let string_of_float f = c_string_of_float f

let string_of_char c = S.string_of_char c

private let hex_digit (n:int) : string =
  bsub "0123456789abcdef" n (n + 1)

let hex_string_of_byte b =
  let n = U8.v b in
  hex_digit (n / 16) ^ hex_digit (n % 16)

let base64_encode s = c_base64_encode s

let base64_decode s =
  if c_base64_ok s then c_base64_decode s else failwith "Invalid_char"

let starts_with long short = matches_at long short 0

let trim_string s = trim s

let ends_with long short = matches_at long short (blen long - blen short)

let char_at s i = S.get s i

let is_upper c = I.(of_char c >= of_char 'A' && of_char c <= of_char 'Z')

private let rec contains_from (s sub:string) (i last:int) : Tot bool (decreases (last + 1 - i)) =
  if i > last then false
  else if matches_at s sub i then true
  else contains_from s sub (i + 1) last

let contains s sub = contains_from s sub 0 (blen s - blen sub)

(* Bytes, as BatString.tail and String.sub. *)
let substring_from s i =
  if i < 0 then failwith "String.tail" else bsub s i (blen s)

let substring s i len =
  if i < 0 || len < 0 || i + len > blen s then failwith "String.sub / Bytes.sub"
  else bsub s i (i + len)

let replace_char s c1 c2 =
  S.string_of_list (List.Tot.map (fun x -> if x = c1 then c2 else x) (S.list_of_string s))

private
let rec replace_bytes (s:string) (b:int) (rep:string) (n start i:int) (acc:list string)
  : Tot (list string) (decreases (n - i)) =
  if i >= n then bsub s start n :: acc
  else if byte s i = b then replace_bytes s b rep n (i + 1) (i + 1) (rep :: bsub s start i :: acc)
  else replace_bytes s b rep n start (i + 1) acc

let replace_chars s c rep =
  S.concat "" (List.Tot.rev (replace_bytes s (int_of_char c) rep (blen s) 0 0 []))

(* FNV-1a, in 30 bits as OCaml's hashes. *)
private let rec fnv (s:string) (i n:int) (h:U32.t) : Tot U32.t (decreases (n - i)) =
  if i >= n then h
  else fnv s (i + 1) n (U32.mul_mod (U32.logxor h (U32.uint_to_t (byte s i))) 16777619ul)

let hashcode s = U32.v (fnv s 0 (blen s) 2166136261ul) % 0x40000000

let compare s1 s2 = S.compare s1 s2

let splitlines s = if s = "" then [""] else S.split_on_string s "\n"

let split s sep = if s = "" then [""] else S.split_on_string s sep

let find_dup #a f l =
  let rec aux (l:list a) : ML (option a) =
    match l with
    | hd :: tl ->
      let hds, tl' = L.partition (f hd) tl in
      (match hds with
       | [] -> aux tl'
       | _ -> Some hd)
    | [] -> None
  in
  aux l

let nodups f l = None? (find_dup f l)

let sort_with f l = L.sortWith f l

let remove_dups #a f l =
  let rec aux (out l:list a) : ML (list a) =
    match l with
    | hd :: tl -> if L.existsb (f hd) out then aux out tl else aux (hd :: out) tl
    | [] -> List.Tot.rev out
  in
  aux [] l

let add_unique f x l = if L.existsb (f x) l then l else x :: l

let try_find f l = L.tryFind f l

let rec find_map l f =
  match l with
  | [] -> None
  | x :: tl ->
    match f x with
    | None -> find_map tl f
    | y -> y

let try_find_index #a f l =
  let rec aux (i:int) (l:list a) : ML (option int) =
    match l with
    | [] -> None
    | hd :: tl -> if f hd then Some i else aux (i + 1) tl
  in
  aux 0 l

let fold_map #a #b #c f state s =
  let rec aux (state:a) (acc:list c) (s:list b) : ML (a & list c) =
    match s with
    | [] -> state, List.Tot.rev acc
    | x :: s -> let state, v = f state x in aux state (v :: acc) s
  in
  aux state [] s

let choose_map #a #b #c f state s =
  let rec aux (state:a) (acc:list c) (s:list b) : ML (a & list c) =
    match s with
    | [] -> state, List.Tot.rev acc
    | x :: s ->
      match f state x with
      | state, None -> aux state acc s
      | state, Some v -> aux state (v :: acc) s
  in
  aux state [] s

let for_all f l = L.for_all f l

let for_some f l = L.existsb f l

let forall_exists rel l1 l2 = for_all (fun x -> for_some (rel x) l2) l1

let multiset_equiv rel l1 l2 =
  List.Tot.length l1 = List.Tot.length l2 && forall_exists rel l1 l2

let take #a p l =
  let rec aux (acc l':list a) : ML (list a & list a) =
    match l' with
    | [] -> l, []
    | x :: xs -> if p x then aux (x :: acc) xs else List.Tot.rev acc, x :: xs
  in
  aux [] l

let rec fold_flatten f acc l =
  match l with
  | [] -> acc
  | x :: xs -> let acc, xs' = f acc x in fold_flatten f acc (List.Tot.append xs' xs)

let first_N #a n l =
  let rec aux (acc:list a) (i:int) (l:list a) : Tot (list a & list a) (decreases l) =
    if i = n then List.Tot.rev acc, l
    else match l with
      | h :: tl -> aux (h :: acc) (i + 1) tl
  in
  aux [] 0 l

let rec nth_tail n l =
  if n = 0 then l
  else match l with
    | _ :: tl -> nth_tail (n - 1) tl

let prefix_until #a f l =
  let rec aux (prefix l:list a) : ML (option (list a & a & list a)) =
    match l with
    | [] -> None
    | hd :: tl -> if f hd then Some (List.Tot.rev prefix, hd, tl) else aux (hd :: prefix) tl
  in
  aux [] l

let prefix l =
  match List.Tot.rev l with
  | hd :: tl -> List.Tot.rev tl, hd

let incr r = r := !r + 1

let decr r = r := !r - 1

let geq i j = i >= j

let rec for_range lo hi f =
  if lo > hi then ()
  else begin
    f lo;
    for_range (lo + 1) hi f
  end

(* The executable with all symbolic links resolved: F* finds its library
   relative to it. *)
let exec_name = c_exec_name ()

let argv0 = c_argv 0

let get_exec_dir () = dirname exec_name

let get_cmd_args () =
  let rec aux (i:int) (acc:list string) : ML (list string) =
    if i < 0 then acc else aux (i - 1) (c_argv i :: acc)
  in
  aux (c_argc () - 1) []

let expand_environment_variable x =
  if has_env x then Some (getenv x) else None

let physical_equality x y = phys_eq x y

let check_sharing a b msg =
  if physical_equality a b
  then pr ("Sharing OK: " ^ msg ^ "\n")
  else pr ("Sharing broken in " ^ msg ^ "\n")

let is_letter c =
  let n = int_of_char c in
  (65 <= n && n <= 90) || (97 <= n && n <= 122)

let is_digit c =
  let n = int_of_char c in
  48 <= n && n <= 57

let is_letter_or_digit c = is_letter c || is_digit c

(* Modeled after: Char.IsPunctuation in .NET
   (http://www.dotnetperls.com/char-ispunctuation) *)
let is_punctuation c =
  List.Tot.mem c ['!'; '"'; '#'; '%'; '&'; '\''; '('; ')'; '*'; ','; '-'; '.'; '/';
                  ':'; ';'; '?'; '@'; '['; '\\'; ']'; '_'; '{'; '}']

(* As BatChar.is_symbol. *)
let is_symbol c =
  List.Tot.mem c ['!'; '#'; '$'; '%'; '&'; '*'; '+'; '-'; '/'; ':'; '<'; '=';
                  '>'; '?'; '@'; '\\'; '^'; '|'; '~']

let monitor_enter _ = ()

let monitor_exit _ = ()

let monitor_wait _ = ()

let monitor_pulse _ = ()

(* This function only protects against signals *)
private
let atomically' (#a:Type) (f:unit -> ML a) : ML a =
  finally
    (fun () ->
      sigint_delay := I.(!sigint_delay - one);
      if !sigint_pending && !sigint_delay = I.zero then
        raise_sigint ())
    (fun () ->
      sigint_delay := I.(!sigint_delay + one);
      f ())

let with_monitor _ f x = atomically' (fun () -> f x)

let current_tid _ = 0

let sleep n = c_sleep_ms n

let atomically f = atomically' f

let spawn _ = unsupported "spawn"

let print_endline s =
  chan_output stdout (s ^ "\n");
  chan_flush stdout;
  check ()

let maybe_create_parent fname = create_parent fname

let save_value_to_file _ _ = unsupported "save_value_to_file"

let load_value_from_file _ = None

let save_2values_to_file _ _ _ = unsupported "save_2values_to_file"

let load_2values_from_file _ = None

let save_3values_to_file _ _ _ _ = unsupported "save_3values_to_file"

let load_1value_from_file3 _ = None

let load_2values_from_file3 _ = None

let load_3rd_value_from_file3 _ = None

let print_exn e = exn_message e

private
let digest_cache : ref (list (string & string)) = mk_ref []

let digest_of_file fname =
  match List.Tot.assoc fname !digest_cache with
  | Some dig -> dig
  | None ->
    let dig = md5_hex_file fname in
    check ();
    digest_cache := (fname, dig) :: !digest_cache;
    dig

let digest_of_string s = md5_hex s

(* Sets access and modification times to current time *)
let touch_file fname = c_touch_file fname; check ()

let ensure_decimal s =
  match parse_int s with
  | Some k -> string_of_int k
  | None -> false_elim ()

(* Milliseconds since [t], a [cpu_time] *)
private let ms_since (t:float) : ML float =
  let now = float64_of_float (cpu_time ()) in
  float_of_float64 (F.mul (F.of_int 1000L) (F.sub now (float64_of_float t)))

let measure_execution_time tag f =
  let t = cpu_time () in
  let retv = f () in
  let ms = ms_since t in
  pr ("Execution time of " ^ tag ^ ": " ^ string_of_float ms ^ " ms\n");
  retv

let return_execution_time f =
  let t = cpu_time () in
  let retv = f () in
  (retv, ms_since t)

let read r = !r

let write r v = r := v

let marshal _ = unsupported "marshal"

let unmarshal _ = unsupported "unmarshal"

private
let rec print_elems (#a:Type) (f:a -> string) (s:IA.t a) (i:nat) (acc:list string)
  : Tot (list string) (decreases (IA.length s - i)) =
  if i >= IA.length s then List.Tot.rev acc
  else print_elems f s (i + 1) (f (IA.index s i) :: acc)

let print_array f s = "[| " ^ S.concat "; " (print_elems f s 0 []) ^ " |]"

let array_length s = IA.length s

let array_index s i =
  if 0 <= i && i < IA.length s then IA.index s i
  else failwith "index out of bounds"

let putenv x v = setenv x v; check ()

let create_process prog args =
  L.iter proc_arg args;
  let pid = c_spawn prog false in
  if pid < 0 then failwith (io_error ()) else pid

let waitpid pid =
  let r = c_waitpid pid in
  if r < 0 then failwith (io_error ())
  else if r >= 256 then Inr (r - 256)
  else Inl r

let exn_is_enoent _ = false
