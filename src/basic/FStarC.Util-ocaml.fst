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

open FStarC.Effect
open FStarC.Json
open FStarC.BaseTypes
module A = FStarC.Array
module I = FStarC.SmallInt
module L = FStarC.List
module S = FStarC.String

(* OCaml implementation.  The targets name OCaml's standard library through
   [Stdlib] where this module defines the same name. *)

[@@custard_extern "Stdlib.failwith"]
private assume val fail (#a:Type) : string -> a

[@@custard_extern "Stdlib.print_string"]
private assume val pr : string -> ML unit

[@@custard_extern "(Z.of_int Stdlib.max_int)"]
let max_int = admit ()

[@@custard_extern "Stdlib.out_channel"]
private assume new type ocaml_out_channel : Type0

type out_channel = ocaml_out_channel

[@@custard_extern "Stdlib.stderr"]
let stderr = admit ()

[@@custard_extern "Stdlib.stdout"]
let stdout = admit ()

[@@custard_extern "Stdlib.open_out_bin"]
let open_file_for_writing _ = admit ()

[@@custard_extern "(fun fn -> Stdlib.open_out_gen [Stdlib.Open_append; Stdlib.Open_wronly; Stdlib.Open_creat; Stdlib.Open_binary] 0o644 fn)"]
let open_file_for_appending _ = admit ()

[@@custard_extern "Stdlib.close_out"]
let close_out_channel _ = admit ()

[@@custard_extern "Stdlib.flush"]
let flush _ = admit ()

[@@custard_extern "Stdlib.output_string"]
private assume val output_string : out_channel -> string -> ML unit

let fprint oc fmt args = output_string oc (FStarC.Format.fmt fmt args)

let append_to_file c s =
  output_string c s;
  output_string c "\n";
  flush c

let strcat s1 s2 = s1 ^ s2

let concat_l sep l = S.concat sep l

[@@custard_extern "Stdlib.in_channel"]
private assume new type in_channel : Type0

[@@custard_extern "Stdlib.open_in"]
private assume val open_in : string -> ML in_channel

[@@custard_extern "Stdlib.open_in_bin"]
private assume val open_in_bin : string -> ML in_channel

[@@custard_extern "Stdlib.close_in"]
private assume val close_in : in_channel -> ML unit

[@@custard_extern "(fun ic -> try Some (Stdlib.input_line ic) with End_of_file -> None)"]
private assume val input_line_opt : in_channel -> ML (option string)

[@@custard_extern "(fun h f -> BatPervasives.finally h f ())"]
private assume val finally' (#a:Type) : (unit -> ML unit) -> (unit -> ML a) -> ML a

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

[@@custard_extern "(fun () -> match Sys.os_type with \"Unix\" -> Stdlib.ignore (Unix.umask 0o002) | _ -> ())"]
private assume val set_umask : unit -> ML unit

[@@custard_extern "(fun nm -> Unix.mkdir nm 0o777)"]
private assume val unix_mkdir : string -> ML unit

(* 0 if [nm] was created, 1 if it exists already, 2 if its parent does not *)
[@@custard_extern "(fun nm -> try Unix.mkdir nm 0o777; Z.zero with Unix.Unix_error (Unix.EEXIST, _, _) -> Z.one | Unix.Unix_error (Unix.ENOENT, _, _) -> Z.of_int 2)"]
private assume val try_mkdir : string -> ML int

[@@custard_extern "(fun nm -> Array.iter Sys.remove (Array.map (Filename.concat nm) (Sys.readdir nm)))"]
private assume val remove_all_in_dir : string -> ML unit

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

[@@custard_extern "(fun d -> Sys.file_exists d && Sys.is_directory d)"]
private assume val is_existing_dir : string -> ML bool

[@@custard_extern "Filename.dirname"]
private assume val dirname : string -> string

private
let create_parent (fname:string) : ML unit =
  let d = dirname fname in
  if is_existing_dir d then () else mkdir' false true d

let write_file fn s =
  create_parent fn;
  let fh = open_file_for_writing fn in
  append_to_file fh s;
  close_out_channel fh

(* see https://ocaml.github.io/ocamlunix/ocamlunix.html#sec33 *)
[@@custard_extern "(fun input_name output_name -> let buffer = Bytes.create 8192 in let fd_in = Unix.openfile input_name [Unix.O_RDONLY] 0 in let fd_out = Unix.openfile output_name [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC] 0o666 in let rec copy_loop () = match Unix.read fd_in buffer 0 8192 with 0 -> () | r -> Stdlib.ignore (Unix.write fd_out buffer 0 r); copy_loop () in copy_loop (); Unix.close fd_in; Unix.close fd_out)"]
let copy_file _ _ = admit ()

[@@custard_extern "Sys.remove"]
let delete_file _ = admit ()

[@@custard_extern "(fun f -> let ic = Stdlib.open_in_bin f in let s = Stdlib.really_input_string ic (Stdlib.in_channel_length ic) in Stdlib.close_in ic; s)"]
let file_get_contents _ = admit ()

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

[@@custard_extern "Filename.concat"]
let concat_dir_filename _ _ = admit ()

[@@custard_extern "BatIO.input"]
private assume new type bat_input : Type0

type stream_reader = bat_input

[@@custard_extern "(fun () -> BatIO.stdin)"]
let open_stdin _ = admit ()

[@@custard_extern "(fun s -> try Some (BatIO.read_line s) with _ -> None)"]
let read_line _ = admit ()

[@@custard_extern "(fun s n -> try Some (BatIO.nread s (Z.to_int n)) with _ -> None)"]
let nread _ _ = admit ()

[@@custard_extern "(fun f -> try (match Unix.select [Unix.stdin] [] [] f with ([], _, _) -> false | _ -> true) with _ -> false)"]
let poll_stdin _ = admit ()

[@@custard_extern "Printexc.to_string"]
let message_of_exn _ = admit ()

[@@custard_extern "(fun _ -> Printexc.get_backtrace ())"]
let trace_of_exn _ = admit ()

[@@custard_extern "(fun () -> Printexc.raw_backtrace_to_string (Printexc.get_callstack 1000))"]
private assume val callstack : unit -> ML string

let stack_dump () = callstack ()

let finally h f = finally' h f

[@@custard_extern "Sys.signal_behavior"]
private assume new type signal_behavior : Type0

type sigint_handler = signal_behavior

[@@custard_extern "(fun f -> Sys.Signal_handle (fun i -> f (Z.of_int i)))"]
private assume val signal_handle : (int -> ML unit) -> sigint_handler

let sigint_handler_f f = signal_handle f

[@@custard_extern "Sys.Signal_ignore"]
let sigint_ignore = admit ()

private
let sigint_delay : ref I.t = mk_ref I.zero

private
let sigint_pending : ref bool = mk_ref false

private
let raise_sigint () : ML unit =
  sigint_pending := false;
  raise SigInt

(* This function should not do anything complicated, lest it cause deadlocks.
   Calling print_string, for example, can cause a deadlock (print_string →
   caml_flush → process_pending_signals → caml_execute_signal → raise_sigint →
   print_string → caml_io_mutex_lock ⇒ deadlock) *)
private
let raise_sigint_maybe_delay (_:int) : ML unit =
  if !sigint_delay = I.zero
  then raise_sigint ()
  else sigint_pending := true

let sigint_raise = signal_handle raise_sigint_maybe_delay

[@@custard_extern "Sys.Signal_default"]
private assume val signal_default : sigint_handler

private
let cur_sigint_handler : ref sigint_handler = mk_ref signal_default

[@@custard_extern "(fun h -> Sys.set_signal Sys.sigint h)"]
private assume val set_sigint_behavior : sigint_handler -> ML unit

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
  pid : I.t;
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
[@@custard_extern "(fun prog args -> let (stdin_r, stdin_w) = Unix.pipe () in let (stdout_r, stdout_w) = Unix.pipe () in let (stderr_r, stderr_w) = Unix.pipe () in Unix.set_close_on_exec stdin_w; Unix.set_close_on_exec stdout_r; Unix.set_close_on_exec stderr_r; let pid = Unix.create_process prog (Array.of_list (prog :: args)) stdin_r stdout_w stderr_w in Unix.close stdin_r; Unix.close stdout_w; Unix.close stderr_w; (pid, Unix.in_channel_of_descr stdout_r, Unix.in_channel_of_descr stderr_r, Unix.out_channel_of_descr stdin_w))"]
private assume val create_piped_process : string -> list string -> ML (I.t & in_channel & in_channel & out_channel)

(* On the OCaml side it would make more sense to take stop_marker in
   ask_process, but the F# side isn't built that way *)
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

[@@custard_extern "(fun ic -> try Unix.close (Unix.descr_of_in_channel ic) with _ -> ())"]
private assume val close_in_descr : in_channel -> ML unit

[@@custard_extern "(fun oc -> try Unix.close (Unix.descr_of_out_channel oc) with _ -> ())"]
private assume val close_out_descr : out_channel -> ML unit

(* The process may already be gone. On Unix we get ESRCH. On Windows, we
   apparently get EACCES (permission denied). *)
[@@custard_extern "(fun windows pid -> try Unix.kill pid Sys.sigkill with Unix.Unix_error (Unix.ESRCH, _, _) -> () | Unix.Unix_error (Unix.EACCES, _, _) when windows -> ())"]
private assume val kill_pid : bool -> I.t -> ML unit

[@@custard_extern "(fun pid -> let rec go () = try Stdlib.ignore (Unix.waitpid [] pid) with Unix.Unix_error (Unix.EINTR, _, _) -> go () in go ())"]
private assume val waitpid_ignore_signals : I.t -> ML unit

private
let kill_process' (p:proc) : ML unit =
  if not !p.killed then begin
    (* Close the fds directly: close_in and close_out both call `flush`,
       potentially forcing us to wait until p starts reading again. They
       might have been closed already (e.g. `run_process`), so we
       just attempt it. *)
    close_in_descr p.inc;
    close_in_descr p.errc;
    close_out_descr p.outc;
    kill_pid FStarC.Platform.windows p.pid;
    (* Avoid zombie processes (Unix.close_process does the same thing. *)
    waitpid_ignore_signals p.pid;
    p.killed := true
  end

(* The process must have finished without reading its input if this fails *)
[@@custard_extern "(fun oc s -> try Stdlib.output_string oc s with Sys_error _ -> ())"]
private assume val try_output_string : out_channel -> string -> ML unit

(* Only attempts to, so that we don't get an exception if the process is
   finished *)
[@@custard_extern "(fun oc -> (try Stdlib.flush oc with _ -> ()); (try Stdlib.close_out oc with _ -> ()))"]
private assume val try_flush_and_close : out_channel -> ML unit

(* Pass cleanup:false because kill_process closes both fds already. *)
[@@custard_extern "(fun ic -> BatIO.read_all (BatIO.input_channel ~autoclose:true ~cleanup:false ic))"]
private assume val read_all : in_channel -> ML string

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

[@@custard_extern "(fun c -> let buffer = Bytes.create 8192 in let fd = Unix.descr_of_in_channel c in let rec aux idx rem = if rem <= 0 then idx else (let rd, _, _ = Unix.select [fd] [] [] 0.0 in if rd = [] then idx else (let n = Unix.read fd buffer idx rem in if n <= 0 then idx else aux (idx + n) (rem - n))) in Bytes.sub_string buffer 0 (aux 0 1024))"]
private assume val channel_read_all_nonblock : in_channel -> ML string

[@@custard_extern "BatString.trim"]
private assume val trim : string -> string

(* Read stderr and call the handler if anything is in there. *)
private
let handle_stderr (p:proc) (h:string -> ML unit) : ML unit =
  let se = channel_read_all_nonblock p.errc in
  if se <> "" then h (trim se)

(** Feed `stdin` to `p`, and call `reader_fn` in a separate thread to read the
    response.

    Signal handling makes this function fairly hairy.  The usual design is to
    launch a reader thread, then write to the process on the main thread and use
    `Thread.join` to wait for the reader to complete.

    When we get a signal, Caml routes it to either of the threads.  If it
    reaches the reader thread, we're good: the reader thread is most likely
    waiting in input_line at that point, and input_line polls for signals fairly
    frequently.  If the signal reaches the writer (main) thread, on the other
    hand, we're toast: `Thread.join` isn't interruptible, so Caml will save the
    signal until the child thread exits and `join` returns, and at that point the
    Z3 query is complete and the signal is useless.

    There are three possible solutions to this problem:
    1. Use an interruptible version of Thread.join written in C
    2. Ensure that signals are always delivered to the reader thread
    3. Use a different synchronization mechanism between the reader and the writer.

    Option 1 is bad because building F* doesn't currently require a C compiler.
    Option 2 is easy to implement with `Unix.sigprocmask`, but that isn't
    available on Windows.  Option 3 is what the code below does: it uses a pipe
    and a 1-byte write as a way for the writer thread to wait on the reader
    thread. That's why `reader_fn` is passed a `signal_exit` function.

    If a SIGINT reaches the reader, it should still call `signal_exit`.  If
    a SIGINT reaches the writer, it should make sure that the reader exits.
    These two things are the responsibility of the caller of this function. **)
[@@custard_extern "(fun outc stdin reader_fn -> let fd_r, fd_w = Unix.pipe () in BatPervasives.finally (fun () -> Unix.close fd_w; Unix.close fd_r) (fun () -> let wait_for_exit () = Stdlib.ignore (Unix.read fd_r (Bytes.create 1) 0 1) in let signal_exit () = (try Stdlib.ignore (Unix.write fd_w (Bytes.create 1) 0 1) with Unix.Unix_error (Unix.EBADF, _, _) -> ()) in let t = Thread.create reader_fn signal_exit in Stdlib.output_string outc stdin; Stdlib.flush outc; wait_for_exit (); Thread.join t) ())"]
private assume val process_read_async : out_channel -> string -> ((unit -> ML unit) -> ML unit) -> ML unit

[@@custard_extern "Buffer.t"]
private assume new type buffer : Type0

[@@custard_extern "(fun () -> Buffer.create 16)"]
private assume val buffer_create : unit -> ML buffer

[@@custard_extern "Buffer.add_string"]
private assume val buffer_add : buffer -> string -> ML unit

[@@custard_extern "Buffer.contents"]
private assume val buffer_contents : buffer -> ML string

private
type read_result = | EOF | SIGINT

let ask_process p stdin exn_handler stderr_handler =
  let result : ref (option read_result) = mk_ref None in
  let out = buffer_create () in
  let stop_marker (s:string) : ML bool = match p.stop_marker with Some f -> f s | None -> false in
  let reader_fn (signal_fn:unit -> ML unit) : ML unit =
    let rec loop () : ML unit =
      match input_line_opt p.inc with
      | None -> result := Some EOF
      | Some line ->
        let line = trim line in
        if not (stop_marker line) then begin
          buffer_add out (line ^ "\n");
          loop ()
        end
    in
    (try loop () with | SigInt -> result := Some SIGINT);
    signal_fn ()
  in
  try
    (* Check stderr both before and after asking. Note: this does
       not handle the case when the process prints something to stderr
       and then hangs. We will stay in the process_read_async call without
       ever handling the output. To properly handle that, we could
       use a separate thread, but then all stderr_handler functions need
       to take locks. Since this is not a problem for now, we just avoid
       this complexity. *)
    handle_stderr p stderr_handler;
    (* In the following we can get a signal at any point; it's the caller's
       responsibility to ensure that reader_fn will exit in that case *)
    process_read_async p.outc stdin reader_fn;
    handle_stderr p stderr_handler;
    (match !result with
     | Some EOF -> kill_process' p; buffer_add out (exn_handler ())
     | Some SIGINT -> raise SigInt
     | None -> ());
    buffer_contents out
  with
  | e ->
    (* Ensure that reader_fn gets an EOF and exits *)
    kill_process' p;
    raise e

let kill_process p = kill_process' p

let kill_all () = L.iter kill_process' !all_procs

let proc_prog p = p.prog

[@@custard_extern "(fun cmd -> Z.of_int (Sys.command cmd))"]
let system_run _ = admit ()

[@@custard_extern "Sys.getcwd"]
let getcwd _ = admit ()

[@@custard_extern "Z.of_string"]
let int_of_string _ = admit ()

[@@custard_extern "(fun x -> if String.equal x \"\" then None else try Some (Z.of_string x) with Invalid_argument _ -> None)"]
let safe_int_of_string _ = admit ()

[@@custard_extern "Z.of_int"]
let int_of_char _ = admit ()

[@@custard_extern "(fun x -> x)"]
let int_of_byte _ = admit ()

[@@custard_extern "(fun c -> c)"]
let byte_of_char _ = admit ()

[@@custard_extern "Z.to_int"]
let char_of_int _ = admit ()

[@@custard_extern "(fun x -> Z.of_int (Char.code x))"]
let int_of_uint8 _ = admit ()

[@@custard_extern "Z.to_int"]
let uint16_of_int _ = admit ()

[@@custard_extern "(fun b -> Stdlib.float_of_int (Char.code b))"]
let float_of_byte _ = admit ()

[@@custard_extern "Stdlib.float_of_int"]
let float_of_int32 _ = admit ()

[@@custard_extern "BatInt64.to_float"]
let float_of_int64 _ = admit ()

[@@custard_extern "Stdlib.float_of_string"]
private assume val ocaml_float_of_string : string -> float

let float_of_string s = ocaml_float_of_string s

[@@custard_extern "(fun i -> i)"]
let int_of_int32 _ = admit ()

[@@custard_extern "BatInt32.of_int"]
let int32_of_int _ = admit ()

[@@custard_extern "Stdlib.string_of_float"]
let string_of_float _ = admit ()

[@@custard_extern "(fun i -> BatUTF8.init 1 (fun _ -> BatUChar.chr i))"]
let string_of_char _ = admit ()

[@@custard_extern "(fun i -> let hs = Printf.sprintf \"%x\" i in if String.length hs = 1 then \"0\" ^ hs else hs)"]
let hex_string_of_byte _ = admit ()


[@@custard_extern "BatBase64.str_encode"]
let base64_encode _ = admit ()

[@@custard_extern "BatBase64.str_decode"]
let base64_decode _ = admit ()

[@@custard_extern "BatString.starts_with"]
private assume val ocaml_starts_with : string -> string -> bool

let starts_with long short = ocaml_starts_with long short

let trim_string s = trim s

[@@custard_extern "BatString.ends_with"]
private assume val ocaml_ends_with : string -> string -> bool

let ends_with long short = ocaml_ends_with long short

[@@custard_extern "(fun s i -> BatUChar.code (BatUTF8.get s (Z.to_int i)))"]
let char_at _ _ = admit ()

let is_upper c = I.(of_char c >= of_char 'A' && of_char c <= of_char 'Z')

[@@custard_extern "BatString.exists"]
let contains _ _ = admit ()

[@@custard_extern "(fun s i -> BatString.tail s (Z.to_int i))"]
let substring_from _ _ = admit ()

[@@custard_extern "(fun s i j -> BatString.sub s (Z.to_int i) (Z.to_int j))"]
let substring _ _ _ = admit ()

[@@custard_extern "(fun s c1 c2 -> let c1 = BatUChar.chr c1 and c2 = BatUChar.chr c2 in BatUTF8.map (fun x -> if BatUChar.eq x c1 then c2 else x) s)"]
let replace_char _ _ _ = admit ()

[@@custard_extern "(fun s c by -> BatString.replace_chars (fun x -> if Char.equal x (Char.chr c) then by else BatString.of_char x) s)"]
let replace_chars _ _ _ = admit ()

[@@custard_extern "(fun s -> Z.of_int (BatHashtbl.hash s))"]
let hashcode _ = admit ()

[@@custard_extern "(fun s1 s2 -> Z.of_int (BatString.compare s1 s2))"]
let compare _ _ = admit ()

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
      | [] -> fail "firstN"
  in
  aux [] 0 l

let rec nth_tail n l =
  if n = 0 then l
  else match l with
    | _ :: tl -> nth_tail (n - 1) tl
    | [] -> fail "tl"

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
  | [] -> fail "impossible"

let incr r = r := !r + 1

let decr r = r := !r - 1

let geq i j = i >= j

let rec for_range lo hi f =
  if lo > hi then ()
  else begin
    f lo;
    for_range (lo + 1) hi f
  end

(* Note: If F* is called invoked via a symlink, executable_name contains
   the name of the unresolved link in macos (not so in Linux). Since
   F* needs to find its library relative to the path of its installed
   executable, we must resolve all links, so we use realpath. *)
[@@custard_extern "(fun () -> Unix.realpath Sys.executable_name)"]
private assume val ocaml_exec_name : unit -> string

let exec_name = ocaml_exec_name ()

(* This is how F* was called, i.e. argv[0] in Unix. For example
   it may be `./bin/fstar.exe` if we are running it from the
   repository. *)
[@@custard_extern "(fun () -> Sys.argv.(0))"]
private assume val ocaml_argv0 : unit -> string

let argv0 = ocaml_argv0 ()

let get_exec_dir () = dirname exec_name

[@@custard_extern "(fun () -> Array.to_list Sys.argv)"]
let get_cmd_args _ = admit ()

[@@custard_extern "(fun x -> try Some (Sys.getenv x) with Not_found -> None)"]
let expand_environment_variable _ = admit ()

[@@custard_extern "(==)"]
let physical_equality _ _ = admit ()

let check_sharing a b msg =
  if physical_equality a b
  then pr ("Sharing OK: " ^ msg ^ "\n")
  else pr ("Sharing broken in " ^ msg ^ "\n")

[@@custard_extern "(fun c -> c <= 255 && BatChar.is_letter (Char.chr c))"]
let is_letter _ = admit ()

[@@custard_extern "(fun c -> c <= 255 && BatChar.is_digit (Char.chr c))"]
let is_digit _ = admit ()

let is_letter_or_digit c = is_letter c || is_digit c

(* Modeled after: Char.IsPunctuation in .NET
   (http://www.dotnetperls.com/char-ispunctuation) *)
let is_punctuation c =
  List.Tot.mem c ['!'; '"'; '#'; '%'; '&'; '\''; '('; ')'; '*'; ','; '-'; '.'; '/';
                  ':'; ';'; '?'; '@'; '['; '\\'; ']'; '_'; '{'; '}']

[@@custard_extern "(fun c -> c <= 255 && BatChar.is_symbol (Char.chr c))"]
let is_symbol _ = admit ()

[@@custard_extern "Mutex.t"]
private assume new type mutex : Type0

[@@custard_extern "Mutex.create"]
private assume val mutex_create : unit -> mutex

[@@custard_extern "Mutex.lock"]
private assume val mutex_lock : mutex -> ML unit

[@@custard_extern "Mutex.unlock"]
private assume val mutex_unlock : mutex -> ML unit

private
let mlock = mutex_create ()

let monitor_enter _ = mutex_lock mlock

let monitor_exit _ = mutex_unlock mlock

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

let with_monitor _ f x =
  atomically' (fun () ->
    monitor_enter ();
    finally (fun () -> monitor_exit ()) (fun () -> f x))

let current_tid _ = 0

[@@custard_extern "(fun n -> Thread.delay (Z.to_float n /. 1000.))"]
let sleep _ = admit ()

let atomically f = atomically' f

[@@custard_extern "(fun f -> Stdlib.ignore (Thread.create f ()))"]
let spawn _ = admit ()

[@@custard_extern "Stdlib.print_endline"]
let print_endline _ = admit ()

let maybe_create_parent fname = create_parent fname

[@@custard_extern "(fun fname -> Filename.temp_file ~temp_dir:(Filename.dirname fname) (Filename.basename fname) \".tmp\")"]
private assume val temp_file_for : string -> ML string

[@@custard_extern "Sys.rename"]
private assume val rename : string -> string -> ML unit

[@@custard_extern "(fun f -> try Sys.remove f with _ -> ())"]
private assume val try_remove : string -> ML unit

[@@custard_extern "Stdlib.output_value"]
private assume val output_value (#a:Type) : out_channel -> a -> ML unit

[@@custard_extern "Stdlib.input_value"]
private assume val input_value (#a:Type) : in_channel -> ML a

[@@custard_extern "Stdlib.output_binary_int"]
private assume val output_binary_int : out_channel -> I.t -> ML unit

[@@custard_extern "Stdlib.input_binary_int"]
private assume val input_binary_int : in_channel -> ML I.t

[@@custard_extern "(fun c len -> Stdlib.seek_in c (Stdlib.pos_in c + len))"]
private assume val skip : in_channel -> I.t -> ML unit

(* Write [fname] atomically: the payload is first written to a private
   temporary file in the same directory, which is then renamed over [fname].
   Since [Sys.rename] is atomic on POSIX, a concurrent reader of [fname]
   observes either the previous contents or the new ones in full, but never a
   partially written file. This matters because several fstar.exe processes
   may share a single --cache_dir. *)
private
let with_out_channel_atomic (#a:Type) (fname:string) (f:out_channel -> ML a) : ML a =
  create_parent fname;
  let tmp = temp_file_for fname in
  let channel = open_file_for_writing tmp in
  let result =
    try finally (fun () -> close_out_channel channel) (fun () -> f channel)
    with | e -> try_remove tmp; raise e
  in
  rename tmp fname;
  result

private
let with_in_channel_opt (#a:Type) (fname:string) (f:in_channel -> ML a) : ML (option a) =
  try
    let channel = open_in_bin fname in
    finally (fun () -> close_in channel) (fun () -> Some (f channel))
  with | _ -> None

let save_value_to_file fname value =
  with_out_channel_atomic fname (fun channel -> output_value channel value)

let load_value_from_file fname =
  with_in_channel_opt fname (fun channel -> input_value channel)

let save_2values_to_file fname value1 value2 =
  try
    with_out_channel_atomic fname (fun channel ->
      output_value channel value1;
      output_value channel value2)
  with
  (* The atomic write leaves [fname] untouched on failure, but an older,
     now-stale file may still be there: get rid of it. *)
  | e -> try_remove fname; raise e

let load_2values_from_file fname =
  try
    create_parent fname;
    with_in_channel_opt fname (fun channel ->
      let v1 = input_value channel in
      let v2 = input_value channel in
      (v1, v2))
  with | _ -> None

[@@custard_extern "(fun v -> Marshal.to_string v [])"]
private assume val marshal' (#a:Type) : a -> ML string

[@@custard_extern "BatDigest.string"]
private assume val raw_digest : string -> string

[@@custard_extern "BatDigest.to_hex"]
private assume val digest_to_hex : string -> string

(* See FStarC.Util.fsti for the layout of this container format. *)
let save_3values_to_file fname value1 value2 value3 =
  try
    let b12 = marshal' value1 ^ marshal' value2 in
    let b3 = marshal' value3 in
    (* A Merkle-style digest of the two halves, so that we never have to
       materialize the concatenation of the whole payload. *)
    let dig = digest_to_hex (raw_digest (raw_digest b12 ^ raw_digest b3)) in
    with_out_channel_atomic fname (fun channel ->
      output_value channel dig;
      output_binary_int channel (S.byte_length b12);
      output_string channel b12;
      output_string channel b3);
    dig
  with
  (* The atomic write leaves [fname] untouched on failure, but an older,
     now-stale file may still be there: get rid of it. *)
  | e -> try_remove fname; raise e

let load_1value_from_file3 fname =
  with_in_channel_opt fname (fun channel ->
    let dig : string = input_value channel in
    let _len = input_binary_int channel in
    let v1 = input_value channel in
    (dig, v1))

let load_2values_from_file3 fname =
  with_in_channel_opt fname (fun channel ->
    let dig : string = input_value channel in
    let _len = input_binary_int channel in
    let v1 = input_value channel in
    let v2 = input_value channel in
    (dig, v1, v2))

let load_3rd_value_from_file3 fname =
  with_in_channel_opt fname (fun channel ->
    let _dig : string = input_value channel in
    let len = input_binary_int channel in
    skip channel len;
    input_value channel)

[@@custard_extern "Printexc.to_string"]
let print_exn _ = admit ()

[@@custard_extern "(string, string) Hashtbl.t"]
private assume new type digest_table : Type0

[@@custard_extern "(fun () -> Hashtbl.create 101)"]
private assume val digest_table_create : unit -> ML digest_table

[@@custard_extern "Hashtbl.find_opt"]
private assume val digest_table_find : digest_table -> string -> ML (option string)

[@@custard_extern "Hashtbl.replace"]
private assume val digest_table_replace : digest_table -> string -> string -> ML unit

[@@custard_extern "BatDigest.file"]
private assume val raw_digest_of_file : string -> ML string

private
let digest_cache : digest_table = digest_table_create ()

let digest_of_file fname =
  match digest_table_find digest_cache fname with
  | Some dig -> dig
  | None ->
    let dig = digest_to_hex (raw_digest_of_file fname) in
    digest_table_replace digest_cache fname dig;
    dig

let digest_of_string s = digest_to_hex (raw_digest s)

(* Sets access and modification times to current time *)
[@@custard_extern "(fun fname -> Unix.utimes fname 0.0 0.0)"]
let touch_file _ = admit ()

[@@custard_extern "(fun s -> Z.to_string (Z.of_string s))"]
let ensure_decimal _ = admit ()

[@@custard_extern "Sys.time"]
private assume val sys_time : unit -> ML float

(* Milliseconds since [t], a [sys_time] *)
[@@custard_extern "(fun t -> 1000.0 *. (Sys.time () -. t))"]
private assume val ms_since : float -> ML float

let measure_execution_time tag f =
  let t = sys_time () in
  let retv = f () in
  let ms = ms_since t in
  pr ("Execution time of " ^ tag ^ ": " ^ string_of_float ms ^ " ms\n");
  retv

let return_execution_time f =
  let t = sys_time () in
  let retv = f () in
  (retv, ms_since t)

let read r = !r

let write r v = r := v

let marshal x = marshal' x

[@@custard_extern "(fun x -> Marshal.from_string x 0)"]
let unmarshal _ = admit ()

[@@custard_extern "(fun f s -> let ls = Array.fold_left (fun out a -> f a :: out) [] s in Printf.sprintf \"[| %s |]\" (String.concat \"; \" (List.rev ls)))"]
let print_array _ _ = admit ()

[@@custard_extern "(fun a -> Z.of_int (Array.length a))"]
let array_length _ = admit ()

[@@custard_extern "(fun a i -> Array.get a (Z.to_int i))"]
let array_index _ _ = admit ()

[@@custard_extern "Unix.putenv"]
let putenv _ _ = admit ()

[@@custard_extern "(fun prog args -> Z.of_int (Unix.create_process prog (Array.of_list args) Unix.stdin Unix.stdout Unix.stderr))"]
let create_process _ _ = admit ()

[@@custard_extern "(fun pid -> match snd (Unix.waitpid [] (Z.to_int pid)) with Unix.WEXITED rc -> FStar_Pervasives.Inl (Z.of_int rc) | Unix.WSIGNALED rc -> FStar_Pervasives.Inr (Z.of_int rc) | Unix.WSTOPPED _ -> Stdlib.failwith \"waitpid: unexpected WSTOPPED, should not happen with empty flags\")"]
let waitpid _ = admit ()

[@@custard_extern "(function Unix.Unix_error (Unix.ENOENT, _, _) -> true | _ -> false)"]
let exn_is_enoent _ = admit ()
