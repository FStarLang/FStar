open FStarC_Json

let max_int = Z.of_int max_int
let is_letter c = if c > 255 then false else BatChar.is_letter (BatChar.chr c)
let is_digit  c = if c > 255 then false else BatChar.is_digit  (BatChar.chr c)
let is_letter_or_digit c = is_letter c || is_digit c
let is_symbol c = if c > 255 then false else BatChar.is_symbol (BatChar.chr c)

(* Modeled after: Char.IsPunctuation in .NET
   (http://www.dotnetperls.com/char-ispunctuation)
*)
let is_punctuation c = List.mem c [33; 34; 35; 37; 38; 39; 40; 41; 42; 44; 45; 46; 47; 58; 59; 63; 64; 91; 92; 93; 95; 123; 125]
(*'!','"','#','%','&','\'','(',')','*',',','-','.','/',':',';','?','@','[','\\',']','_','{','}'*)

let return_all x = x

type time = float
let now () = BatUnix.gettimeofday ()
let now_ms () = Z.of_int (int_of_float (now () *. 1000.0))
let time_diff (t1:time) (t2:time) : float * Prims.int =
  let n = t2 -. t1 in
  n,
  Z.of_float (n *. 1000.0)
let record_time f =
    let start = now () in
    let res = f () in
    let _, elapsed = time_diff start (now()) in
    res, elapsed
let get_file_last_modification_time f = (BatUnix.stat f).BatUnix.st_mtime
let is_before t1 t2 = compare t1 t2 < 0
let string_of_time = string_of_float

exception Impos

let cur_sigint_handler : Sys.signal_behavior ref =
  ref Sys.Signal_default

exception SigInt
type sigint_handler = Sys.signal_behavior

let sigint_handler_f f = Sys.Signal_handle f

let sigint_ignore: sigint_handler =
  Sys.Signal_ignore

let sigint_delay = ref 0
let sigint_pending = ref false

let raise_sigint _ =
  sigint_pending := false;
  raise SigInt

let raise_sigint_maybe_delay _ =
  (* This function should not do anything complicated, lest it cause deadlocks.
   * Calling print_string, for example, can cause a deadlock (print_string →
   * caml_flush → process_pending_signals → caml_execute_signal → raise_sigint →
   * print_string → caml_io_mutex_lock ⇒ deadlock) *)
  if !sigint_delay = 0
  then raise_sigint ()
  else sigint_pending := true

let sigint_raise: sigint_handler =
  Sys.Signal_handle raise_sigint_maybe_delay

let get_sigint_handler () =
  !cur_sigint_handler

let set_sigint_handler sigint_handler =
  cur_sigint_handler := sigint_handler;
  Sys.set_signal Sys.sigint !cur_sigint_handler

let with_sigint_handler handler f =
  let original_handler = !cur_sigint_handler in
  BatPervasives.finally
    (fun () -> Sys.set_signal Sys.sigint original_handler)
    (fun () -> set_sigint_handler handler; f ())
    ()

(* Re export this type, it's mentioned in the interface for this module. *)
type out_channel = Stdlib.out_channel

let stderr = Stdlib.stderr
let stdout = Stdlib.stdout

let open_file_for_writing (fn : string) = Stdlib.open_out_bin fn
let open_file_for_appending (fn : string) = Stdlib.open_out_gen [Open_append; Open_wronly; Open_creat; Open_binary] 0o644 fn
let close_out_channel (c : out_channel) = Stdlib.close_out c

let flush (c:out_channel) : unit = Stdlib.flush c

let append_to_file (c:out_channel) s = Printf.fprintf c "%s\n" s; flush c

type proc =
    {pid: int;
     inc : in_channel; (* in == where we read from, so the process's stdout *)
     errc : in_channel; (* the process's stderr *)
     outc : out_channel; (* the process's stdin *)
     mutable killed : bool;
     stop_marker: (string -> bool) option;
     id : string;
     prog : string;
     start_time : time}

let all_procs : (proc list) ref = ref []

let lock () = ()
let release () = ()
let sleep n = Thread.delay ((Z.to_float n) /. 1000.)

let mlock = Mutex.create ()

let monitor_enter _ = Mutex.lock mlock
let monitor_exit _ = Mutex.unlock mlock
let monitor_wait _ = ()
let monitor_pulse _ = ()
let current_tid _ = Z.zero

let atomically f = (* This function only protects against signals *)
  let finalizer () =
    decr sigint_delay;
    if !sigint_pending && !sigint_delay = 0 then
      raise_sigint () in
  let body f =
    incr sigint_delay; f () in
  BatPervasives.finally finalizer body f

let with_monitor _ f x = atomically (fun () ->
  monitor_enter ();
  BatPervasives.finally monitor_exit f x)

let spawn f =
  let _ = Thread.create f () in ()

let stack_dump () = Printexc.raw_backtrace_to_string (Printexc.get_callstack 1000)

(* On the OCaml side it would make more sense to take stop_marker in
   ask_process, but the F# side isn't built that way *)
let start_process'
      (id: string) (prog: string) (args: string list)
      (stop_marker: (string -> bool) option) : proc =
  let (stdin_r, stdin_w) = Unix.pipe () in
  let (stdout_r, stdout_w) = Unix.pipe () in
  let (stderr_r, stderr_w) = Unix.pipe () in
  Unix.set_close_on_exec stdin_w;
  Unix.set_close_on_exec stdout_r;
  Unix.set_close_on_exec stderr_r;
  let pid = Unix.create_process prog (Array.of_list (prog :: args)) stdin_r stdout_w stderr_w in
  Unix.close stdin_r;
  Unix.close stdout_w;
  Unix.close stderr_w;
  let proc = { pid = pid;
               id = prog ^ ":" ^ id;
               prog = prog;
               inc = Unix.in_channel_of_descr stdout_r;
               errc = Unix.in_channel_of_descr stderr_r;
               outc = Unix.out_channel_of_descr stdin_w;
               stop_marker = stop_marker;
               killed = false;
               start_time = now()} in
  (* print_string ("Started process " ^ proc.id ^ "\n" ^ (stack_dump())); *)
  all_procs := proc :: !all_procs;
  proc

let start_process
      (id: string) (prog: string) (args: string list)
      (stop_marker: string -> bool) : proc =
  start_process' id prog args (Some stop_marker)

let rec waitpid_ignore_signals pid =
  try ignore (Unix.waitpid [] pid)
  with Unix.Unix_error (Unix.EINTR, _, _) ->
    waitpid_ignore_signals pid

let kill_process (p: proc) =
  if not p.killed then begin
      (* Close the fds directly: close_in and close_out both call `flush`,
         potentially forcing us to wait until p starts reading again. They
         might have been closed already (e.g. `run_process`), so we
         just `attempt` it. *)
      let attempt f =
          try f () with | _ -> ()
      in
      attempt (fun () -> Unix.close (Unix.descr_of_in_channel p.inc));
      attempt (fun () -> Unix.close (Unix.descr_of_in_channel p.errc));
      attempt (fun () -> Unix.close (Unix.descr_of_out_channel p.outc));
      (try Unix.kill p.pid Sys.sigkill
       with Unix.Unix_error (Unix.ESRCH, _, _) -> ());
      (* Avoid zombie processes (Unix.close_process does the same thing. *)
      waitpid_ignore_signals p.pid;
      (* print_string ("Killed process " ^ p.id ^ "\n" ^ (stack_dump()));       *)
      p.killed <- true
    end

let kill_all () =
  BatList.iter kill_process !all_procs

let proc_prog (p:proc) : string = p.prog

let process_read_all_output (p: proc) =
  (* Pass cleanup:false because kill_process closes both fds already. *)
  BatIO.read_all (BatIO.input_channel ~autoclose:true ~cleanup:false p.inc)


let channel_read_all_nonblock (c: in_channel) : string =
  let buffer = Bytes.create 8192 in
  let fd = Unix.descr_of_in_channel c in
  let rec aux (idx:int) (rem:int) =
    if rem <= 0 then idx
    else (
      let rd, _, _ = Unix.select [fd] [] [] 0.0 in
      if rd = [] then idx
      else (
        let n = Unix.read fd buffer idx rem in
        if n <= 0
        then idx
        else aux (idx+n) (rem-n)
      )
    )
  in
  let len = aux 0 1024 in
  Bytes.sub_string buffer 0 len

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

let process_read_async p stdin reader_fn =
  let fd_r, fd_w = Unix.pipe () in
  BatPervasives.finally (fun () -> Unix.close fd_w; Unix.close fd_r)
    (fun () ->
      let wait_for_exit () =
        ignore (Unix.read fd_r (Bytes.create 1) 0 1) in
      let signal_exit () =
        try ignore (Unix.write fd_w (Bytes.create 1) 0 1)
        with (* ‘write’ will fail if called after the finalizer above *)
        | Unix.Unix_error (Unix.EBADF, _, _) -> () in

      let write_input = function
        | Some str -> output_string p.outc str; flush p.outc
        | None -> () in

      (* In the following we can get a signal at any point; it's the caller's
         responsibility to ensure that reader_fn will exit in that case *)
      let t = Thread.create reader_fn signal_exit in
      write_input stdin;
      wait_for_exit ();
      Thread.join t) ()

let run_process (id: string) (prog: string) (args: string list) (stdin: string option): string =
  let p = start_process' id prog args None in
  (match stdin with
   | None -> ()
   | Some str ->
     try output_string p.outc str with
     | Sys_error _ -> () (* FIXME: check for "Broken pipe". In that case this is fine, process must have finished without reading input *)
     | e -> raise e
  );
  (try flush p.outc with | _ -> ()); (* only _attempt_ to flush, so we don't get an exception if the process is finished *)
  (try close_out p.outc with | _ -> ()); (* idem *)
  let s = process_read_all_output p in
  kill_process p;
  s

let system_run (cmd:string) : Z.t = Z.of_int (Sys.command cmd)

type read_result = EOF | SIGINT

let handle_stderr (p:proc) (h : string -> unit) =
  (* Read stderr and call the handler if anything is in there.  *)
  let se = channel_read_all_nonblock p.errc in
  if se <> "" then
     h (BatString.trim se)

let ask_process
      (p: proc) (stdin: string)
      (exn_handler: unit -> string)
      (stderr_handler : string -> unit)
      : string =
  let result = ref None in
  let out = Buffer.create 16 in
  let stop_marker = BatOption.default (fun s -> false) p.stop_marker in

  let reader_fn signal_fn =
    let rec loop p out =
      let line = BatString.trim (input_line p.inc) in (* raises EOF *)
      if not (stop_marker line) then
        (Buffer.add_string out (line ^ "\n"); loop p out) in
    (try loop p out
     with | SigInt -> result := Some SIGINT
          | End_of_file -> result := Some EOF);
    signal_fn () in

  try
    (* Check stderr both before and after asking. Note: this does
     * not handle the case when the process prints something to stderr
     * and then hangs. We will stay in the process_read_async call without
     * ever handling the output. To properly handle that, we could
     * use a separate thread, but then all stderr_handler functions need
     * to take locks. Since this is not a problem for now, we just avoid
     * this complexity. *)
    handle_stderr p stderr_handler;
    process_read_async p (Some stdin) reader_fn;
    handle_stderr p stderr_handler;
    (match !result with
     | Some EOF -> kill_process p; Buffer.add_string out (exn_handler ())
     | Some SIGINT -> raise SigInt
     | None -> ());
    Buffer.contents out
  with e -> (* Ensure that reader_fn gets an EOF and exits *)
    kill_process p; raise e

let get_file_extension (fn:string) : string = snd (BatString.rsplit fn ".")
let is_path_absolute path_str =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let path_str' = of_string path_str in
  is_absolute path_str'
let join_paths path_str0 path_str1 =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  to_string ((of_string path_str0) //@ (of_string path_str1))

let normalize_file_path (path_str:string) =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  to_string
    (normalize_in_tree
       (let path = of_string path_str in
         if is_absolute path then
           path
         else
           let pwd = of_string (BatSys.getcwd ()) in
           pwd //@ path))

type stream_reader = BatIO.input
let open_stdin () = BatIO.stdin
let read_line s =
  try
    Some (BatIO.read_line s)
  with
    _ -> None
let nread (s:stream_reader) (n:Z.t) =
  try
    Some (BatIO.nread s (Z.to_int n))
  with
    _ -> None

let poll_stdin (f:float) =
    try 
      let ready_fds, _, _ = Unix.select [Unix.stdin] [] [] f in
      match ready_fds with
      | [] -> false
      | _ -> true
    with
    | _ -> false

type string_builder = BatBuffer.t
let new_string_builder () = BatBuffer.create 256
let clear_string_builder b = BatBuffer.clear b
let string_of_string_builder b = BatBuffer.contents b
let string_builder_append b s = BatBuffer.add_string b s

let message_of_exn (e:exn) = Printexc.to_string e
let trace_of_exn (e:exn) = Printexc.get_backtrace ()

module StringOps =
  struct
    type t = string
    let equal (x:t) (y:t) = x=y
    let compare (x:t) (y:t) = BatString.compare x y
    let hash (x:t) = BatHashtbl.hash x
  end

module StringHashtbl = BatHashtbl.Make(StringOps)
module StringMap = BatMap.Make(StringOps)

type 'value smap = 'value StringHashtbl.t
let smap_create (i:Z.t) : 'value smap = StringHashtbl.create (Z.to_int i)
let smap_clear (s:('value smap)) = StringHashtbl.clear s
let smap_add (m:'value smap) k (v:'value) = StringHashtbl.replace m k v
let smap_of_list (l: (string * 'value) list) =
  let s = StringHashtbl.create (BatList.length l) in
  FStar_List.iter (fun (x,y) -> smap_add s x y) l;
  s
let smap_try_find (m:'value smap) k = StringHashtbl.find_option m k
let smap_fold (m:'value smap) f a = StringHashtbl.fold f m a
let smap_remove (m:'value smap) k = StringHashtbl.remove m k
let smap_keys (m:'value smap) = smap_fold m (fun k _ acc -> k::acc) []
let smap_copy (m:'value smap) = StringHashtbl.copy m
let smap_size (m:'value smap) = StringHashtbl.length m
let smap_iter (m:'value smap) f = StringHashtbl.iter f m

exception PSMap_Found
type 'value psmap = 'value StringMap.t
let psmap_empty (_: unit) : 'value psmap = StringMap.empty
let psmap_add (map: 'value psmap) (key: string) (value: 'value) = StringMap.add key value map
let psmap_find_default (map: 'value psmap) (key: string) (dflt: 'value) =
  StringMap.find_default dflt key map
let psmap_try_find (map: 'value psmap) (key: string) =
  StringMap.Exceptionless.find key map
let psmap_fold (m:'value psmap) f a = StringMap.fold f m a
let psmap_find_map (m:'value psmap) f =
  let res = ref None in
  let upd k v =
    let r = f k v in
    if r <> None then (res := r; raise PSMap_Found) in
  (try StringMap.iter upd m with PSMap_Found -> ());
  !res
let psmap_modify (m: 'value psmap) (k: string) (upd: 'value option -> 'value) =
  StringMap.modify_opt k (fun vopt -> Some (upd vopt)) m

let psmap_merge (m1: 'value psmap) (m2: 'value psmap) : 'value psmap =
  psmap_fold m1 (fun k v m -> psmap_add m k v) m2

let psmap_remove (m: 'value psmap)  (key:string)
  : 'value psmap = StringMap.remove key m
  
module ZHashtbl = BatHashtbl.Make(Z)
module ZMap = BatMap.Make(Z)

type 'value imap = 'value ZHashtbl.t
let imap_create (i:Z.t) : 'value imap = ZHashtbl.create (Z.to_int i)
let imap_clear (s:('value imap)) = ZHashtbl.clear s
let imap_add (m:'value imap) k (v:'value) = ZHashtbl.replace m k v
let imap_of_list (l: (Z.t * 'value) list) =
  let s = ZHashtbl.create (BatList.length l) in
  FStar_List.iter (fun (x,y) -> imap_add s x y) l;
  s
let imap_try_find (m:'value imap) k = ZHashtbl.find_option m k
let imap_fold (m:'value imap) f a = ZHashtbl.fold f m a
let imap_remove (m:'value imap) k = ZHashtbl.remove m k
let imap_keys (m:'value imap) = imap_fold m (fun k _ acc -> k::acc) []
let imap_copy (m:'value imap) = ZHashtbl.copy m

type 'value pimap = 'value ZMap.t
let pimap_empty (_: unit) : 'value pimap = ZMap.empty
let pimap_add (map: 'value pimap) (key: Z.t) (value: 'value) = ZMap.add key value map
let pimap_find_default (map: 'value pimap) (key: Z.t) (dflt: 'value) =
  ZMap.find_default dflt key map
let pimap_try_find (map: 'value pimap) (key: Z.t) =
  ZMap.Exceptionless.find key map
let pimap_fold (m:'value pimap) f a = ZMap.fold f m a
let pimap_remove (m:'value pimap) k = ZMap.remove k m

(* restore pre-2.11 BatString.nsplit behavior,
   see https://github.com/ocaml-batteries-team/batteries-included/issues/845 *)
let batstring_nsplit s t =
  if s = "" then [] else BatString.split_on_string t s

let format (fmt:string) (args:string list) =
  let frags = batstring_nsplit fmt "%s" in
  if BatList.length frags <> BatList.length args + 1 then
    failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (Stdlib.string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
  else
    let sbldr = new_string_builder () in
    string_builder_append sbldr (List.hd frags);
    BatList.iter2
        (fun frag arg -> string_builder_append sbldr arg;
                         string_builder_append sbldr frag)
        (List.tl frags) args;
    string_of_string_builder sbldr

let format1 f a = format f [a]
let format2 f a b = format f [a;b]
let format3 f a b c = format f [a;b;c]
let format4 f a b c d = format f [a;b;c;d]
let format5 f a b c d e = format f [a;b;c;d;e]
let format6 f a b c d e g = format f [a;b;c;d;e;g]

let flush_stdout () = flush stdout

let stdout_isatty () = Some (Unix.isatty Unix.stdout)

(* NOTE: this is deciding whether or not to color by looking
   at stdout_isatty(), which may be a wrong choice if
   we're instead outputting to stderr. e.g.
     fstar.exe Blah.fst 2>errlog
   will colorize the errors in the file if stdout is not
   also redirected.
*)
let colorize s colors =
  match colors with
  | (c1,c2) ->
     match stdout_isatty () with
     | Some true -> format3 "%s%s%s" c1 s c2
     | _ -> s

let colorize_bold s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[39;1m" s "\x1b[0m"
  | _ -> s

let colorize_red s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[31;1m" s "\x1b[0m"
  | _ -> s

let colorize_yellow s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[33;1m" s "\x1b[0m"
  | _ -> s

let colorize_cyan s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[36;1m" s "\x1b[0m"
  | _ -> s

let colorize_green s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[32;1m" s "\x1b[0m"
  | _ -> s

let colorize_magenta  s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[35;1m" s "\x1b[0m"
  | _ -> s

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

type printer = {
  printer_prinfo: string -> unit;
  printer_prwarning: string -> unit;
  printer_prerror: string -> unit;
  printer_prgeneric: string -> (unit -> string) -> (unit -> json) -> unit
}

let default_printer =
  { printer_prinfo = (fun s -> pr "%s" s; flush stdout);
    printer_prwarning = (fun s -> fpr stderr "%s" (colorize_yellow s); flush stdout; flush stderr);
    printer_prerror = (fun s -> fpr stderr "%s" (colorize_red s); flush stdout; flush stderr);
    printer_prgeneric = fun label get_string get_json -> pr "%s: %s" label (get_string ())}

let current_printer = ref default_printer
let set_printer printer = current_printer := printer

let print_raw s = set_binary_mode_out stdout true; pr "%s" s; flush stdout
let print_string s = (!current_printer).printer_prinfo s
let print_generic label to_string to_json a = (!current_printer).printer_prgeneric label (fun () -> to_string a) (fun () -> to_json a)
let print_any s = (!current_printer).printer_prinfo (Marshal.to_string s [])
let strcat s1 s2 = s1 ^ s2
let concat_l sep (l:string list) = BatString.concat sep l

let string_of_unicode (bytes:int array) =
  BatArray.fold_left (fun acc b -> acc^(BatUTF8.init 1 (fun _ -> BatUChar.of_int b))) "" bytes
let unicode_of_string (string:string) =
  let n = BatUTF8.length string in
  let t = Array.make n 0 in
  let i = ref 0 in
  BatUTF8.iter (fun c -> t.(!i) <- BatUChar.code c; incr i) string;
  t
let base64_encode s = BatBase64.str_encode s
let base64_decode s = BatBase64.str_decode s
let char_of_int i = Z.to_int i
let int_of_string = Z.of_string
let safe_int_of_string x =
  if x = "" then None else
  try Some (int_of_string x) with Invalid_argument _ -> None
let int_of_char x = Z.of_int x
let int_of_byte x = x
let int_of_uint8 x = Z.of_int (Char.code x)
let uint16_of_int i = Z.to_int i
let byte_of_char c = c

let float_of_string s = float_of_string s
let float_of_byte b = float_of_int (Char.code b)
let float_of_int32 = float_of_int
let float_of_int64 = BatInt64.to_float

let int_of_int32 i = i
let int32_of_int i = BatInt32.of_int i

let string_of_int = Z.to_string
let string_of_bool = string_of_bool
let string_of_int32 = BatInt32.to_string
let string_of_int64 = BatInt64.to_string
let string_of_float = string_of_float
let string_of_char i = BatUTF8.init 1 (fun _ -> BatUChar.chr i)
let hex_string_of_byte (i:int) =
  let hs = spr "%x" i in
  if (String.length hs = 1) then "0" ^ hs
  else hs
let string_of_bytes = string_of_unicode
let bytes_of_string = unicode_of_string
let starts_with = BatString.starts_with
let trim_string = BatString.trim
let ends_with = BatString.ends_with
let char_at s index = BatUChar.code (BatUTF8.get s (Z.to_int index))
let is_upper c = 65 <= c && c <= 90
let contains (s1:string) (s2:string) = BatString.exists s1 s2
let substring_from s index = BatString.tail s (Z.to_int index)
let substring s i j = BatString.sub s (Z.to_int i) (Z.to_int j)
let replace_char (s:string) c1 c2 =
  let c1, c2 = BatUChar.chr c1, BatUChar.chr c2 in
  BatUTF8.map (fun x -> if x = c1 then c2 else x) s
let replace_chars (s:string) c (by:string) =
  BatString.replace_chars (fun x -> if x = Char.chr c then by else BatString.of_char x) s
let hashcode s = Z.of_int (StringOps.hash s)
let compare s1 s2 = Z.of_int (BatString.compare s1 s2)
let split s sep = BatString.split_on_string sep s
let splitlines s = split s "\n"

let iof = int_of_float
let foi = float_of_int

let print1 a b = print_string (format1 a b)
let print2 a b c = print_string (format2 a b c)
let print3 a b c d = print_string (format3 a b c d)
let print4 a b c d e = print_string (format4 a b c d e)
let print5 a b c d e f = print_string (format5 a b c d e f)
let print6 a b c d e f g = print_string (format6 a b c d e f g)
let print fmt args = print_string (format fmt args)

let print_error s = (!current_printer).printer_prerror s
let print1_error a b = print_error (format1 a b)
let print2_error a b c = print_error (format2 a b c)
let print3_error a b c d = print_error (format3 a b c d)

let print_warning s = (!current_printer).printer_prwarning s
let print1_warning a b = print_warning (format1 a b)
let print2_warning a b c = print_warning (format2 a b c)
let print3_warning a b c d = print_warning (format3 a b c d)

let fprint (oc:out_channel) fmt args : unit = Printf.fprintf oc "%s" (format fmt args)

[@@deriving yojson,show]

let is_left = function
  | FStar_Pervasives.Inl _ -> true
  | _ -> false

let is_right = function
  | FStar_Pervasives.Inr _ -> true
  | _ -> false

let left = function
  | FStar_Pervasives.Inl x -> x
  | _ -> failwith "Not in left"
let right = function
  | FStar_Pervasives.Inr x -> x
  | _ -> failwith "Not in right"

let (-<-) f g x = f (g x)

let find_dup f l =
  let rec aux = function
    | hd::tl ->
       let hds, tl' = BatList.partition (f hd) tl in
       (match hds with
        | [] -> aux tl'
        | _ -> Some hd)
    | _ -> None in
  aux l

let nodups f l = match find_dup f l with | None -> true | _ -> false

let remove_dups f l =
  let rec aux out = function
    | hd::tl -> let _, tl' = BatList.partition (f hd) tl in aux (hd::out) tl'
    | _ -> out in
  aux [] l

let is_none = function
  | None -> true
  | Some _ -> false

let is_some = function
  | None -> false
  | Some _ -> true

let must = function
  | Some x -> x
  | None -> failwith "Empty option"

let dflt x = function
  | None   -> x
  | Some x -> x

let find_opt f l =
  let rec aux = function
    | [] -> None
    | hd::tl -> if f hd then Some hd else aux tl in
  aux l

(* JP: why so many duplicates? :'( *)
let sort_with = FStar_List.sortWith

let bind_opt opt f =
  match opt with
  | None -> None
  | Some x -> f x

let catch_opt opt f =
  match opt with
  | Some x -> opt
  | None -> f ()

let map_opt opt f =
  match opt with
  | None -> None
  | Some x -> Some (f x)

let iter_opt opt f =
  ignore (map_opt opt f)

let rec find_map l f =
  match l with
  | [] -> None
  | x::tl ->
     match f x with
     | None -> find_map tl f
     | y -> y

let try_find f l = BatList.find_opt f l

let try_find_index f l =
  let rec aux i = function
    | [] -> None
    | hd::tl -> if f hd then Some (Z.of_int i) else aux (i+1) tl in
  aux 0 l

let fold_map f state s =
  let fold (state, acc) x =
    let state, v = f state x in (state, v :: acc) in
  let (state, rs) = BatList.fold_left fold (state, []) s in
  (state, BatList.rev rs)

let choose_map f state s =
  let fold (state, acc) x =
    match f state x with
    | state, None   -> (state, acc)
    | state, Some v -> (state, v :: acc) in
  let (state, rs) = BatList.fold_left fold (state, []) s in
  (state, BatList.rev rs)

let for_all f l = BatList.for_all f l
let for_some f l = BatList.exists f l
let forall_exists rel l1 l2 =
  for_all (fun x -> for_some (rel x) l2) l1
let multiset_equiv rel l1 l2 =
  BatList.length l1 = BatList.length l2 && forall_exists rel l1 l2
let take p l =
  let rec take_aux acc = function
    | [] -> l, []
    | x::xs when p x -> take_aux (x::acc) xs
    | x::xs -> List.rev acc, x::xs
  in take_aux [] l

let rec fold_flatten f acc l =
  match l with
  | [] -> acc
  | x :: xs -> let acc, xs' = f acc x in fold_flatten f acc (xs' @ xs)

let add_unique f x l =
  if for_some (f x) l then
    l
  else
    x::l

let first_N n l =
  let n = Z.to_int n in
  let rec f acc i l =
    if i = n then BatList.rev acc,l else
      match l with
      | h::tl -> f (h::acc) (i+1) tl
      | _     -> failwith "firstN"
  in
  f [] 0 l

let nth_tail n l =
  let rec aux n l =
    if n=0 then l else aux (n - 1) (BatList.tl l)
  in
  aux (Z.to_int n) l

let prefix l =
  match BatList.rev l with
  | hd::tl -> BatList.rev tl, hd
  | _ -> failwith "impossible"

let prefix_until f l =
  let rec aux prefix = function
    | [] -> None
    | hd::tl ->
       if f hd then Some (BatList.rev prefix, hd, tl)
       else aux (hd::prefix) tl in
  aux [] l

let string_to_ascii_bytes (s:string) : char array =
  BatArray.of_list (BatString.explode s)
let ascii_bytes_to_string (b:char array) : string =
  BatString.implode (BatArray.to_list b)
let mk_ref a = FStar_ST.alloc a

let write_file (fn:string) s =
  let fh = open_file_for_writing fn in
  append_to_file fh s;
  close_out_channel fh

let copy_file input_name output_name =
  (* see https://ocaml.github.io/ocamlunix/ocamlunix.html#sec33 *)
  let open Unix in
  let buffer_size = 8192 in
  let buffer = Bytes.create buffer_size in
  let fd_in = openfile input_name [O_RDONLY] 0 in
  let fd_out = openfile output_name [O_WRONLY; O_CREAT; O_TRUNC] 0o666 in
  let rec copy_loop () =
    match read fd_in buffer 0 buffer_size with
    |  0 -> ()
    | r -> ignore (write fd_out buffer 0 r); copy_loop ()
  in
  copy_loop ();
  close fd_in;
  close fd_out
let delete_file (fn:string) = Sys.remove fn
let file_get_contents f =
  let ic = open_in_bin f in
  let l = in_channel_length ic in
  let s = really_input_string ic l in
  close_in ic;
  s
let file_get_lines f =
  let ic = open_in f in
  let rec aux accu =
    let l =
      try
        Some (input_line ic)
      with
      | End_of_file -> None
    in
    match l with
    | None -> accu
    | Some l -> aux (l::accu)
  in
  let l = aux [] in
  close_in ic;
  List.rev l
let concat_dir_filename d f = Filename.concat d f

let slash_code : int =
  BatUChar.code (BatUChar.of_char '/')

let rec dropWhile f xs =
  match xs with
  | [] -> []
  | x::xs ->
    if f x
    then dropWhile f xs
    else x::xs

let path_parent (fn : string) : string =
  let cs = FStar_String.split [slash_code] fn in
  (* ^ Components of the path *)
  let cs = cs |> List.rev |> dropWhile (fun s -> s = "") |> List.rev in
  (* ^ Remove empty trailing components, so we interpret a/b/c/ as a/b/c *)
  (* Remove last component to get parent and concat. *)
  FStar_String.concat "/" (FStar_List.init cs)

let rec __mkdir clean mkparents nm =
  let remove_all_in_dir nm =
    let open Sys in
    Array.iter remove (Array.map (concat_dir_filename nm) (readdir nm)) in
  let open Unix in
  (match Sys.os_type with
  | "Unix" -> ignore (umask 0o002)
  | _ -> (* unimplemented*) ());
  try Unix.mkdir nm 0o777
  with
  | Unix_error (EEXIST, _, _) ->
    if clean then remove_all_in_dir nm

  (* failed due to nonexisting directory, mkparents is true, and nm has a slash:
      attempt to recursively create parent and retry. *)
  | Unix_error (ENOENT, _, _) when mkparents && FStar_String.index_of nm slash_code <> (Z.of_int (-1)) ->
    __mkdir false true (path_parent nm);
    Unix.mkdir nm 0o777

let mkdir = __mkdir

let for_range lo hi f =
  for i = Z.to_int lo to Z.to_int hi do
    f (Z.of_int i)
  done


let incr r = FStar_ST.(Z.(write r (read r + one)))
let decr r = FStar_ST.(Z.(write r (read r - one)))
let geq (i:int) (j:int) = i >= j

let exec_name = Sys.executable_name
let get_exec_dir () = Filename.dirname (Sys.executable_name)
let get_cmd_args () = Array.to_list Sys.argv
let expand_environment_variable x = try Some (Sys.getenv x) with Not_found -> None

let physical_equality (x:'a) (y:'a) = x == y
let check_sharing a b msg = if physical_equality a b then print1 "Sharing OK: %s\n" msg else print1 "Sharing broken in %s\n" msg

type oWriter = {
  write_byte: char -> unit;
  write_bool: bool -> unit;
  write_int: int -> unit;
  write_int32: int32 -> unit;
  write_int64: int64 -> unit;
  write_char: char -> unit;
  write_double: float -> unit;
  write_bytearray: char array -> unit;
  write_string: string -> unit;

  close: unit -> unit
}

type oReader = {
  read_byte: unit -> char;
  read_bool: unit -> bool;
  read_int: unit -> int;
  read_int32: unit -> int32;
  read_int64: unit -> int64;
  read_char: unit -> char;
  read_double: unit -> float;
  read_bytearray: unit -> char array;
  read_string: unit -> string;

  close: unit -> unit
}

module MkoReader = struct
  let read_byte r x = r.read_byte x
  let read_bool r x = r.read_bool x
  let read_int r x = r.read_int32 x
  let read_int32 r x = r.read_int32 x
  let read_int64 r x = r.read_int64 x
  let read_char r x = r.read_char x
  let read_double r x = r.read_double x
  let read_bytearray r x = r.read_bytearray x
  let read_string r x = r.read_string x

  let close r x = r.close x
end

module MkoWriter = struct
  let write_byte w x = w.write_byte x
  let write_bool w x = w.write_bool x
  let write_int w x = w.write_int32 x
  let write_int32 w x = w.write_int32 x
  let write_int64 w x = w.write_int64 x
  let write_char w x = w.write_char x
  let write_double w x = w.write_double x
  let write_bytearray w x = w.write_bytearray x
  let write_string w x = w.write_string x

  let close w x = w.close x
end

(*
 * TODO: these functions need to be filled in
 *)
let get_owriter (filename:string) : oWriter = {
  write_byte = (fun _ -> ());
  write_bool = (fun _ -> ());
  write_int = (fun _ -> ());
  write_int32 = (fun _ -> ());
  write_int64 = (fun _ -> ());
  write_char = (fun _ -> ());
  write_double = (fun _ -> ());
  write_bytearray = (fun _ -> ());
  write_string = (fun _ -> ());

  close = (fun _ -> ());
}

let get_oreader (filename:string) : oReader = {
  read_byte = (fun _ -> 'a');
  read_bool = (fun _ -> true);
  read_int = (fun _ -> 0);
  read_int32 = (fun _ -> failwith "NYI");
  read_int64 = (fun _ -> 0L);
  read_char = (fun _ -> 'a');
  read_double = (fun _ -> 0.0);
  read_bytearray = (fun _ -> [||]);
  read_string = (fun _ -> "");

  close = (fun _ -> ());
}

let getcwd = Sys.getcwd

let readdir dir = "." :: ".." :: Array.to_list (Sys.readdir dir)

let paths_to_same_file f g =
  let open Unix in
  let { st_dev = i; st_ino = j } = stat f in
  let { st_dev = i'; st_ino = j' } = stat g in
  (i,j) = (i',j')

let file_exists = Sys.file_exists
(* Sys.is_directory raises Sys_error if the path does not exist *)
let is_directory f = Sys.file_exists f && Sys.is_directory f


let basename = Filename.basename
let dirname = Filename.dirname
let print_endline = print_endline

let map_option f opt = BatOption.map f opt

let save_value_to_file (fname:string) value =
  (* BatFile.with_file_out uses Unix.openfile (which isn't available in
     js_of_ocaml) instead of Pervasives.open_out, so we don't use it here. *)
  let channel = open_out_bin fname in
  BatPervasives.finally
    (fun () -> close_out channel)
    (fun channel -> output_value channel value)
    channel

let load_value_from_file (fname:string) =
  (* BatFile.with_file_in uses Unix.openfile (which isn't available in
     js_of_ocaml) instead of Pervasives.open_in, so we don't use it here. *)
  try
    let channel = open_in_bin fname in
    BatPervasives.finally
      (fun () -> close_in channel)
      (fun channel -> Some (input_value channel))
      channel
  with | _ -> None

let save_2values_to_file (fname:string) value1 value2 =
  try
    let channel = open_out_bin fname in
    BatPervasives.finally
      (fun () -> close_out channel)
      (fun channel ->
        output_value channel value1;
        output_value channel value2)
      channel
  with
  | e -> delete_file fname;
         raise e

let load_2values_from_file (fname:string) =
  try
    let channel = open_in_bin fname in
    BatPervasives.finally
      (fun () -> close_in channel)
      (fun channel ->
        let v1 = input_value channel in
        let v2 = input_value channel in
        Some (v1, v2))
      channel
  with | _ -> None

let print_exn e =
  Printexc.to_string e

let digest_of_file =
  let cache = smap_create (Z.of_int 101) in
  fun (fname:string) ->
    match smap_try_find cache fname with
    | Some dig -> dig
    | None ->
      let dig = BatDigest.file fname in
      smap_add cache fname dig;
      dig

let digest_of_string (s:string) =
  BatDigest.to_hex (BatDigest.string s)

(* Precondition: file exists *)
let touch_file (fname:string) : unit =
  (* Sets access and modification times to current time *)
  Unix.utimes fname 0.0 0.0

let ensure_decimal s = Z.to_string (Z.of_string s)

let measure_execution_time tag f =
  let t = Sys.time () in
  let retv = f () in
  print2 "Execution time of %s: %s ms\n" tag (string_of_float (1000.0 *. (Sys.time() -. t)));
  retv

let return_execution_time f =
  let t1 = Sys.time () in
  let retv = f () in
  let t2 = Sys.time () in
  (retv, 1000.0 *. (t2 -. t1))

(* Outside of this file the reference to FStar_Util.ref must use the following combinators *)
(* Export it at the end of the file so that we don't break other internal uses of ref *)
type 'a ref = 'a FStar_Monotonic_Heap.ref
let read = FStar_ST.read
let write = FStar_ST.write
let (!) = FStar_ST.read
let (:=) = FStar_ST.write

let marshal (x:'a) : string = Marshal.to_string x []
let unmarshal (x:string) : 'a = Marshal.from_string x 0

type signedness = | Unsigned | Signed
type width = | Int8 | Int16 | Int32 | Int64

let rec z_pow2 n =
  if n = Z.zero then Z.one
  else Z.mul (Z.of_string "2") (z_pow2 (Z.sub n Z.one))

let bounds signedness width =
    let n =
        match width with
        | Int8 -> Z.of_string "8"
        | Int16 -> Z.of_string "16"
        | Int32 -> Z.of_string "32"
        | Int64 -> Z.of_string "64"
    in
    let lower, upper =
      match signedness with
      | Unsigned ->
        Z.zero, Z.sub (z_pow2 n) Z.one
      | Signed ->
        let upper = z_pow2 (Z.sub n Z.one) in
        Z.neg upper, Z.sub upper Z.one
    in
    lower, upper

let within_bounds repr signedness width =
  let lower, upper = bounds signedness width in
  let value = Z.of_string (ensure_decimal repr) in
  Z.leq lower value && Z.leq value upper

let print_array (f: 'a -> string) 
                (s: 'a array)
  : string 
  = let ls = Array.fold_left (fun out a -> f a  :: out) [] s in
    format1 "[| %s |]" (String.concat "; " (List.rev ls))

let array_of_list (l:'a list) = FStar_ImmutableArray_Base.of_list l

let array_length (l:'a FStar_ImmutableArray_Base.t) = FStar_ImmutableArray_Base.length l

let array_index (l:'a FStar_ImmutableArray_Base.t) (i:Z.t) = FStar_ImmutableArray_Base.index l i

let putenv k v = Unix.putenv k v
let execvp c args = Unix.execvp c (Array.of_list args)
