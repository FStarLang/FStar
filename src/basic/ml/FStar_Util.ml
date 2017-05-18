let max_int = Z.of_int max_int
let is_letter_or_digit c = (BatChar.is_digit c) || (BatChar.is_letter c)
let is_symbol c = BatChar.is_symbol c

(* Modeled after: Char.IsPunctuation in .NET
   (http://www.dotnetperls.com/char-ispunctuation)
*)
let is_punctuation c = (
    c = '!' ||
    c = '"' ||
    c = '#' ||
    c = '%' ||
    c = '&' ||
    c = '\'' ||
    c = '(' ||
    c = ')' ||
    c = '*' ||
    c = ',' ||
    c = '-' ||
    c = '.' ||
    c = '/' ||
    c = ':' ||
    c = ';' ||
    c = '?' ||
    c = '@' ||
    c = '[' ||
    c = '\\' ||
    c = ']' ||
    c = '_' ||
    c = '{' ||
    c = '}'
  )

let return_all x = x

type time = float
let now () = BatUnix.gettimeofday ()
let time_diff (t1:time) (t2:time) : float * Prims.int =
  let n = t2 -. t1 in
  n,
  Z.of_float (n *. 1000.0)
let record_time f =
    let start = now () in
    let res = f () in
    let _, elapsed = time_diff start (now()) in
    res, elapsed
let get_file_last_modification_time f = (BatUnix.stat f).st_mtime
let is_before t1 t2 = compare t1 t2 < 0
let string_of_time = string_of_float

exception Impos
exception NYI of string
exception Failure of string

type proc =
    {inc : in_channel;
     outc : out_channel;
     mutable killed : bool;
     id : string}

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

let atomically =
  (* let mutex = Mutex.create () in *)
  fun f -> f ()
(*fun f -> Mutex.lock mutex; let r = f () in Mutex.unlock mutex; r*)

let spawn f =
  let _ = Thread.create f () in ()

let write_input in_write input =
  output_string in_write input;
  flush in_write

(*let cnt = ref 0*)

let launch_process (id:string) (prog:string) (args:string) (input:string) (cond:string -> string -> bool): string =
  (*let fc = open_out ("tmp/q"^(string_of_int !cnt)) in
  output_string fc input;
  close_out fc;*)
  let cmd = prog^" "^args in
  let (to_chd_r, to_chd_w) = Unix.pipe () in
  let (from_chd_r, from_chd_w) = Unix.pipe () in
  Unix.set_close_on_exec to_chd_w;
  Unix.set_close_on_exec from_chd_r;
  let pid = Unix.create_process "/bin/sh" [| "/bin/sh"; "-c"; cmd |]
  (*let pid = Unix.create_process "/bin/sh" [| "/bin/sh"; "-c"; ("run.sh "^(string_of_int (!cnt)))^" | " ^ cmd |]*)
                               to_chd_r from_chd_w Unix.stderr
  in
  (*cnt := !cnt +1;*)
  Unix.close from_chd_w;
  Unix.close to_chd_r;
  let cin = Unix.in_channel_of_descr from_chd_r in
  let cout = Unix.out_channel_of_descr to_chd_w in

  (* parallel reading thread *)
  let out = Buffer.create 16 in
  let rec read_out _ =
    let s, eof = (try
                    BatString.trim (input_line cin), false
                  with End_of_file ->
                    Buffer.add_string out ("\nkilled\n") ; "", true) in
    if not eof then
      if s = "Done!" then ()
      else (Buffer.add_string out (s ^ "\n"); read_out ())  in
  let child_thread = Thread.create (fun _ -> read_out ()) () in

  (* writing to z3 *)
  write_input cout input;
  close_out cout;

  (* waiting for z3 to finish *)
  Thread.join child_thread;
  close_in cin;
  Buffer.contents out

let start_process (id:string) (prog:string) (args:string) (cond:string -> string -> bool) : proc =
  let command = prog^" "^args in
  let (inc,outc) = Unix.open_process command in
  let proc = {inc = inc; outc = outc; killed = false; id = prog^":"^id} in
  all_procs := proc::!all_procs;
  proc

let ask_process (p:proc) (stdin:string) : string =
  let out = Buffer.create 16 in

  let rec read_out _ =
    let s, eof = (try
                    BatString.trim (input_line p.inc), false
                  with End_of_file ->
                    Buffer.add_string out ("\nkilled\n") ; "", true) in
    if not eof then
      if s = "Done!" then ()
      else (Buffer.add_string out (s ^ "\n"); read_out ())
  in

  let child_thread = Thread.create (fun _ -> read_out ()) () in
  output_string p.outc stdin;
  flush p.outc;
  Thread.join child_thread;
  Buffer.contents out

let kill_process (p:proc) =
  let _ = Unix.close_process (p.inc, p.outc) in
  p.killed <- true

let kill_all () =
  FStar_List.iter (fun p -> if not p.killed then kill_process p) !all_procs

let run_proc (name:string) (args:string) (stdin:string) : bool * string * string =
  let command = name^" "^args in
  let (inc,outc,errc) = Unix.open_process_full command (Unix.environment ()) in
  output_string outc stdin;
  flush outc;
  let res = BatPervasives.input_all inc in
  let err = BatPervasives.input_all errc in
  let _ = Unix.close_process_full (inc, outc, errc) in
  (true, res, err)

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

type string_builder = BatBuffer.t
let new_string_builder () = BatBuffer.create 256
let clear_string_builder b = BatBuffer.clear b
let string_of_string_builder b = BatBuffer.contents b
let string_builder_append b s = BatBuffer.add_string b s

let message_of_exn (e:exn) = Printexc.to_string e
let trace_of_exn (e:exn) = Printexc.get_backtrace ()

type 'a set = ('a list) * ('a -> 'a -> bool)

let set_is_empty ((s, _):'a set) =
  match s with
  | [] -> true
  | _ -> false

let new_set (cmp:'a -> 'a -> Z.t) (hash:'a -> Z.t) : 'a set =
  ([], fun x y -> cmp x y = Z.zero)

let set_elements ((s1, eq):'a set) : 'a list =
  let rec aux out = function
    | [] -> out
    | hd::tl ->
       if BatList.exists (eq hd) out then
         aux out tl
       else
         aux (hd::out) tl in
  aux [] s1
let set_add a ((s, b):'a set) = (a::s, b)
let set_remove x ((s1, eq):'a set) =
  (BatList.filter (fun y -> not (eq x y)) s1, eq)
let set_mem a ((s, b):'a set) = BatList.exists (b a) s
let set_union ((s1, b):'a set) ((s2, _):'a set) = (s1@s2, b)
let set_intersect ((s1, eq):'a set) ((s2, _):'a set) =
  (BatList.filter (fun y -> BatList.exists (eq y) s2) s1, eq)
let set_is_subset_of ((s1, eq):'a set) ((s2, _):'a set) =
  BatList.for_all (fun y -> BatList.exists (eq y) s2) s1
let set_count ((s1, _):'a set) = Z.of_int (BatList.length s1)
let set_difference ((s1, eq):'a set) ((s2, _):'a set) : 'a set =
  (BatList.filter (fun y -> not (BatList.exists (eq y) s2)) s1, eq)


(* See ../Util.fsi for documentation and ../Util.fs for implementation details *)
type 'a fifo_set = ('a list) * ('a -> 'a -> bool)

let fifo_set_is_empty ((s, _):'a fifo_set) =
  match s with
  | [] -> true
  | _ -> false

let new_fifo_set (cmp:'a -> 'a -> Z.t) (hash:'a -> Z.t) : 'a fifo_set =
  ([], fun x y -> cmp x y = Z.zero)

let fifo_set_elements ((s1, eq):'a fifo_set) : 'a list =
  let rec aux out = function
    | [] -> out
    | hd::tl ->
       if BatList.exists (eq hd) tl then
         aux out tl
       else
         aux (hd::out) tl in
  aux [] s1
let fifo_set_add a ((s, b):'a fifo_set) = (a::s, b)
let fifo_set_remove x ((s1, eq):'a fifo_set) =
  (BatList.filter (fun y -> not (eq x y)) s1, eq)
let fifo_set_mem a ((s, b):'a fifo_set) = BatList.exists (b a) s
let fifo_set_union ((s1, b):'a fifo_set) ((s2, _):'a fifo_set) = (s2@s1, b)
let fifo_set_count ((s1, _):'a fifo_set) = Z.of_int (BatList.length s1)
let fifo_set_difference ((s1, eq):'a fifo_set) ((s2, _):'a fifo_set) : 'a fifo_set =
  (BatList.filter (fun y -> not (BatList.exists (eq y) s2)) s1, eq)

type 'value smap = (string, 'value) BatHashtbl.t
let smap_create (i:Z.t) : 'value smap = BatHashtbl.create (Z.to_int i)
let smap_clear (s:('value smap)) = BatHashtbl.clear s
let smap_add (m:'value smap) k (v:'value) = BatHashtbl.add m k v
let smap_of_list (l: (string * 'value) list) =
  let s = BatHashtbl.create (BatList.length l) in
  FStar_List.iter (fun (x,y) -> smap_add s x y) l;
  s
let smap_try_find (m:'value smap) k = BatHashtbl.find_option m k
let smap_fold (m:'value smap) f a = BatHashtbl.fold f m a
let smap_remove (m:'value smap) k = BatHashtbl.remove m k
let smap_keys (m:'value smap) = smap_fold m (fun k _ acc -> k::acc) []
let smap_copy (m:'value smap) = BatHashtbl.copy m
let smap_size (m:'value smap) = BatHashtbl.length m

type 'value imap = (Z.t, 'value) BatHashtbl.t
let imap_create (i:Z.t) : 'value imap = BatHashtbl.create (Z.to_int i)
let imap_clear (s:('value imap)) = BatHashtbl.clear s
let imap_add (m:'value imap) k (v:'value) = BatHashtbl.add m k v
let imap_of_list (l: (Z.t * 'value) list) =
  let s = BatHashtbl.create (BatList.length l) in
  FStar_List.iter (fun (x,y) -> imap_add s x y) l;
  s
let imap_try_find (m:'value imap) k = BatHashtbl.find_option m k
let imap_fold (m:'value imap) f a = BatHashtbl.fold f m a
let imap_remove (m:'value imap) k = BatHashtbl.remove m k
let imap_keys (m:'value imap) = imap_fold m (fun k _ acc -> k::acc) []
let imap_copy (m:'value imap) = BatHashtbl.copy m

let format (fmt:string) (args:string list) =
  let frags = BatString.nsplit fmt "%s" in
  if BatList.length frags <> BatList.length args + 1 then
    failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (Pervasives.string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
  else
    let args = args@[""] in
    BatList.fold_left2 (fun out frag arg -> out ^ frag ^ arg) "" frags args

let format1 f a = format f [a]
let format2 f a b = format f [a;b]
let format3 f a b c = format f [a;b;c]
let format4 f a b c d = format f [a;b;c;d]
let format5 f a b c d e = format f [a;b;c;d;e]
let format6 f a b c d e g = format f [a;b;c;d;e;g]

let stdout_isatty () = Some (Unix.isatty Unix.stdout)

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

let colorize_cyan s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[36;1m" s "\x1b[0m"
  | _ -> s

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

type printer = {
  printer_prinfo: string -> unit;
  printer_prwarning: string -> unit;
  printer_prerror: string -> unit;
}

let default_printer =
  { printer_prinfo = (fun s -> pr "%s" s; flush stdout);
    printer_prwarning = (fun s -> fpr stderr "%s" (colorize_cyan s); flush stdout; flush stderr);
    printer_prerror = (fun s -> fpr stderr "%s" (colorize_red s); flush stdout; flush stderr); }

let current_printer = ref default_printer
let set_printer printer = current_printer := printer

let print_raw s = pr "%s" s; flush stdout
let print_string s = (!current_printer).printer_prinfo s
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

let char_of_int i = char_of_int (Z.to_int i)
let int_of_string = Z.of_string
let int_of_char x= Z.of_int (Char.code x)
let int_of_byte x = x
let int_of_uint8 = int_of_char
let uint16_of_int i = Z.to_int i
let byte_of_char (c:char) = Char.code c

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
let string_of_char  (i:char) = spr "%c" i
let hex_string_of_byte (i:int) =
  let hs = spr "%x" i in
  if (String.length hs = 1) then "0" ^ hs
  else hs
let string_of_bytes = string_of_unicode
let bytes_of_string = unicode_of_string
let starts_with = BatString.starts_with
let trim_string = BatString.trim
let ends_with = BatString.ends_with
let char_at s index = BatString.get s (Z.to_int index)
let is_upper (c:char) = 'A' <= c && c <= 'Z'
let contains (s1:string) (s2:string) = BatString.exists s1 s2
let substring_from s index = BatString.tail s (Z.to_int index)
let substring s i j= BatString.sub s (Z.to_int i) (Z.to_int j)
let replace_char (s:string) (c1:char) (c2:char) =
  BatString.map (fun c -> if c = c1 then c2 else c) s
let replace_chars (s:string) (c:char) (by:string) =
  BatString.replace_chars (fun x -> if x=c then by else BatString.of_char x) s
let hashcode s = Z.of_int (BatHashtbl.hash s)
let compare s1 s2 = Z.of_int (BatString.compare s1 s2)
let split s sep = if s = "" then [""] else BatString.nsplit s sep
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

let stderr = stderr
let stdout = stdout

let fprint oc fmt args = Printf.fprintf oc "%s" (format fmt args)

type ('a,'b) either =
  | Inl of 'a
  | Inr of 'b

let is_left = function
  | Inl _ -> true
  | _ -> false

let is_right = function
  | Inr _ -> true
  | _ -> false

let left = function
  | Inl x -> x
  | _ -> failwith "Not in left"
let right = function
  | Inr x -> x
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

let set_eq (f: 'a -> 'a -> Z.t) (l1: 'a list) (l2: 'a list) =
  let l1 = sort_with f l1 in
  let l2 = sort_with f l2 in
  BatList.for_all2 (fun l1 l2 -> f l1 l2 = Z.zero) l1 l2

let bind_opt opt f =
  match opt with
  | None -> None
  | Some x -> f x

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

let try_find f l = try Some (List.find f l) with Not_found -> None

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

let rec nth_tail n l =
  if n=0 then l else nth_tail (n - 1) (BatList.tl l)

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

(* A simple state monad *)
type ('s,'a) state = 's -> ('a*'s)
let get : ('s,'s) state = fun s -> (s,s)
let upd (f:'s -> 's) : ('s,unit) state = fun s -> ((), f s)
let put (s:'s) : ('s,unit) state = fun _ -> ((), s)
let ret (x:'a) : ('s,'a) state = fun s -> (x, s)
let bind (sa:('s,'a) state) (f : 'a -> ('s,'b) state) : ('s,'b) state =
  fun s1 -> let (a, s2) = sa s1 in f a s2
let (>>) s f = bind s f
let run_st init (s:('s,'a) state) = s init

let rec stmap (l:'a list) (f: 'a -> ('s,'b) state) : ('s, ('b list)) state =
  match l with
  | [] -> ret []
  | hd::tl -> bind (f hd)
                   (fun b ->
                    let stl = stmap tl f in
                    bind stl (fun tl -> ret (b::tl)))

let stmapi (l:'a list) (f:int -> 'a -> ('s, 'b) state) : ('s, ('b list)) state =
  let rec aux i l =
    match l with
    | [] -> ret []
    | hd::tl ->
       bind (f i hd)
            (fun b ->
             let stl = aux (i + 1) tl in
             bind stl (fun tl -> ret (b::tl))) in
  aux 0 l

let rec stiter (l:'a list) (f: 'a -> ('s,unit) state) : ('s,unit) state =
  match l with
  | [] -> ret ()
  | hd::tl -> bind (f hd) (fun () -> stiter tl f)

let rec stfoldr_pfx (l:'a list) (f: 'a list -> 'a -> ('s,unit) state) : ('s,unit) state =
  match l with
  | [] -> ret ()
  | hd::tl -> (stfoldr_pfx tl f) >> (fun _ -> f tl hd)

let rec stfold (init:'b) (l:'a list) (f: 'b -> 'a -> ('s,'b) state) : ('s,'b) state =
  match l with
  | [] -> ret init
  | hd::tl -> (f init hd) >> (fun next -> stfold next tl f)

type file_handle = out_channel
let open_file_for_writing (fn:string) : file_handle = open_out_bin fn
let append_to_file (fh:file_handle) s = fpr fh "%s\n" s; flush fh
let close_file (fh:file_handle) = close_out fh
let write_file (fn:string) s =
  let fh = open_file_for_writing fn in
  append_to_file fh s;
  close_file fh
let flush_file (fh:file_handle) = flush fh
let file_get_contents f =
  let ic = open_in_bin f in
  let l = in_channel_length ic in
  let s = really_input_string ic l in
  close_in ic;
  s
let concat_dir_filename d f = Filename.concat d f
let mkdir clean nm =
  let remove_all_in_dir nm =
    let open Sys in
    Array.iter remove (Array.map (concat_dir_filename nm) (readdir nm)) in
  let open Unix in
  (match Sys.os_type with
  | "Unix" -> ignore (umask 0o002)
  | _ -> (* unimplemented*) ());
  try mkdir nm 0o777
  with Unix_error (EEXIST,_,_) ->
    if clean then remove_all_in_dir nm

let for_range lo hi f =
  for i = Z.to_int lo to Z.to_int hi do
    f (Z.of_int i)
  done


let incr r = FStar_ST.(Z.(write r (read r + one)))
let decr r = FStar_ST.(Z.(write r (read r - one)))
let geq (i:int) (j:int) = i >= j

let get_exec_dir () = Filename.dirname (Sys.executable_name)
let expand_environment_variable x = try Sys.getenv x with Not_found -> ""

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

let getcwd = Unix.getcwd

let readdir dir =
  let handle = Unix.opendir dir in
  let files = ref [] in
  try
    while true do
      files := Unix.readdir handle :: !files
    done;
    assert false
  with End_of_file ->
    !files

let file_exists = Sys.file_exists
let basename = Filename.basename
let print_endline = print_endline

let map_option f opt = BatOption.map f opt

let save_value_to_file (fname:string) value =
  BatFile.with_file_out
    fname
    (fun f ->
      BatPervasives.output_value f value)

let load_value_from_file (fname:string) =
  try
    BatFile.with_file_in
      fname
      (fun f ->
        Some (BatPervasives.input_value f))
  with
  | _ ->
    None

let print_exn e =
  Printexc.to_string e

let digest_of_file (fname:string) =
  BatDigest.file fname

let digest_of_string (s:string) =
  BatDigest.to_hex (BatDigest.string s)

let ensure_decimal s = Z.to_string (Z.of_string s)


(** Hints. *)
type hint = {
    hint_name: string;
    hint_index: Z.t;
    fuel:Z.t;
    ifuel:Z.t;
    unsat_core: string list option;
    query_elapsed_time:Z.t
}

type hints = hint option list

type hints_db = {
    module_digest:string;
    hints: hints
}

let write_hints (filename: string) (hints: hints_db): unit =
  let json = `List [
    `String hints.module_digest;
    `List (List.map (function
      | None -> `Null
      | Some { hint_name; hint_index; fuel; ifuel; unsat_core; query_elapsed_time } ->
          `List [
	    `String hint_name;
	    `Int (Z.to_int hint_index);
            `Int (Z.to_int fuel);
            `Int (Z.to_int ifuel);
            (match unsat_core with
            | None -> `Null
            | Some strings ->
                `List (List.map (fun s -> `String s) strings));
            `Int (Z.to_int query_elapsed_time)
          ]
    ) hints.hints)
  ] in
  Yojson.Safe.pretty_to_channel (open_out_bin filename) json

let read_hints (filename: string): hints_db option =
    try
    let chan = open_in filename in
    let json = Yojson.Safe.from_channel chan in
    close_in chan;
    Some (match json with
    | `List [
        `String module_digest;
        `List hints
      ] ->
        {
          module_digest;
          hints = List.map (function
            | `Null -> None
            | `List [
		`String hint_name;
		`Int hint_index;
                `Int fuel;
                `Int ifuel;
                unsat_core;
                `Int query_elapsed_time
              ] ->
                Some {
		  hint_name;
		  hint_index = Z.of_int hint_index;
                  fuel = Z.of_int fuel;
                  ifuel = Z.of_int ifuel;
                  unsat_core = begin match unsat_core with
                    | `Null ->
                        None
                    | `List strings ->
                        Some (List.map (function
                          | `String s -> s
                          | _ -> raise Exit
                        ) strings)
                    |  _ ->
                        raise Exit
                  end;
                  query_elapsed_time = Z.of_int query_elapsed_time
                }
              | _ ->
                 raise Exit
          ) hints
        }
    | _ ->
        raise Exit
    )
  with
   | Exit ->
      Printf.eprintf "Warning: Malformed JSON hints file: %s; ran without hints\n" filename;
      None
   | Sys_error _ ->
      Printf.eprintf "Warning: Unable to open hints file: %s; ran without hints\n" filename;
      None

(** Interactive protocol **)

type json =
| JsonNull
| JsonBool of bool
| JsonInt of Z.t
| JsonStr of string
| JsonList of json list
| JsonAssoc of (string * json) list

exception UnsupportedJson

let json_of_yojson yjs: json option =
  let rec aux yjs =
    match yjs with
    | `Null -> JsonNull
    | `Bool b -> JsonBool b
    | `Int i -> JsonInt (Z.of_int i)
    | `String s -> JsonStr s
    | `List l -> JsonList (List.map aux l)
    | `Assoc a -> JsonAssoc (List.map (fun (k, v) -> (k, aux v)) a)
    | _ -> raise UnsupportedJson in
  try Some (aux yjs) with UnsupportedJson -> None

let rec yojson_of_json js =
  match js with
  | JsonNull -> `Null
  | JsonBool b -> `Bool b
  | JsonInt i -> `Int (Z.to_int i)
  | JsonStr s -> `String s
  | JsonList l -> `List (List.map yojson_of_json l)
  | JsonAssoc a -> `Assoc (List.map (fun (k, v) -> (k, yojson_of_json v)) a)

let json_of_string str : json option =
  let open Yojson.Basic in
  try
    json_of_yojson (Yojson.Basic.from_string str)
  with Yojson.Json_error _ -> None

let string_of_json json =
  Yojson.Basic.to_string (yojson_of_json json)

(* Outside of this file the reference to FStar_Util.ref must use the following combinators *)
(* Export it at the end of the file so that we don't break other internal uses of ref *)
type 'a ref = 'a FStar_Heap.ref
let read = FStar_ST.read
let write = FStar_ST.write
let (!) = FStar_ST.read
let (:=) = FStar_ST.write
