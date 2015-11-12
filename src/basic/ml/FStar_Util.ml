let max_int = max_int
let is_letter_or_digit c = (BatChar.is_digit c) || (BatChar.is_letter c)
let is_symbol c = BatChar.is_symbol c

(* Modeled after: Char.IsPunctuation in .NET
   (http://www.dotnetperls.com/char-ispunctuation) *)
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
let sleep n = Thread.delay ((float_of_int n) /. 1000.)

let monitor_enter _ = ()
let monitor_exit _ = ()
let monitor_wait _ = ()
let monitor_pulse _ = ()
let current_tid _ = 0

let atomically =
  (* let mutex = Mutex.create () in *)
  fun f -> f ()
(*fun f -> Mutex.lock mutex; let r = f () in Mutex.unlock mutex; r*)

let spawn f =
  let _ = Thread.create f () in ()

let start_process (id:string) (prog:string) (args:string) (cond:string -> string -> bool) : proc =
  let command = prog^" "^args in
  let (inc,outc) = Unix.open_process command in
  let proc = {inc = inc; outc = outc; killed = false; id = prog^":"^id} in
  all_procs := proc::!all_procs;
  proc

let ask_process (p:proc) (stdin:string) : string =
  let out = Buffer.create 16 in

  let rec read_out _ =
    let s = BatString.trim (input_line p.inc) in
    if s = "Done!" then ()
    else
      (Buffer.add_string out (s ^ "\n"); read_out ())
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
  let (inc,outc) = Unix.open_process command in
  output_string outc stdin;
  flush outc;
  let res = BatPervasives.input_all inc in
  let _ = Unix.close_process (inc, outc) in
  (true, res, "")

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

let new_set (cmp:'a -> 'a -> int) (hash:'a -> int) : 'a set =
  ([], fun x y -> cmp x y = 0)

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
let set_count ((s1, _):'a set) = BatList.length s1
let set_difference ((s1, eq):'a set) ((s2, _):'a set) : 'a set =
  (BatList.filter (fun y -> not (BatList.exists (eq y) s2)) s1, eq)

type 'value smap = (string, 'value) BatHashtbl.t
let smap_create (i:int) : 'value smap = BatHashtbl.create i
let smap_clear (s:('value smap)) = BatHashtbl.clear s
let smap_add (m:'value smap) k (v:'value) = BatHashtbl.add m k v
let smap_of_list (l: (string * 'value) list) =
  let s = smap_create (FStar_List.length l) in
  FStar_List.iter (fun (x,y) -> smap_add s x y) l;
  s
let smap_try_find (m:'value smap) k = BatHashtbl.find_option m k
let smap_fold (m:'value smap) f a = BatHashtbl.fold f m a
let smap_remove (m:'value smap) k = BatHashtbl.remove m k
let smap_keys (m:'value smap) = smap_fold m (fun k _ acc -> k::acc) []
let smap_copy (m:'value smap) = BatHashtbl.copy m

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let print_string s = pr "%s" s; flush stdout
let print_any s = output_value stdout s; flush stdout
let strcat s1 s2 = s1 ^ s2
let concat_l sep (l:string list) = BatString.concat sep l

let string_of_unicode (bytes:char array) =
  BatArray.fold_left (fun acc b -> acc^(BatUTF8.init 1 (fun _ -> BatUChar.of_char b))) "" bytes
let unicode_of_string (string:string) =
  let n = BatUTF8.length string in
  let t = Array.make n 'x' in
  let i = ref 0 in
  BatUTF8.iter (fun c -> t.(!i) <- BatUChar.char_of c; incr i) string;
  t

let char_of_int = char_of_int
let int_of_string = int_of_string
let int_of_char = int_of_char
let int_of_byte = int_of_char
let int_of_uint8 = int_of_char
let uint16_of_int (i:int) = i
let byte_of_char (c:char) = c

let float_of_byte b = float_of_int (int_of_char b)
let float_of_int32 = float_of_int
let float_of_int64 = BatInt64.to_float

let int_of_int32 i = i
let int32_of_int i = BatInt32.of_int i

let string_of_int = string_of_int
let string_of_int32 = BatInt32.to_string
let string_of_int64 = BatInt64.to_string
let string_of_float = string_of_float
let string_of_char  (i:char) = spr "%c" i
let hex_string_of_byte (i:char) =
  let hs = spr "%x" (int_of_char i) in
  if (String.length hs = 1) then "0" ^ hs
  else hs
let string_of_bytes = string_of_unicode
let starts_with = BatString.starts_with
let trim_string = BatString.trim
let ends_with = BatString.ends_with
let char_at = BatString.get
let is_upper (c:char) = 'A' <= c && c <= 'Z'
let substring_from = BatString.tail
let substring = BatString.sub
let replace_char (s:string) (c1:char) (c2:char) =
  BatString.map (fun c -> if c = c1 then c2 else c) s
let replace_string (s:string) (s1:string) (s2:string) =
  BatString.rev (BatString.nreplace ~str:(BatString.rev s) ~sub:s1 ~by:s2)
let hashcode s = BatHashtbl.hash s
let compare s1 s2 = BatString.compare s1 s2
let splitlines s = BatString.nsplit s "\n"
let split s sep = BatString.nsplit s sep

let iof = int_of_float
let foi = float_of_int

let format (fmt:string) (args:string list) =
  let frags = BatString.nsplit fmt "%s" in
  if BatList.length frags <> BatList.length args + 1 then
    failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
  else
    let args = args@[""] in
    BatList.fold_left2 (fun out frag arg -> out ^ frag ^ arg) "" frags args

let format1 f a = format f [a]
let format2 f a b = format f [a;b]
let format3 f a b c = format f [a;b;c]
let format4 f a b c d = format f [a;b;c;d]
let format5 f a b c d e = format f [a;b;c;d;e]
let format6 f a b c d e g = format f [a;b;c;d;e;g]

let fprint1 a b = print_string (format1 a b)
let fprint2 a b c = print_string (format2 a b c)
let fprint3 a b c d = print_string (format3 a b c d)
let fprint4 a b c d e = print_string (format4 a b c d e)
let fprint5 a b c d e f = print_string (format5 a b c d e f)
let fprint6 a b c d e f g = print_string (format6 a b c d e f g)

type ('a,'b) either =
  | Inl of 'a
  | Inr of 'b

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

let sort_with = BatList.sort

let set_eq f l1 l2 =
  let l1 = sort_with f l1 in
  let l2 = sort_with f l2 in
  BatList.for_all2 (fun l1 l2 -> f l1 l2 = 0) l1 l2

let bind_opt opt f =
  match opt with
  | None -> None
  | Some x -> f x

let map_opt opt f =
  match opt with
  | None -> None
  | Some x -> Some (f x)

let rec find_map l f =
  match l with
  | [] -> None
  | x::tl ->
     match f x with
     | None -> find_map tl f
     | y -> y

let try_find_index f l =
  let rec aux i = function
    | [] -> None
    | hd::tl -> if f hd then Some i else aux (i+1) tl in
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

let add_unique f x l =
  if for_some (f x) l then
    l
  else
    x::l

let first_N n l =
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
let mk_ref a = ref a

let incr = Pervasives.incr
let decr = Pervasives.decr

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
let open_file_for_writing (fn:string) : file_handle = open_out fn
let append_to_file (fh:file_handle) s = fpr fh "%s\n" s; flush fh
let close_file (fh:file_handle) = close_out fh
let write_file (fn:string) s =
  let fh = open_file_for_writing fn in
  append_to_file fh s;
  close_file fh
let flush_file (fh:file_handle) = flush fh

let for_range lo hi f =
  for i = lo to hi do
    f i
  done

let incr r = r := !r + 1
let geq (i:int) (j:int) = i >= j

let get_exec_dir () = Filename.dirname (Sys.executable_name)
let expand_environment_variable x = try Sys.getenv x with Not_found -> ""

let physical_equality (x:'a) (y:'a) = x == y
let check_sharing a b msg = if physical_equality a b then fprint1 "Sharing OK: %s\n" msg else fprint1 "Sharing broken in %s\n" msg

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

