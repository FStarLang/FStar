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
// Using light syntax in this file because of object-oriented F# constructs
// (c) Microsoft Corporation. All rights reserved
module FStar.Util

open System
open System.Text
open System.Diagnostics
open System.IO
open System.IO.Compression

let return_all x = x

exception Impos
exception NYI of string
exception Failure of string
let max_int: int = System.Int32.MaxValue

type proc = {m:Object;
             outbuf:StringBuilder;
             proc:Process;
             killed:ref<bool>;
             id:string}
let all_procs : ref<list<proc>> = ref []
open System.Threading
let global_lock = new Object()
let monitor_enter m = System.Threading.Monitor.Enter(m)
let monitor_exit m = System.Threading.Monitor.Exit(m)
let monitor_wait m = ignore <| System.Threading.Monitor.Wait(m)
let monitor_pulse m = System.Threading.Monitor.Pulse(m)
let current_tid () = System.Threading.Thread.CurrentThread.ManagedThreadId
let sleep n = System.Threading.Thread.Sleep(0+n)
let atomically (f:unit -> 'a) =
    System.Threading.Monitor.Enter(global_lock);
    let result = f () in
    System.Threading.Monitor.Exit(global_lock);
    result
let spawn (f:unit -> unit) = let t = new Thread(f) in t.Start()
let ctr = ref 0
let start_process (id:string) (prog:string) (args:string) (cond:string -> string -> bool) : proc =
    let signal = new Object() in
    let startInfo = new ProcessStartInfo() in
    let driverOutput = new StringBuilder() in
    let killed = ref false in
    let proc = new Process() in
    incr ctr;
    let proc_wrapper = {m=signal;
                        outbuf=new StringBuilder();
                        proc=proc;
                        killed=killed;
                        id=prog ^ ":" ^id^ "-" ^ (string_of_int !ctr)} in

    startInfo.FileName <- prog;
    startInfo.Arguments <- args;
    startInfo.UseShellExecute <- false;
    startInfo.RedirectStandardOutput <- true;
    startInfo.RedirectStandardInput <- true;
    proc.EnableRaisingEvents <- true;
    proc.OutputDataReceived.AddHandler(
            DataReceivedEventHandler(
                fun _ args ->
                    if !killed then ()
                    else
                        ignore <| driverOutput.Append(args.Data);
                        ignore <| driverOutput.Append("\n");
                        if null = args.Data
                            then (Printf.printf "Unexpected output from %s\n%s\n" prog (driverOutput.ToString()));
                        if null = args.Data || cond id args.Data
                        then
                            System.Threading.Monitor.Enter(signal);
                            ignore (proc_wrapper.outbuf.Clear());
                            ignore (proc_wrapper.outbuf.Append(driverOutput.ToString()));
                            ignore (driverOutput.Clear());
                            System.Threading.Monitor.Pulse(signal);
                            System.Threading.Monitor.Exit(signal)));
    proc.Exited.AddHandler(
            EventHandler(fun _ _ ->
            if !killed then ()
            else
                System.Threading.Monitor.Enter(signal);
                killed := true;
                Printf.fprintf stdout "%s exited inadvertently\n%s\n" prog (driverOutput.ToString());
                stdout.Flush();
                System.Threading.Monitor.Exit(signal);
                exit(1)));
    proc.StartInfo <- startInfo;
    proc.Start() |> ignore;
    proc.BeginOutputReadLine();
    all_procs := proc_wrapper::!all_procs;
//        Printf.printf "Started process %s\n" (proc.id);
    proc_wrapper
let tid () = System.Threading.Thread.CurrentThread.ManagedThreadId |> string_of_int

let ask_process (p:proc) (input:string) : string =
    System.Threading.Monitor.Enter(p.m);
    //Printf.printf "Thread %s is asking process %s\n" (tid()) p.id;
    //Printf.printf "Thread %s is writing to process %s ... responding?=%A\n" (tid()) p.id p.proc.Responding;
    //Printf.fprintf stderr "Thread %s is writing to process %s:\n%s\n" (tid()) p.id input;
//    if p.id = "z3.exe:bg"
//    then begin
//        Printf.printf "Thread BG break\n"
//    end;
    p.proc.StandardInput.WriteLine(input);
//    Printf.printf "Thread %s is waiting for process to reply\n" (tid());
//    flush(stdout);
    ignore <| System.Threading.Monitor.Wait(p.m);
//    Printf.printf "Thread %s is continuing with reply from process %s\n" (tid()) p.id;
    let x = p.outbuf.ToString() in
    System.Threading.Monitor.Exit(p.m);
    x

let kill_process (p:proc) =
//    Printf.printf "Killing process %s\n" (p.id);
    p.killed := true;
    System.Threading.Monitor.Enter(p.m);
    p.proc.StandardInput.Close();
    System.Threading.Monitor.Exit(p.m);
    p.proc.WaitForExit()

let kill_all () = !all_procs |> List.iter (fun p -> if not !p.killed then kill_process p)

let run_proc (name:string) (args:string) (stdin:string) : bool * string * string =
  let pinfo = new ProcessStartInfo(name, args) in
  pinfo.RedirectStandardOutput <- true;
  pinfo.RedirectStandardError <- true;
  pinfo.UseShellExecute <- false;
  pinfo.RedirectStandardInput <- true;
  let proc = new Process() in
  proc.StartInfo <- pinfo;
  let result = proc.Start() in
  proc.StandardInput.Write(stdin);
  let stdout = proc.StandardOutput.ReadToEnd() in
  let stderr = proc.StandardError.ReadToEnd() in
  result, stdout, stderr

let get_file_extension (fn: string) :string = Path.GetExtension fn
let is_path_absolute p = System.IO.Path.IsPathRooted(p)
let join_paths p0 p1 = System.IO.Path.Combine(p0, p1)
let normalize_file_path (path:string) = System.IO.Path.GetFullPath(path)

type stream_reader = System.IO.StreamReader (* not relying on representation *)
let open_stdin () = new System.IO.StreamReader(System.Console.OpenStandardInput())
let is_end_of_stream (s: stream_reader) = s.EndOfStream
let read_line (s:stream_reader) =
    if is_end_of_stream s
    then None
    else Some <| s.ReadLine()
type string_builder = System.Text.StringBuilder (* not relying on representation *)
let new_string_builder () = new System.Text.StringBuilder()
let clear_string_builder (s:string_builder) = s.Clear() |> ignore
let string_of_string_builder (s: string_builder) = s.ToString()
let string_builder_append (s: string_builder) (t:string) = s.Append t |> ignore

let message_of_exn (e:exn) = e.Message
let trace_of_exn (e:exn) = e.StackTrace
type set<'a> = (list<'a> * ('a -> 'a -> bool))

let set_is_empty ((s, _):set<'a>) =
    match s with
    | [] -> true
    | _ -> false

let new_set (cmp:'a -> 'a -> int) (hash:'a -> int) : set<'a> =
    ([], fun x y -> cmp x y = 0)

let set_elements ((s1, eq):set<'a>) :list<'a> =
   let rec aux out = function
        | [] -> out
        | hd::tl -> if List.exists (eq hd) out
                    then aux out tl
                    else aux (hd::out) tl in
   aux [] s1
let set_add a ((s, b):set<'a>) = (a::s, b)
let set_remove x ((s1, eq):set<'a>) = (List.filter (fun y -> not (eq x y)) s1, eq)
let set_mem a ((s, b):set<'a>) = List.exists (b a) s
let set_union ((s1, b):set<'a>) ((s2, _):set<'a>) = (s1@s2, b)//set_elements (s1,b)@set_elements (s2,b), b)
let set_intersect ((s1, eq):set<'a>) ((s2, _):set<'a>) = List.filter (fun y -> List.exists (eq y) s2) s1, eq
let set_is_subset_of ((s1, eq): set<'a>) ((s2, _):set<'a>) = List.for_all (fun y -> List.exists (eq y) s2) s1
let set_count ((s1, _):set<'a>) = s1.Length
let set_difference ((s1, eq):set<'a>) ((s2, _):set<'a>) : set<'a> = List.filter (fun y -> not (List.exists (eq y) s2)) s1, eq


type System.Collections.Generic.Dictionary<'K, 'V> with
  member x.TryFind(key) =
    match x.TryGetValue(key) with
    | true, v -> Some v
    | _ -> None
open System.Collections.Generic
type smap<'value>=System.Collections.Generic.Dictionary<string,'value>
let smap_create<'value> (i:int) = new Dictionary<string,'value>(i)
let smap_clear<'value> (s:smap<'value>) = s.Clear()
let smap_add (m:smap<'value>) k (v:'value) = ignore <| m.Remove(k); m.Add(k,v)
let smap_of_list<'value> (l:list<string*'value>) =
    let s = smap_create (List.length l) in
    List.iter (fun (x,y) -> smap_add s x y) l;
    s
let smap_try_find (m:smap<'value>) k = m.TryFind(k)
let smap_fold (m:smap<'value>) f a = 
    let out = ref a in 
    for entry in m do
        out := f entry.Key entry.Value !out;
    !out
let smap_remove (m:smap<'value>) k = m.Remove k |> ignore
let smap_keys (m:smap<'value>) = smap_fold m (fun k v keys -> k::keys) []
let smap_copy (m:smap<'value>) =
    let n = smap_create (m.Count) in
    smap_fold m (fun k v () -> smap_add n k v) ();
    n
let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let print_string s = pr "%s" s
let print_any s = pr "%A" s
let strcat s1 s2 = s1 ^ s2
let concat_l sep (l:list<string>) = String.concat sep l

let unicodeEncoding = new System.Text.UnicodeEncoding()
let asciiEncoding = new System.Text.ASCIIEncoding()
let string_of_unicode (bytes:byte []) = unicodeEncoding.GetString(bytes)
let unicode_of_string (string:string) = unicodeEncoding.GetBytes(string)

let char_of_int (i:int) = char i
let int_of_string (s:string) = int_of_string s
let int_of_char (s:char) = int32 s
let int_of_byte (s:byte) = int32 s
let int_of_uint8 (i:uint8) = int32 i
let uint16_of_int (i:int) = uint16 i
let byte_of_char (s:char) = byte s

let float_of_byte (b:byte) = (float)b
let float_of_int32 (n:int32) = (float)n
let float_of_int64 (n:int64) = (float)n

let int_of_int32 (i:int32) = i
let int32_of_int (i:int) = int32 i

let string_of_int   i = string_of_int i
let string_of_int64  (i:int64) = i.ToString()
let string_of_int32 i = string_of_int i
let string_of_float i = string_of_float i
let hex_string_of_byte  (i:byte) =
    let hs = spr "%x" i in
    if (String.length hs = 1) then "0"^hs
    else hs
let string_of_char  (i:char) = spr "%c" i
let string_of_bytes (i:byte[]) = string_of_unicode i
let starts_with (s1:string) (s2:string) = s1.StartsWith(s2)
let trim_string (s:string) = s.Trim()
let ends_with (s1:string) (s2:string) = s1.EndsWith(s2)
let char_at (s:string) (i:int) : char = s.[i]
let is_upper (c:char) = 'A' <= c && c <= 'Z'
let substring_from (s:string) i = s.Substring(i)
let substring (s:string) i j = s.Substring(i, j)
let replace_char (s:string) (c1:char) (c2:char) = s.Replace(c1,c2)
let replace_string (s:string) (s1:string) (s2:string) = s.Replace(s1, s2)
let hashcode (s:string) = s.GetHashCode()
let compare (s1:string) (s2:string) = s1.CompareTo(s2)
let splitlines (s:string) = Array.toList (s.Split([|Environment.NewLine;"\n"|], StringSplitOptions.None))
let split (s1:string) (s2:string) = Array.toList (s1.Split([|s2|], StringSplitOptions.None))

let iof = int_of_float
let foi = float_of_int

let format (fmt:string) (args:list<string>) =
    let frags = fmt.Split([|"%s"|], System.StringSplitOptions.None) in
    if frags.Length <> List.length args + 1
    then failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (string frags.Length) ^ " got [" ^ (String.concat ", " args) ^ "] frags are [" ^ (String.concat ", " (List.ofArray frags)) ^ "]")
    else let args = Array.ofList (args@[""]) in
         Array.fold2 (fun out frag arg -> out ^ frag ^ arg) "" frags args

let format1 f a = format f [a]
let format2 f a b = format f [a;b]
let format3 f a b c = format f [a;b;c]
let format4 f a b c d = format f [a;b;c;d]
let format5 f a b c d e = format f [a;b;c;d;e]
let format6 f a b c d e g = format f [a;b;c;d;e;g]


let fprint1 a b = print_string <| format1 a b
let fprint2 a b c = print_string <| format2 a b c
let fprint3 a b c d = print_string <| format3 a b c d
let fprint4 a b c d e = print_string <| format4 a b c d e
let fprint5 a b c d e f = print_string <| format5 a b c d e f
let fprint6 a b c d e f g = print_string <| format6 a b c d e f g

type either<'a,'b> =
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
        let hds, tl' = List.partition (f hd) tl in
          (match hds with
             | [] -> aux tl'
             | _ -> Some hd)
    | _ -> None in
    aux l

let nodups f l = find_dup f l |> Option.isNone

let remove_dups f l =
   let rec aux out = function
   | hd::tl -> let _, tl' = List.partition (f hd) tl in aux (hd::out) tl'
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

let try_find_index f l = List.tryFindIndex f l

let sort_with f l = List.sortWith f l

let set_eq f l1 l2 =
  let eq x y = f x y = 0 in
  let l1 = sort_with f l1 |> remove_dups eq in
  let l2 = sort_with f l2 |> remove_dups eq in
  if List.length l1 <> List.length l2
  then false
  else List.forall2 eq l1 l2

let bind_opt opt f =
    match opt with
    | None -> None
    | Some x -> f x

let map_opt opt f =
    match opt with
      | None -> None
      | Some x -> Some (f x)

let try_find_i f l =
    let rec aux i = function
        | [] -> None
        | hd::tl ->
            if f i hd
            then Some(i, hd)
            else aux (i+1) tl in
    aux 0 l

let rec find_map l f =
    match l with
      | [] -> None
      | x::tl ->
        match f x with
          | None -> find_map tl f
          | y -> y

let fold_map f state s =
    let fold (state, acc) x =
        let state, v = f state x in (state, v :: acc) in
    let (state, rs) = List.fold fold (state, []) s in
    (state, List.rev rs)

let choose_map f state s =
    let fold (state, acc) x =
        match f state x with
        | state, None   -> (state, acc)
        | state, Some v -> (state, v :: acc) in
    let (state, rs) = List.fold fold (state, []) s in
    (state, List.rev rs)

let for_all f l = List.forall f l
let for_some f l = List.exists f l
let forall_exists rel l1 l2 = l1 |> for_all (fun x -> l2 |> for_some (rel x))
let multiset_equiv rel l1 l2 = List.length l1 = List.length l2 && forall_exists rel l1 l2

let add_unique f x l =
  if l |> for_some (f x)
  then l
  else x::l

(**split the list at index n and return the 2 parts *)
let first_N n l (*: list 'a * list 'a*)=
  let rec f acc i l =
    if i = n then List.rev acc,l else
    match l with
      | h::tl -> f (h::acc) (i+1) tl
      | _     -> failwith "firstN"
  in
  f [] 0 l

let rec nth_tail n l =
   if n=0 then l else nth_tail (n - 1) (List.tl l)

let prefix l =
    match List.rev l with
      | hd::tl -> List.rev tl, hd
      | _ -> failwith "impossible"

let prefix_until f l =
    let rec aux prefix = function
        | [] -> None
        | hd::tl ->
            if f hd then Some (List.rev prefix, hd, tl)
            else aux (hd::prefix) tl in
    aux [] l


let string_to_ascii_bytes: string -> byte [] = fun s -> asciiEncoding.GetBytes(s)
let ascii_bytes_to_string: byte [] -> string = fun b -> asciiEncoding.GetString(b)
let mk_ref a = ref a

(* A simple state monad *)
type state<'s,'a> = ('s -> ('a*'s))
let get : state<'s,'s> = fun s -> s,s
let upd (f:'s -> 's) : state<'s, unit> = fun s -> (), f s
let put (s:'s) : state<'s, unit> = fun _ -> (), s
let ret (x:'a) : state<'s,'a> = fun s -> x, s
let bind (sa:state<'s,'a>) (f : 'a -> state<'s,'b>) : state<'s,'b> = fun s1 ->
  let a, s2 = sa s1 in (f a) s2
let (>>) s f = bind s f
let run_st init (s:state<'s,'a>) = s init

let rec stmap (l:list<'a>) (f: 'a -> state<'s,'b>) : state<'s, list<'b>> =
    match l with
    | [] -> ret []
    | hd::tl -> bind (f hd)
                     (fun b ->
                        let stl = stmap tl f in
                        bind stl (fun tl -> ret (b::tl)))

let stmapi (l:list<'a>) (f:int -> 'a -> state<'s,'b>) : state<'s, list<'b>> =
  let rec aux i l =
    match l with
    | [] -> ret []
    | hd::tl ->
      bind (f i hd)
        (fun b ->
          let stl = aux (i + 1) tl in
          bind stl (fun tl -> ret (b::tl))) in
  aux 0 l

let rec stiter (l:list<'a>) (f: 'a -> state<'s,unit>) : state<'s, unit> =
    match l with
    | [] -> ret ()
    | hd::tl -> bind (f hd) (fun () -> stiter tl f)

let rec stfoldr_pfx (l:list<'a>) (f: list<'a> -> 'a -> state<'s,unit>) : state<'s,unit> =
  match l with
    | [] -> ret ()
    | hd::tl -> (stfoldr_pfx tl f) >> (fun _ -> f tl hd)

let rec stfold (init:'b) (l:list<'a>) (f: 'b -> 'a -> state<'s,'b>) : state<'s,'b> =
  match l with
    | [] -> ret init
    | hd::tl -> (f init hd) >> (fun next -> stfold next tl f)


type file_handle = System.IO.TextWriter
let open_file_for_writing (fn:string) : file_handle =
  new System.IO.StreamWriter(fn)  :> System.IO.TextWriter
let append_to_file (fh:file_handle) s = fpr fh "%s\n" s; flush fh
let close_file (fh:file_handle) = fh.Close()
let write_file (fn:string) s =
  let fh = open_file_for_writing fn in
  append_to_file fh s;
  close_file fh
let flush_file (fh:file_handle) = fh.Flush()

let for_range lo hi f =
  for i = lo to hi do
    f i
  done

let incr r = r := !r + 1
let decr r = r := !r - 1
let geq (i:int) (j:int) = i >= j

let get_exec_dir () =
    let asm = System.Reflection.Assembly.GetEntryAssembly() in
    Path.GetDirectoryName(asm.Location)

let expand_environment_variable s =
  System.Environment.ExpandEnvironmentVariables ("%"^s^"%")

let physical_equality (x:'a) (y:'a) = LanguagePrimitives.PhysicalEquality (box x) (box y)
let check_sharing a b msg = if physical_equality a b then fprint1 "Sharing OK: %s\n" msg else fprint1 "Sharing broken in %s\n" msg

let is_letter_or_digit = Char.IsLetterOrDigit
let is_punctuation = Char.IsPunctuation
let is_symbol = Char.IsSymbol

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

let get_owriter (file:string) : oWriter =
    let w = new BinaryWriter(File.Open(file, FileMode.Create)) in
    {
        write_byte = w.Write;
        write_bool = w.Write;
        write_int = w.Write;
        write_int32 = w.Write;
        write_int64 = w.Write;
        write_char = w.Write;
        write_double = w.Write;
        write_bytearray = fun a -> w.Write(a.Length); w.Write(a);
        write_string = w.Write;

        close = w.Close;
    }

let get_oreader (file:string) : oReader =
    let r = new BinaryReader(File.Open(file, FileMode.Open)) in
    {
        read_byte = r.ReadByte;
        read_bool = r.ReadBoolean;
        read_int = r.ReadInt32;
        read_int32 = r.ReadInt32;
        read_int64 = r.ReadInt64;
        read_char = r.ReadChar;
        read_double = r.ReadDouble;
        read_bytearray = fun _ -> let n = r.ReadInt32() in r.ReadBytes(n)
        read_string = r.ReadString;

        close = r.Close
    }

