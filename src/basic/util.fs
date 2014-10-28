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
module Microsoft.FStar.Util

open System
open System.Text
open System.Diagnostics
open System.IO
open System.IO.Compression
open Profiling

let return_all x = x

exception Impos
exception NYI of string
exception Failure of string

type proc = {m:Object; 
             outbuf:StringBuilder;
             proc:Process;
             killed:ref<bool>}
let all_procs : ref<list<proc>> = ref []

let start_process (prog:string) (args:string) (cond:string -> bool) : proc = 
    let signal = new Object() in
    let with_sig f = 
        System.Threading.Monitor.Enter(signal);
        let res = f() in
        System.Threading.Monitor.Exit(signal);
        res in
    let startInfo = new ProcessStartInfo() in
    let driverOutput = new StringBuilder() in
    let killed = ref false in
    let proc = new Process() in
        startInfo.FileName <- prog;
        startInfo.Arguments <- args;
        startInfo.UseShellExecute <- false;
        startInfo.RedirectStandardOutput <- true;
        startInfo.RedirectStandardInput <- true;
        proc.EnableRaisingEvents <- true;
        proc.OutputDataReceived.AddHandler(
             DataReceivedEventHandler(fun _ args -> 
                if !killed then ()
                else with_sig(fun () -> 
                           ignore <| driverOutput.Append(args.Data);
                           ignore <| driverOutput.Append("\n");
                           if null = args.Data
                           then (Printf.printf "Unexpected output from %s\n%s\n" prog (driverOutput.ToString()));
                           if null = args.Data || cond args.Data
                           then System.Threading.Monitor.Pulse(signal))));
        proc.Exited.AddHandler(
             EventHandler(fun _ _ ->
               System.Threading.Monitor.Enter(signal);
               killed := true;
               Printf.fprintf stdout "Z3 exited unadvertedly\n%s\n" (driverOutput.ToString());
               stdout.Flush();
               System.Threading.Monitor.Exit(signal);
               exit(1)));
        proc.StartInfo <- startInfo;
        proc.Start() |> ignore;
        proc.BeginOutputReadLine();
        let proc = {m=signal;
                    outbuf=driverOutput;
                    proc=proc;
                    killed=killed} in
        all_procs := proc::!all_procs;
        proc

let ask_process (p:proc) (stdin:string) : string = 
    ignore <| p.outbuf.Clear();
    System.Threading.Monitor.Enter(p.m);
    p.proc.StandardInput.WriteLine(stdin);
    ignore <| System.Threading.Monitor.Wait(p.m);
    System.Threading.Monitor.Exit(p.m);
    p.outbuf.ToString()

let kill_process (p:proc) = 
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

open Prims
//type set<'a> = Collections.Set<Boxed<'a>> * ('a -> Boxed<'a>)
//
//let new_set (cmp:'a -> 'a -> int) (hash:'a -> int) : set<'a> = 
//    let box v = new Boxed<'a>(v, cmp, hash) in
//    (new Collections.Set<Boxed<'a>>([]), box)
//
//let set_add a ((s, b):set<'a>) = s.Add (b a), b
//let set_remove a ((s1, b):set<'a>) = s1.Remove(b a), b
//let set_mem a ((s, b):set<'a>) = s.Contains (b a)
//let set_union ((s1, b):set<'a>) ((s2, _):set<'a>) = Set.union s1 s2, b
//let set_intersect ((s1, b):set<'a>) ((s2, _):set<'a>) = Set.intersect s1 s2, b
//let set_is_subset_of ((s1, _): set<'a>) ((s2, _):set<'a>) = s1.IsSubsetOf(s2)
//let set_count ((s1, _):set<'a>) = s1.Count
//let set_difference ((s1, b):set<'a>) ((s2, _):set<'a>) : set<'a> = Set.difference s1 s2, b
//let set_elements ((s1, b):set<'a>) :list<'a> = Set.toList s1 |> List.map (fun x -> x.unbox)

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


type smap<'value>=HashMultiMap<string, 'value>
let smap_create<'value> (i:int) = new HashMultiMap<string,'value>(i, HashIdentity.Structural)
let smap_clear<'value> (s:smap<'value>) = s.Clear()
let smap_add (m:smap<'value>) k (v:'value) = m.Add(k,v)
let smap_try_find (m:smap<'value>) k = m.TryFind(k)
let smap_fold (m:smap<'value>) f a = m.Fold f a
let smap_remove (m:smap<'value>) k = m.Remove k
let smap_keys (m:smap<'value>) = m.Fold (fun k v keys -> k::keys) []
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
let int_of_char (s:char) = int s

let uint16_of_int (i:int) = uint16 i

let float_of_byte (b:byte) = (float)b
let float_of_int32 (n:int32) = (float)n
let float_of_int64 (n:int64) = (float)n

let string_of_int   i = string_of_int i
let string_of_float i = string_of_float i
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
let splitlines (s:string) = Array.toList (s.Split([|Environment.NewLine|], StringSplitOptions.None))
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

let fprint1 a b = print_string <| format1 a b
let fprint2 a b c = print_string <| format2 a b c
let fprint3 a b c d = print_string <| format3 a b c d
let fprint4 a b c d e = print_string <| format4 a b c d e
let fprint5 a b c d e f = print_string <| format5 a b c d e f
        
let err_out : option<System.IO.StreamWriter> ref = ref None 
let open_err_out (s:string) = (err_out := Some (new System.IO.StreamWriter(s)))
let flush_err_out () = match !err_out with None -> () | Some e -> (e.Flush(); e.Close())

let try_find_position matcher f = 
  let rec aux pos = function
    | [] -> None
    | a::tl -> if (matcher a) then Some pos else aux (pos+1us) tl
  in aux 0us f
      
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

let nodups f l = 
  let rec aux = function 
    | hd::tl -> 
        let hds, tl' = List.partition (f hd) tl in 
          (match hds with 
             | [] -> aux tl' 
             | _ -> false)
    | _ -> true in
    aux l

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

let sort_with f l = List.sortWith f l 

let set_eq f l1 l2 = 
  let l1 = sort_with f l1 in
  let l2 = sort_with f l2 in
  List.forall2 (fun l1 l2 -> f l1 l2 = 0) l1 l2

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
   
let first_N n l =
  let rec f acc i l =
    if i = n then List.rev acc,l else
    match l with
      | h::tl -> f (h::acc) (i+1) tl
      | _     -> failwith "firstN"
  in
  f [] 0 l

let prefix l = 
    match List.rev l with 
      | hd::tl -> List.rev tl, hd
      | _ -> failwith "impossible"
          
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
let geq (i:int) (j:int) = i >= j

let expand_environment_variable s = 
  System.Environment.ExpandEnvironmentVariables ("%"^s^"%")

let physical_equality (x:'a) (y:'a) = LanguagePrimitives.PhysicalEquality (box x) (box y)
let check_sharing a b msg = if physical_equality a b then fprint1 "Sharing OK: %s\n" msg else fprint1 "Sharing broken in %s\n" msg
