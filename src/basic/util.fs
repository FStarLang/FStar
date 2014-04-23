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
// (c) Microsoft Corporation. All rights reserved
module Microsoft.FStar.Util

open System.Diagnostics
open System.IO
open System.IO.Compression
open Profiling

exception Impos
exception NYI of string
exception Failure of string

type smap<'value>=HashMultiMap<string, 'value>
let smap_create<'value> (i:int) = new HashMultiMap<string,'value>(i, HashIdentity.Structural)
let smap_add (m:smap<'value>) k (v:'value) = m.Add(k,v)
let smap_try_find (m:smap<'value>) k = m.TryFind(k)
let smap_fold (m:smap<'value>) f a = m.Fold f a
let smap_remove (m:smap<'value>) k = m.Remove k

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

let string_of_int   i = string_of_int i
let string_of_float i = string_of_float i
let string_of_char  (i:char) = spr "%A" i
let string_of_bytes (i:byte[]) = string_of_unicode i

let char_at (s:string) (i:int) : char = s.[i]

let iof = int_of_float
let foi = float_of_int

let format (fmt:string) (args:list<string>) = 
    let frags = fmt.Split([|"%s"|], System.StringSplitOptions.None) in
    if frags.Length <> List.length args + 1
    then failwith "Not enough arguments to format string"
    else let args = Array.ofList (args@[""]) in 
         Array.fold2 (fun out frag arg -> out ^ frag ^ arg) "" frags args 

let format1 f a = format f [a]
let format2 f a b = format f [a;b]
let format3 f a b c = format f [a;b;c]
let format4 f a b c d = format f [a;b;c;d]
let format5 f a b c d e = format f [a;b;c;d;e]

        
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
  | None -> failwith "impossible"



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

let bind_opt opt f = match opt with
  | None -> None
  | Some x -> f x

let map_opt opt f = match opt with
  | None -> None
  | Some x -> Some (f x)

let rec find_map l f = match l with 
  | [] -> None 
  | x::tl -> match f x with 
      | None -> find_map tl f
      | y -> y

let for_all f l = List.forall f l
let for_some f l = List.exists f l
let forall_exists rel l1 l2 = l1 |> for_all (fun x -> l2 |> for_some (rel x))
let multiset_equiv rel l1 l2 = List.length l1 = List.length l2 && forall_exists rel l1 l2
   
let first_N n l =
  let rec f acc i l =
    if i = n then List.rev acc,l else
    match l with
      | h::tl -> f (h::acc) (i+1) tl
      | _     -> failwith "firstN"
  in
  f [] 0 l

let prefix l = match List.rev l with 
  | hd::tl -> List.rev tl, hd
  | _ -> failwith "impossible"
          
let (===) a b = LanguagePrimitives.PhysicalEquality a b
let physical_eq a b = a === b

let string_to_ascii_bytes: string -> byte [] = fun s -> asciiEncoding.GetBytes(s)
let ascii_bytes_to_string: byte [] -> string = fun b -> asciiEncoding.GetString(b)
let substring (s:string) i j = s.Substring(i,j)
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

let rec stmap (l:list<'a>) (f: 'a -> state<'s,'b>) : state<'s, list<'b>> = match l with 
    | [] -> ret []
    | hd::tl -> bind (f hd) 
                     (fun b -> 
                        let stl = stmap tl f in 
                        bind stl (fun tl -> ret (b::tl)))   

let stmapi (l:list<'a>) (f:int -> 'a -> state<'s,'b>) : state<'s, list<'b>> = 
  let rec aux i l = match l with
    | [] -> ret []
    | hd::tl -> 
      bind (f i hd) 
        (fun b -> 
          let stl = aux (i + 1) tl in 
          bind stl (fun tl -> ret (b::tl))) in 
  aux 0 l

let rec stiter (l:list<'a>) (f: 'a -> state<'s,unit>) : state<'s, unit> = match l with 
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
                                 
(* Query logging *)
let bump_query_count, 
    query_count =
  let qc = ref 0 in
  (fun () -> 
    incr qc;
    pr "\n#############QUERY %d##################\n" !qc; !qc), 
  (fun () -> !qc)

let write_file (fn:string) s = 
  let fh = new System.IO.StreamWriter(fn)  :> System.IO.TextWriter in
  fpr fh "%s" s;
  fh.Close()

let for_range lo hi f = 
  for i = lo to hi do
    f i
  done

let incr r = r := !r + 1
let geq (i:int) (j:int) = i >= j

let expand_environment_variable s = 
  System.Environment.ExpandEnvironmentVariables ("%"^s^"%")
