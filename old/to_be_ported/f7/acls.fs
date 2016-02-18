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
module Acls
open Pi
open Db

type facts = 
  | CanRead of string
  | CanWrite of string 
  | PublicFile of string 

#if fs
let read file = 
  expect(CanRead(file));
  printf "Reading file %s...\n" file; "data"
let delete file = 
  expect(CanWrite(file));
  printf "Deleting file %s...\n" file
#else
(*--- primBegin *)
let read file = expect(CanRead(file)); "data"
let delete file = expect(CanWrite(file))
(*--- primEnd *)
#endif

(* some sample files, one of them writable *)
(*--- filesBegin *)
let pwd = "C:/etc/password"
let readme = "C:/public/README"
let tmp = "C:/temp/tempfile"
let _ = Assume (CanWrite(tmp)) //<--NIK: assume is a keyword in Fine 
(*--- filesEnd *)

(* some dynamic validation function *)
(* "all files in the public directory are readable" *)
(*--- pfnBegin *)
let publicfile f = 
  if f = "C:/public/README" then Assume (PublicFile(f))
  else failwith "not a public file"
(*--- pfnEnd *)

(*--- testbasicBegin *)
let test:unit = 
  delete tmp; // $\mbox{ok}$
//  delete pwd; // $\mbox{type error}$
  let v1 = read tmp in // $\mbox{ok, using 1st logical rule}$ 
//  let v2 = read readme in // $\mbox{type error}$ 
  publicfile readme; let v3 = read readme in () // $\mbox{ok}$  
(*--- testbasicEnd *)
  
(* some higher-order code *)
(* let rc file = fun (x:unit) -> read file //<-- NIK: inlined type ascriptions on lambdas 
                                                      not handled well in Fine right now. 
                                                      Let's just infer it.  *)
let rc file = fun _unit -> read file //<-- underscores not handled well in Fine

(*--- testhoBegin *)
let test_higher_order:unit =
  let reader: unit -> string = 
    (publicfile readme; (fun () -> read readme)) in
//  let v4 = read readme in // $\mbox{type error}$ 
  let v5 = reader () in () // $\mbox{ok}$
(*--- testhoEnd *)
  
(* $\mbox{using dynamic ACLs in some database}$ *)
type entry = 
  | Readable of string
  | Writable of string
  | Nothing

(*--- dbBegin *)
let acls: (string,entry) Db_t = (* Db. *)create() (* NIK: Name resolution on long names is bit broken. 
                                                          Using short names for now *)
let safe_read file = 
  match (* Db. *)select acls file with
  | Readable file -> read file 
  | Writable file -> read file 
  | _ -> failwith "unreadable"
let readable file = 
  match (* Db. *)select acls file with
  | Readable f when file = f -> () //reversed the order of equality test here
  | Writable f when file = f -> () //to make unification happy
  | _ -> failwith "unreadable"
(*--- dbEnd *)

(*--- dbexBegin *)
let test_acls:unit =
  (* Db. *)insert acls tmp (Writable(tmp)); // $\mbox{ok}$ (* NIK: See short name/long name issue again *)
//  (* Db. *)insert acls tmp (Readable(pwd)); // $\mbox{type error}$
  (* Db. *)insert acls pwd (Nothing); // $\mbox{ok}$
  let v6 = safe_read pwd in // $\mbox{ok (but dynamically fails)}$
  let v7 = readable tmp; read tmp in () // $\mbox{ok}$
(*--- dbexEnd *)

(* merge *)
type t = string 

let rec fold_left f a xs = match xs with
  | (x::xs) -> fold_left f (f a x) xs
  | [] -> a

let append a file = (* a^ *) read file 
let merge sources = fold_left append "" sources
    
      
(* NIK: This was the original code. 
   Contains unnecessary extra type annotations.
   Fine parser doesn't like annotation on formal params ... for the moment *)

(* let append (a:string) (file:t) = (\* a^ *\) read file  *)
(* let merge sources =  *)
(*   let f: (string -> t -> string) -> string -> t list -> string = fold_left in *)
(*     f append "" sources *)
