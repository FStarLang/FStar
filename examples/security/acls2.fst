module ACLs
open String
open List
type file = string

let canWrite = function
  | "C:/temp/tempfile" -> true
  | _ -> false

let publicFile = function 
  | "C:/public/README" -> true
  | _ -> false
  
let canRead (f:file) = 
  canWrite f           (* 1. writeable files are also readable *)
  || publicFile f      (* 2. public files are readable *)
  || f="C:/acls2.fst"  (* and so is this file *)

(* two dangerous primitives *)
assume val read:   file:string{canRead file} -> string
assume val delete: file:string{canWrite file} -> unit

(* some sample files, one of them writable *)
let pwd    = "C:/etc/password"
let readme = "C:/public/README"
let tmp    = "C:/temp/tempfile"

let test () = 
  delete tmp; (* ok *)
//delete pwd; (* type error *)
  let v1 = read tmp in    (* ok, rule 1. *)
  let v2 = read readme in (* ok, rule 2. *)
  () 

(* some higher-order code *)
val rc: file -> ML (unit -> string)
let rc file = 
  if canRead file 
  then (fun () -> read file)
  else failwith "Can't read"

module DynACLs
open Heap
open ST
type file = string
      
(* using dynamic ACLs in some database *)
type entry = 
  | Readable of string
  | Writable of string
type db = list entry 

let canWrite db file = 
  is_Some (List.find (function Writable x -> x=file | _ -> false) db)

let canRead db file = 
  is_Some (List.find (function Readable x | Writable x -> x=file) db)
  
assume val acls: ref db
type CanRead f h  = canRead  (Heap.sel h acls) f == true
type CanWrite f h = canWrite (Heap.sel h acls) f == true

let grant e = 
  let a = ST.read acls in 
  ST.write acls (e::a)

let revoke e = 
  let a = ST.read acls in
  let db = List.filter (fun e' -> e<>e') a in
  ST.write acls db

(* two dangerous primitives *)
assume val read:   file:string -> ST string 
                                     (requires (CanRead file))
                                     (ensures (fun h s h' -> h=h'))
                                     (modifies no_refs)

assume val delete: file:string -> ST unit
                                     (requires (CanWrite file))
                                     (ensures (fun h s h' -> h=h'))
                                     (modifies no_refs)

val safe_delete: file -> All unit (fun h -> True) (fun h x h' -> h==h')
let safe_delete file = 
  if canWrite !acls file 
  then delete file
  else failwith "unwritable"

val test_acls: file -> unit
let test_acls f = 
  grant (Readable f);     (* ok *)
  let _ = read f in       (* ok --- it's in the acl *)
  (* delete f;               (\* not ok --- we're only allowed to read it *\) *)
  safe_delete f;          (* ok, but fails dynamically *)
  revoke (Readable f);
  (* let _ = read f in       (\* not ok any more *\) *)
  ()

