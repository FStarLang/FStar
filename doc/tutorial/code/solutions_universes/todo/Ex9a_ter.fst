module Ex9a_ter
open FStar.String
open FStar.List
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

open FStar.Heap
open FStar.ST
      
(* using dynamic ACLs in some database *)
type entry = 
  | Readable of string
  | Writable of string
type db = list entry 

  
assume val acls: ref db
type canRead_t f h  = canRead  (Heap.sel h acls) f == true
type canWrite_t f h = canWrite (Heap.sel h acls) f == true


val grant : e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> sel h' acls == e::sel h acls))
//                               (modifies (a_ref acls))
let grant e = ST.write acls (e::ST.read acls)

val revoke: e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> not(List.mem e (sel h' acls))))
                               (modifies (a_ref acls))
let revoke e = 
  let db = List.filter (fun e' -> e<>e') (ST.read acls) in
  ST.write acls db

(* two dangerous primitives *)
assume val read:   file:string -> ST string 
                                     (requires (canRead_t file))
                                     (ensures (fun h s h' -> h=h'))
                                     (modifies no_refs)

assume val delete: file:string -> ST unit
                                     (requires (canWrite_t file))
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

