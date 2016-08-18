module Ex10a

open FStar.List.Tot
open FStar.Heap

type file = string

(* using dynamic ACLs in some database *)
type entry =
  | Readable of string
  | Writable of string
type db = list entry

let canWrite db file =
  is_Some (tryFind (function Writable x -> x=file | _ -> false) db)


let canRead db file =
  is_Some (tryFind (function Readable x | Writable x -> x=file) db)


assume val acls: ref db


type canRead_t f h  = canRead  (sel h acls) f  == true


type canWrite_t f h = canWrite (sel h acls) f == true


val grant : e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> sel h' acls == e::sel h acls))
let grant e = ST.write acls (e::ST.read acls)

val revoke: e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> not(mem e (sel h' acls))))
let revoke e =
  let db = filter (fun e' -> e<>e') (ST.read acls) in
  ST.write acls db


(* two dangerous primitives *)
assume val read:   file:string -> ST string
                                     (requires (canRead_t file))
                                     (ensures (fun h s h' -> modifies_none h h'))


assume val delete: file:string -> ST unit
                                     (requires (canWrite_t file))
                                     (ensures (fun h s h' -> modifies_none h h'))


val safe_delete: file -> All unit 
			    (requires (fun h -> True))
			    (ensures (fun h x h' -> modifies_none h h'))


let safe_delete file =
  if canWrite !acls file
  then delete file
  else  
  failwith "unwritable"


val test_acls: file -> unit
let test_acls f =
  grant (Readable f);     (* ok *)
  let _ = read f in       (* ok --- it's in the acl *)
  //delete f;               (* not ok --- we're only allowed to read it *) 
  safe_delete f;          (* ok, but fails dynamically *)
  revoke (Readable f);
  //let _ = read f in       (* not ok any more *) 
  ()
