module Ex10a
open FStar.All
//acls-variant

open FStar.List.Tot
open FStar.Heap

type file = string

(* Each entry is an element in our access-control list *)
type entry =
  | Readable of string
  | Writable of string
type db = list entry

(* We define two pure functions that test whether
   the suitable permission exists in some db *)
let canWrite db file =
  Some? (tryFind (function Writable x -> x=file | _ -> false) db)


let canRead db file =
  Some? (tryFind (function Readable x | Writable x -> x=file) db)

(* The acls reference stores the current access-control list, initially empty *)
val acls: ref db
let acls = ST.alloc []

(*
   Here are two stateful functions which alter the access control list.
   In reality, these functions may themselves be protected by some
   further authentication mechanism to ensure that an attacker cannot
   alter the access control list

   F* infers a fully precise predicate transformer semantics for them.
*)

let grant e = ST.write acls (e::ST.read acls)

let revoke e =
  let db = filter (fun e' -> e<>e') (ST.read acls) in
  ST.write acls db

(* Next, we model two primitives that provide access to files *)

(* We use two heap predicates, which will serve as stateful pre-conditions *)
type canRead_t f h  = canRead  (sel h acls) f  == true
type canWrite_t f h = canWrite (sel h acls) f == true

(* In order to call `read`, you need to prove
   the `canRead f` permission exists in the input heap *)
assume val read:   file:string -> ST string
                                     (requires (canRead_t file))
                                     (ensures (fun h s h' -> modifies_none h h'))

(* Likewise for `delete` *)
assume val delete: file:string -> ST unit
                                     (requires (canWrite_t file))
                                     (ensures (fun h s h' -> modifies_none h h'))

(* Then, we have a top-level API, which provides protected
   access to a file by first checking the access control list.

   If the check fails, it raises a fatal exception using `failwith`.
   As such, it is defined to have effect `All`, which combines
   both state and exceptions.

   Regardless, the specification proves that `safe_Delete`
   does not change the heap.
 *)
val safe_delete: file -> All unit 
			    (requires (fun h -> True))
			    (ensures (fun h x h' -> modifies_none h h'))


let safe_delete file =
  if canWrite !acls file
  then delete file
  else failwith "unwritable"

(* Finally, we have a top-level client program *)
val test_acls: file -> ML unit
let test_acls f =
  grant (Readable f);     (* ok *)
  let _ = read f in       (* ok --- it's in the acl *)
  //delete f;               (* not ok --- we're only allowed to read it *) 
  safe_delete f;          (* ok, but fails dynamically *)
  revoke (Readable f);
  //let _ = read f in       (* not ok any more *) 
  ()
