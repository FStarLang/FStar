module DynACLs

open FStar.List
open FStar.Heap (* we open the Heap namespace to use stateful primitives *)

type file = string

(* Each entry is an element in our access-control list *)
type entry =
  | Readable of string
  | Writable of string
type db = list entry

(* The acls reference stores the current access-control list, initially empty *)
val acls : ref (list entry)
let acls = ref []

(* We define two pure functions that test whether
   the suitable permission exists in some db *)
let canRead db file =
  is_Some (find (function Readable x | Writable x -> x=file) db)

let canWrite db file =
  is_Some (find (function Writable x -> x=file | _ -> false) db)

(*
   Here are two stateful functions which alter the access control list.
   In reality, these functions may themselves be protected by some
   further authentication mechanism to ensure that an attacker cannot
   alter the access control list

   F* infers a fully precise predicate transformer semantics for them
*)
let grant e  = acls := e::!acls
let revoke e = acls := filter (fun e' -> e<>e') !acls

(* Next, we model two primitives that provide access to files *)

(* We use two heap predicates, which will serve as stateful pre-conditions *)
type CanRead (f:file) (h:heap)  = b2t (canRead  (sel h acls) f)
type CanWrite (f:file) (h:heap) = b2t (canWrite (sel h acls) f)

(* In order to call `read`, you need to prove
   the `CanRead f` permission exists in the input heap *)
assume val read:   f:file -> ST string
       (requires (CanRead f))
       (ensures (fun h s h' -> h=h'))

(* Likewise for `delete` *)
assume val delete: f:file -> ST unit
       (requires (CanWrite f))
       (ensures (fun h s h' -> h=h'))

(* Then, we have a top-level API, which provides protected
   access to a file by first checking the access control list.

   If the check fails, it raises a fatal exception using `failwith`.
   As such, it is defined to have effect `All`, which combines
   both state and exceptions.

   Regardless, the specification proves that `checkedDelete`
   does not change the heap.
 *)
val checkedDelete: file -> All unit
    (requires (fun h -> True))
    (ensures (fun h x h' -> h=h'))
let checkedDelete file =
  if canWrite !acls file
  then delete file
  else failwith "unwritable"

(* Finally, we have a top-level client program *)
val test_acls: file -> unit
let test_acls f =
  grant (Readable f);     (* ok *)
  let _ = read f in       (* ok --- it's in the acl *)
  (* delete f;               not ok --- we're only allowed to read it *)
  checkedDelete f;          (* ok, but fails dynamically *)
  revoke (Readable f);
  (* let _ = read f in *)   (* not ok any more *)
  ()
