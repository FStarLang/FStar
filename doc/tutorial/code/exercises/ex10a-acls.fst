(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst
--*)
module DynACLs
open FStar.List
open FStar.Heap

type file = string

(* using dynamic ACLs in some database *)
type entry =
  | Readable of string
  | Writable of string
type db = list entry

let canWrite db file =
  is_Some (find (function Writable x -> x=file | _ -> false) db)

let canRead db file =
  is_Some (find (function Readable x | Writable x -> x=file) db)

assume val acls: ref db
type CanRead f h  = canRead  (sel h acls) f == true
type CanWrite f h = canWrite (sel h acls) f == true


val grant : e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> True))
let grant e = ST.write acls (e::ST.read acls)

val revoke: e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> True))
let revoke e =
  let db = filterT (fun e' -> e<>e') (ST.read acls) in
  ST.write acls db

(* two dangerous primitives *)
assume val read:   file:string -> ST string
                                     (requires (CanRead file))
                                     (ensures (fun h s h' -> h=h'))

assume val delete: file:string -> ST unit
                                     (requires (CanWrite file))
                                     (ensures (fun h s h' -> h=h'))

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
