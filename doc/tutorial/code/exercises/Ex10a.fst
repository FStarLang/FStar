(*
   Copyright 2008-2018 Microsoft Research

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
module Ex10a
open FStar.All
open FStar.List.Tot
open FStar.Ref

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

(* 
// Uncomment these types and make them precise enough to pass the test
// BEGIN: Ex10aExercise
val grant : e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> True))
val revoke: e:entry -> ST unit (requires (fun h -> True))
                               (ensures (fun h x h' -> True))
// END: Ex10aExercise
*)

let grant e = acls := e::!acls

let revoke e =
  let db = filter (fun e' -> e<>e') !acls in
  acls := db

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

