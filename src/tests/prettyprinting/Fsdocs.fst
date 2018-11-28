(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi,
                       Microsoft Research, University of Maryland

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

(** Propositional sets (on any types): membership is a predicate *)
module Fh

let ne e1 e2 = CompProp e1 C_Ne e2
assume new
type eq : #a: Type -> #m: nat -> #n: nat -> matrix2 m n a -> matrix2 m n a -> Type 

(* TODO: move to FStar.Reflection.Basic? *)
(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from) the environment in the proofstate *)
assume
val push_binder: env -> binder -> env

let ne e1 e2 = CompProp e1 C_Ne e2
let gt e1 e2 = CompProp e1 C_Gt e2
let ge e1 e2 = CompProp (Plus (Lit 1) e1) C_Gt e2


(** Interpretation of type codes.

   Defines functions mapping from type codes (`typ`) to their interpretation as
   FStar types. For example, `type_of_typ (TBase TUInt8)` is `FStar.UInt8.t`.
*)


(** Interpretation of base types. *)
let type_of_base_typ (t: base_typ) : Tot Type0 = match t with | TUInt -> nat

(* TODO: The following is now wrong, should be replaced with readable *)
(** The modifies  as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from)clause *)
noeq
type loc_aux =
  | LocBuffer : #t: typ -> b: buffer t -> loc_aux
  | LocPointer : #t: typ -> p: pointer t -> loc_aux

(* TODO: move to FStar.Reflection.Basic? *)
(** [push_binder] extends the environment with a single binder.
    This is useful as one traverses the syntax of a term,
    pushing binders as one traverses a binder in a lambda,
    match, etc. Note, the environment here is disconnected to
    (though perhaps derived from) the environment in the proofstate *)

assume
val push_binder: env -> binder -> env

(* end else
    disjoint_root p1 p2
*)
(*** The modifies clause *)

noeq
type loc_aux =
  | LocBuffer : #t: typ -> b: buffer t -> loc_aux
  | LocPointer : #t: typ -> p: pointer t -> loc_aux

(* c
omment *)
(** fsdoc *)
let rec tm = 2
and tm = 3

(*
//  * AR: (may be this is an overkill)
 beforehand
//  *)
(** TODO: we need dependent functional extensionality *)
[@ "opaque_to_smt"]
unfold private
let equal_heap_dom (r: rid) (m0 m1: mem) : Type0 = Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r)

[@ "opaque_to_smt"]
unfold private
let equal_heap_dom (r: rid) (m0 m1: mem) : Type0 = Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r)

[@ "opaque_to_smt"]
unfold private
let equal_heap_dom (r: rid) (m0 m1: mem) : Type0 = Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r)

(*
//  * AR: (may be this is an overkill)
 beforehand
//  *)
(** TODO: we need dependent functional extensionality *)
[@ "opaque_to_smt"]
unfold private
let equal_heap_dom (r: rid) (m0 m1: mem) : Type0 = Heap.equal_dom (Map.sel m0.h r) (Map.sel m1.h r)

