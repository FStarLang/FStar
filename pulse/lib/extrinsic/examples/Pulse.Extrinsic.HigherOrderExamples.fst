(*
   Copyright 2026 Microsoft Research
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
module Pulse.Extrinsic.HigherOrderExamples

(** A lock protects an INVARIANT HANDLE, not a timeless physical cell.
    Acquiring it transfers that higher-order assertion with no caller-supplied
    credit. The critical section opens the recovered inner invariant to read
    the cell, then returns the handle when releasing the lock.
    The fully allocating program starts from emp and returns exactly 37.
    Only public source-logic/library rules occur in this proof. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module G = Pulse.Extrinsic.Ghost
module K = Pulse.Extrinsic.HeapLang.Spinlock
module M = Pulse.Extrinsic.MaskExamples

let client_at (#g:list ty) (cell flag:expr g TRef) =
  K.with_lock_at flag (load cell)
let client (cell flag:H.core_ref) = client_at (ref_ #[] cell) (ref_ flag)

let client_correct (i j:S.iref) (g:G.name) (cell flag:H.core_ref) (old:int)
  : Lemma (P.hoare (K.handle i g flag (S.inv j (C.points_to cell old)))
      (client cell flag) (P.returns_value old))
  = let resource = S.inv j (C.points_to cell old) in
    let shared = K.handle i g flag resource in
    M.read_with_updates cell old j;
    K.with_lock_correct i g flag resource (Load (Val cell)) (P.returns_value old);
    R.entails_refl shared;
    introduce forall v. S.implies (P.prepend_post shared (P.returns_value old) v)
      (P.returns_value old v)
    with (S.sep_laws (); R.entails_left (P.returns_value old v) shared);
    P.consequence shared shared (client cell flag)
      (P.prepend_post shared (P.returns_value old)) (P.returns_value old)

let from_owned (cell flag:H.core_ref) (old:int)
  : Lemma (P.hoare (S.star (C.points_to cell old) (C.points_to flag 1))
      (client cell flag) (P.returns_value old))
  = S.sep_laws ();
    P.allocate_invariant (C.points_to cell old) (C.points_to flag 1)
      (client cell flag) (P.returns_value old) (fun j ->
        K.allocate flag (S.inv j (C.points_to cell old))
          (client cell flag) (P.returns_value old)
          (fun i g -> client_correct i j g cell flag old))

let continuation : expr [TRef] TInt =
  let cell = Var Here in
  let! flag = alloc (int_ 1) in
  client_at (weaken cell) flag

let program : expr [] TInt =
  let! cell = alloc (int_ 37) in
  let! flag = alloc (int_ 1) in
  client_at (weaken cell) flag

let program_correct ()
  : Lemma (P.hoare S.emp program (P.returns_value 37))
  = S.sep_laws ();
    P.alloc 37;
    introduce forall cell. P.hoare (P.allocation_post 37 cell)
      (substitute cell continuation) (P.returns_value 37)
    with (
      let point = C.points_to cell 37 in
      let mid = P.framed_post (P.allocation_post 1) point in
      let body : expr [TRef] TInt = client_at (ref_ cell) (Var Here) in
      P.alloc 1;
      P.frame S.emp (Alloc (Val 1)) (P.allocation_post 1) point;
      introduce forall flag. P.hoare (mid flag) (substitute flag body) (P.returns_value 37)
      with (
        from_owned cell flag 37;
        assert_norm (substitute flag (client_at (ref_ cell) (Var Here)) == client cell flag)
      );
      P.let_rule point (Alloc (Val 1)) body mid (P.returns_value 37);
      assert_norm (substitute cell continuation == Let (Alloc (Val 1)) body)
    );
    P.let_rule S.emp (Alloc (Val 37)) continuation (P.allocation_post 37) (P.returns_value 37)
