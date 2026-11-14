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
module Pulse.Extrinsic.ParallelIncrement

(** Owicki-Gries parallel increment with fractional ghost contributions.
    The physical invariant owns counter |-> x+y and half of each contribution
    x,y in {0,1}; each thread owns the other half of its own contribution.
    A successful CAS changes the physical sum and that ghost contribution
    together. A failed CAS leaves both unchanged and retries.

    run forks one increment, performs the other, obtains the child's completed
    half-share through Join, and reads exactly 2. from_owned allocates ghost
    resources and installs both invariants; program also allocates the physical
    counter and flag, giving the final triple from emp.
    All program reasoning uses logical rules, not traces or native actions.
    The fractions are ghost shares, never fractional physical write access. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
open FStar.Real
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module F = Pulse.Extrinsic.Ghost.Fractional
module G = Pulse.Extrinsic.Ghost
module B = Pulse.Extrinsic.ExamplePredicates
module GS = Pulse.Lib.GhostSet
module L = Pulse.Extrinsic.HeapLang.Loops
module J = Pulse.Extrinsic.HeapLang.Join
module I = Pulse.Extrinsic.HeapLang.AtomicIncrement

let half (g:G.name) (n:int) = F.own #int g 0.5R n
let piece (r:H.core_ref) (g h:G.name) (x y:B.bit) =
  S.star (C.points_to r (x + y)) (S.star (half g x) (half h y))
let row (r:H.core_ref) (g h:G.name) (x:B.bit) =
  S.op_exists_Star (piece r g h x)
let body (r:H.core_ref) (g h:G.name) = S.op_exists_Star (row r g h)
let contribution (g:G.name) (success:bool) = half g (if success then 1 else 0)

let piece_intro (r:H.core_ref) (g h:G.name) (x y:B.bit)
  : Lemma (S.implies (piece r g h x y) (body r g h))
  = R.exists_intro (piece r g h x) y;
    R.exists_intro (row r g h) x;
    R.entails_trans (piece r g h x y) (row r g h x) (body r g h)

let body_exposed (r:H.core_ref) (g h:G.name)
  : Lemma (S.implies (P.exposed (body r g h)) (body r g h))
  = introduce forall (x:B.bit). S.implies (P.exposed (row r g h x)) (row r g h x)
    with (
      introduce forall (y:B.bit). S.implies (P.exposed (piece r g h x y)) (piece r g h x y)
      with (
        C.points_to_exposed r (x + y);
        F.exposed #int g 0.5R x;
        F.exposed #int h 0.5R y;
        R.exposed_star (half g x) (half h y);
        R.exposed_star (C.points_to r (x + y)) (S.star (half g x) (half h y))
      );
      R.exposed_exists (piece r g h x)
    );
    R.exposed_exists (row r g h)

let mine_agrees (r:H.core_ref) (g h:G.name) (x y:B.bit) (mine:int)
  : Lemma (S.implies (S.star (piece r g h x y) (half g mine))
      (S.star (S.star (piece r g h x y) (half g mine)) (S.pure (x == mine))))
  = S.sep_laws ();
    let pair = S.star (half g x) (half g mine) in
    let rest = S.star (C.points_to r (x + y)) (half h y) in
    F.agree #int g 0.5R 0.5R x mine;
    assert_norm ((x == mine /\ 0.5R +. 0.5R <=. 1.0R) == (x == mine));
    R.entails_emp rest;
    R.entails_star pair (S.pure (x == mine)) rest S.emp;
    R.with_pure (S.star (piece r g h x y) (half g mine)) (x == mine)

(** Agreement with the private zero half fixes x=0. Combine the two halves
    before changing the ghost contribution; split afterward and restore the
    existential invariant. On CAS failure neither physical nor ghost state
    changes. Explicit #int prevents accidentally using the PCM for bit. *)
let cas_piece (mask:S.inames) (r:H.core_ref) (g h:G.name)
  (x y:B.bit) (expected:int)
  : Lemma (P.atomic mask (S.star (piece r g h x y) (half g 0))
      (Cas (Val r) (Val expected) (Val (expected + 1)))
      (P.prepend_post (P.exposed (body r g h)) (contribution g)))
  = S.sep_laws ();
    let pre = S.star (piece r g h x y) (half g 0) in
    let e = Cas (Val r) (Val expected) (Val (expected + 1)) in
    let post = P.prepend_post (P.exposed (body r g h)) (contribution g) in
    mine_agrees r g h x y 0;
    P.atomic_pure_pre mask pre (x == 0) e post (fun _ ->
      F.split #int g 0.5R 0.5R 0;
      let ghost = S.star (F.own #int g 1.0R 0) (half h y) in
      let raw = P.framed_post (P.cas_post r y expected (expected + 1)) ghost in
      P.atomic_cas mask r y expected (expected + 1);
      P.atomic_frame mask (C.points_to r y) e (P.cas_post r y expected (expected + 1)) ghost;
      R.entails_refl pre;
      introduce forall b. S.implies (raw b) (raw b) with R.entails_refl (raw b);
      P.atomic_consequence mask (S.star (C.points_to r y) ghost) pre e raw raw;
      P.update_entails mask pre pre;
      introduce forall b. P.update mask mask (raw b) (post b)
      with (
        let n : B.bit = if b then 1 else 0 in
        let point = C.points_to r (if b then expected + 1 else y) in
        let plain = S.star point ghost in
        let updated = S.star (C.points_to r (n + y))
          (S.star (F.own #int g 1.0R n) (half h y)) in
        P.update_pure_pre mask mask plain (post b) (b == (y = expected)) (fun _ ->
          if b then (
            F.write #int mask g 0 1;
            P.update_frame mask mask (F.own #int g 1.0R 0) (F.own #int g 1.0R 1)
              (S.star point (half h y))
          ) else (
            R.entails_refl plain;
            P.update_entails mask plain plain
          );
          F.split #int g 0.5R 0.5R n;
          piece_intro r g h n y;
          R.entails_refl (half g n);
          R.entails_star (piece r g h n y) (body r g h) (half g n) (half g n);
          R.entails_exposed (body r g h);
          R.entails_star (body r g h) (P.exposed (body r g h)) (half g n) (half g n);
          R.entails_trans updated (S.star (body r g h) (half g n)) (post b);
          P.update_entails mask updated (post b);
          P.update_trans mask mask mask plain updated (post b)
        )
      );
      P.atomic_updates mask mask pre pre e raw post
    );
    introduce forall b. S.implies (post b) (post b) with R.entails_refl (post b);
    P.atomic_consequence mask (S.star pre (S.pure (x == 0))) pre e post post

let cas_increment (i:S.iref) (r:H.core_ref) (g h:G.name) (expected:int)
  : Lemma (P.atomic GS.empty (S.star (S.inv i (body r g h)) (half g 0))
      (Cas (Val r) (Val expected) (Val (expected + 1)))
      (P.prepend_post (S.inv i (body r g h)) (contribution g)))
  = S.sep_laws ();
    let opened = S.add_inv GS.empty i in
    let e = Cas (Val r) (Val expected) (Val (expected + 1)) in
    let post = P.prepend_post (P.exposed (body r g h)) (contribution g) in
    introduce forall (x:B.bit). P.atomic opened (S.star (row r g h x) (half g 0)) e post
    with (
      introduce forall (y:B.bit). P.atomic opened (S.star (piece r g h x y) (half g 0)) e post
      with cas_piece opened r g h x y expected;
      P.atomic_exists opened (fun (y:B.bit) -> S.star (piece r g h x y) (half g 0)) e post;
      R.exists_star (piece r g h x) (half g 0)
    );
    P.atomic_exists opened (fun (x:B.bit) -> S.star (row r g h x) (half g 0)) e post;
    R.exists_star (row r g h) (half g 0);
    body_exposed r g h;
    R.entails_refl (half g 0);
    R.entails_star (P.exposed (body r g h)) (body r g h) (half g 0) (half g 0);
    introduce forall b. S.implies (post b) (post b) with R.entails_refl (post b);
    P.atomic_consequence opened (S.star (body r g h) (half g 0))
      (S.star (P.exposed (body r g h)) (half g 0)) e post post;
    P.atomic_invariant GS.empty i (body r g h) (half g 0) e (contribution g)

let read_shared (i:S.iref) (r:H.core_ref) (g h:G.name)
  : Lemma (P.hoare (S.inv i (body r g h)) (Load (Val r))
      (P.constant_post (S.inv i (body r g h))))
  = S.sep_laws ();
    let opened = S.add_inv GS.empty i in
    let e = Load (Val r) in
    let contents = body r g h in
    let handle = S.inv i contents in
    let post = P.prepend_post (P.exposed contents) (P.constant_post #TInt S.emp) in
    introduce forall (x:B.bit). P.atomic opened (row r g h x) e post
    with (
      introduce forall (y:B.bit). P.atomic opened (piece r g h x y) e post
      with (
        let point = C.points_to r (x + y) in
        let ghost = S.star (half g x) (half h y) in
        let raw = P.framed_post (P.read_post r (x + y)) ghost in
        P.atomic_load opened r (x + y);
        P.atomic_frame opened point e (P.read_post r (x + y)) ghost;
        R.entails_refl (piece r g h x y);
        introduce forall v. S.implies (raw v) (post v)
        with (
          R.entails_left point (S.pure (v == x + y));
          R.entails_refl ghost;
          R.entails_star (P.read_post r (x + y) v) point ghost ghost;
          piece_intro r g h x y;
          R.entails_trans (raw v) (piece r g h x y) contents;
          R.entails_exposed contents;
          R.entails_trans (raw v) contents (post v)
        );
        P.atomic_consequence opened (piece r g h x y) (piece r g h x y) e raw post
      );
      P.atomic_exists opened (piece r g h x) e post
    );
    P.atomic_exists opened (row r g h) e post;
    body_exposed r g h;
    introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
    P.atomic_consequence opened contents (P.exposed contents) e post post;
    P.atomic_invariant GS.empty i contents S.emp e (P.constant_post #TInt S.emp);
    R.entails_refl handle;
    introduce forall v. S.implies
      (P.prepend_post handle (P.constant_post #TInt S.emp) v) (P.constant_post handle v)
    with R.entails_refl handle;
    P.atomic_consequence GS.empty handle handle e
      (P.prepend_post handle (P.constant_post S.emp)) (P.constant_post handle);
    P.atomic_to_hoare handle e (P.constant_post handle)

let held (i:S.iref) (r:H.core_ref) (g h:G.name) (n:int) =
  S.star (S.inv i (body r g h)) (half g n)

let retry_at (#ctx:list ty) (r:expr ctx TRef) : expr (TInt :: ctx) TBool =
  I.retry_at r

let increment_at (#ctx:list ty) (r:expr ctx TRef) : expr ctx TUnit =
  I.increment_at r

let retry_body (r:H.core_ref) = retry_at (Val #[] r)
let increment (r:H.core_ref) = increment_at (Val #[] r)

let retry_correct (i:S.iref) (r:H.core_ref) (g h:G.name) (expected:int)
  : Lemma (P.hoare (held i r g h 0) (substitute expected (retry_body r))
      (L.condition_post (held i r g h 0) (held i r g h 1)))
  = S.sep_laws ();
    let pre = held i r g h 0 in
    let exit = held i r g h 1 in
    let result = P.prepend_post (S.inv i (body r g h)) (contribution g) in
    let desired = Add (Val expected) (Val 1) in
    let mid = P.framed_post (P.returns_value (expected + 1)) pre in
    P.add expected 1;
    P.frame S.emp desired (P.returns_value (expected + 1)) pre;
    let k = CasDesired r expected Hole in
    introduce forall v. P.hoare (mid v) (fill k (Val v)) result
    with (
      P.pure_pre pre (v == expected + 1) (fill k (Val v)) result (fun _ ->
        cas_increment i r g h expected;
        P.atomic_to_hoare pre (fill k (Val v)) result)
    );
    P.context_rule k pre desired mid result;
    let cas_expr = fill k desired in
    let post = L.condition_post pre exit in
    introduce forall b. P.hoare (result b) (If (Val b) (Val false) (Val true)) post
    with (
      R.entails_refl (result b);
      P.value_rule (result b) (not b) post;
      P.if_value (result b) b (Val false) (Val true) post
    );
    P.context_rule (IfCtx Hole (Val false) (Val true)) pre cas_expr result post;
    assert_norm (substitute expected (retry_body r) == If cas_expr (Val false) (Val true))

let increment_correct (i:S.iref) (r:H.core_ref) (g h:G.name)
  : Lemma (P.hoare (held i r g h 0) (increment r) (P.constant_post (held i r g h 1)))
  = S.sep_laws ();
    let handle = S.inv i (body r g h) in
    let pre = held i r g h 0 in
    let exit = held i r g h 1 in
    let load = Load (Val r) in
    read_shared i r g h;
    P.frame handle load (P.constant_post handle) (half g 0);
    R.entails_refl pre;
    introduce forall v. S.implies (P.framed_post (P.constant_post #TInt handle) (half g 0) v)
      (P.constant_post pre v)
    with R.entails_refl pre;
    P.consequence pre pre load (P.framed_post (P.constant_post handle) (half g 0))
      (P.constant_post pre);
    introduce forall expected. P.hoare pre (substitute expected (retry_body r))
      (L.condition_post pre exit)
    with retry_correct i r g h expected;
    P.let_rule pre load (retry_body r) (P.constant_post pre) (L.condition_post pre exit);
    P.value_rule pre () (P.constant_post pre);
    L.while_rule pre pre exit (Let load (retry_body r)) (Val ())

let body_symmetric (r:H.core_ref) (g h:G.name)
  : Lemma (body r g h == body r h g)
  = S.sep_laws ();
    introduce forall (y:B.bit). row r g h y ==
      S.op_exists_Star (fun (x:B.bit) -> piece r h g x y)
    with (
      introduce forall (x:B.bit). piece r g h y x == piece r h g x y with ();
      S.exists_ext (piece r g h y) (fun (x:B.bit) -> piece r h g x y)
    );
    S.exists_ext (row r g h) (fun (y:B.bit) -> S.op_exists_Star (fun (x:B.bit) -> piece r h g x y));
    R.exists_swap (piece r h g);
    assert_norm (body r h g == S.op_exists_Star (fun (x:B.bit) -> S.op_exists_Star (piece r h g x)))

let read_two (i:S.iref) (r:H.core_ref) (g h:G.name)
  : Lemma (P.hoare (S.star (S.inv i (body r g h)) (S.star (half g 1) (half h 1)))
      (Load (Val r)) (P.returns_value 2))
  = S.sep_laws ();
    let mask = S.add_inv GS.empty i in
    let receipts = S.star (half g 1) (half h 1) in
    let contents = body r g h in
    let e = Load (Val r) in
    let post = P.prepend_post (P.exposed contents) (P.returns_value 2) in
    introduce forall (x:B.bit). P.atomic mask (S.star (row r g h x) receipts) e post
    with (
      introduce forall (y:B.bit). P.atomic mask (S.star (piece r g h x y) receipts) e post
      with (
        let pre = S.star (piece r g h x y) receipts in
        mine_agrees r g h x y 1;
        R.entails_refl (half h 1);
        R.entails_star (S.star (piece r g h x y) (half g 1))
          (S.star (S.star (piece r g h x y) (half g 1)) (S.pure (x == 1)))
          (half h 1) (half h 1);
        P.atomic_pure_pre mask pre (x == 1) e post (fun _ ->
          mine_agrees r h g y x 1;
          R.entails_refl (half g 1);
          R.entails_star (S.star (piece r h g y x) (half h 1))
            (S.star (S.star (piece r h g y x) (half h 1)) (S.pure (y == 1)))
            (half g 1) (half g 1);
          P.atomic_pure_pre mask pre (y == 1) e post (fun _ ->
            let ghost = S.star (S.star (half g 1) (half h 1)) receipts in
            let raw = P.framed_post (P.read_post r 2) ghost in
            P.atomic_load mask r 2;
            P.atomic_frame mask (C.points_to r 2) e (P.read_post r 2) ghost;
            R.entails_refl pre;
            introduce forall v. S.implies (raw v) (post v)
            with (
              let fact = P.returns_value 2 v in
              R.entails_left (S.star (piece r g h 1 1) fact) receipts;
              piece_intro r g h 1 1;
              R.entails_refl fact;
              R.entails_star (piece r g h 1 1) contents fact fact;
              R.entails_trans (raw v) (S.star (piece r g h 1 1) fact) (S.star contents fact);
              R.entails_exposed contents;
              R.entails_star contents (P.exposed contents) fact fact;
              R.entails_trans (raw v) (S.star contents fact) (post v)
            );
            P.atomic_consequence mask pre pre e raw post
          );
          introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
          P.atomic_consequence mask (S.star pre (S.pure (y == 1))) pre e post post
        );
        introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
        P.atomic_consequence mask (S.star pre (S.pure (x == 1))) pre e post post
      );
      P.atomic_exists mask (fun (y:B.bit) -> S.star (piece r g h x y) receipts) e post;
      R.exists_star (piece r g h x) receipts
    );
    P.atomic_exists mask (fun (x:B.bit) -> S.star (row r g h x) receipts) e post;
    R.exists_star (row r g h) receipts;
    body_exposed r g h;
    R.entails_refl receipts;
    R.entails_star (P.exposed contents) contents receipts receipts;
    introduce forall v. S.implies (post v) (post v) with R.entails_refl (post v);
    P.atomic_consequence mask (S.star contents receipts) (S.star (P.exposed contents) receipts) e post post;
    P.atomic_invariant GS.empty i contents receipts e (P.returns_value 2);
    P.atomic_to_hoare (S.star (S.inv i contents) receipts) e
      (P.prepend_post (S.inv i contents) (P.returns_value 2));
    R.entails_refl (S.star (S.inv i contents) receipts);
    introduce forall v. S.implies (P.prepend_post (S.inv i contents) (P.returns_value 2) v)
      (P.returns_value 2 v)
    with R.entails_left (P.returns_value 2 v) (S.inv i contents);
    P.consequence (S.star (S.inv i contents) receipts) (S.star (S.inv i contents) receipts) e
      (P.prepend_post (S.inv i contents) (P.returns_value 2)) (P.returns_value 2)

let run_at (#ctx:list ty) (r flag:expr ctx TRef) : expr ctx TInt =
  fork (increment_at r >> J.signal_at flag) >>
  (increment_at r >> (J.wait_at flag >> load r))

let run (r flag:H.core_ref) = run_at (Val #[] r) (Val flag)

let run_pre (i j:S.iref) (r flag:H.core_ref) (g h:G.name) =
  S.star (S.inv i (body r g h))
    (S.star (J.handle j flag (half h 1)) (S.star (half g 0) (half h 0)))

(** Separate the child and parent halves before fork. The child publishes its
    completed half; the parent keeps its own across wait and recovers the other.
    read_two can then force both hidden contributions to one. Sharing invariant
    handles never duplicates the private receipts. *)
let run_correct (i j:S.iref) (r flag:H.core_ref) (g h:G.name)
  : Lemma (P.hoare (run_pre i j r flag g h) (run r flag) (P.returns_value 2))
  = S.sep_laws ();
    let shared = S.inv i (body r g h) in
    let joined = J.handle j flag (half h 1) in
    let parent = S.star (held i r g h 0) joined in
    let child = S.star (held i r h g 0) joined in
    let child_code = Seq (increment r) (J.signal flag) in
    let child_done = S.star shared joined in
    let parent_done = S.star (held i r g h 1) joined in
    let both_done = S.star (S.star shared (S.star (half g 1) (half h 1))) joined in
    body_symmetric r g h;
    increment_correct i r h g;
    P.frame_constant (held i r h g 0) (increment r) (held i r h g 1) joined;
    J.signal_correct j flag (half h 1);
    P.frame_constant (S.star joined (half h 1)) (J.signal flag) joined shared;
    P.sequence child (S.star (held i r h g 1) joined) (increment r) (J.signal flag)
      (P.constant_post child_done);
    R.entails_refl child;
    introduce forall (_:unit). S.implies child_done S.emp with R.entails_emp child_done;
    P.consequence child child child_code (P.constant_post child_done) (P.constant_post S.emp);

    increment_correct i r g h;
    P.frame_constant (held i r g h 0) (increment r) (held i r g h 1) joined;
    J.wait_correct j flag (half h 1);
    P.frame_constant joined (J.wait flag) (S.star joined (half h 1)) (held i r g h 1);
    read_two i r g h;
    P.frame (S.star shared (S.star (half g 1) (half h 1))) (Load (Val r)) (P.returns_value 2) joined;
    R.entails_refl both_done;
    introduce forall v. S.implies (P.framed_post (P.returns_value 2) joined v) (P.returns_value 2 v)
    with R.entails_left (P.returns_value 2 v) joined;
    P.consequence both_done both_done (Load (Val r))
      (P.framed_post (P.returns_value 2) joined) (P.returns_value 2);
    P.sequence parent_done both_done (J.wait flag) (Load (Val r)) (P.returns_value 2);
    P.sequence parent parent_done (increment r) (Seq (J.wait flag) (Load (Val r))) (P.returns_value 2);

    S.dup_inv_equiv i (body r g h);
    Pulse.Extrinsic.HeapLang.Invariants.duplicate j (J.body flag (half h 1));
    R.entails_refl parent;
    P.fork parent child child_code (P.constant_post parent);
    P.sequence (run_pre i j r flag g h) parent (Fork child_code)
      (Seq (increment r) (Seq (J.wait flag) (Load (Val r)))) (P.returns_value 2)

let owned (r flag:H.core_ref) =
  S.star (C.points_to r 0) (C.points_to flag 0)
let initialized (r flag:H.core_ref) (g h:G.name) =
  S.star (owned r flag) (S.star (F.own #int g 1.0R 0) (F.own #int h 1.0R 0))

let from_ghost_owned (r flag:H.core_ref) (g h:G.name)
  : Lemma (P.hoare (initialized r flag g h) (run r flag) (P.returns_value 2))
  = S.sep_laws ();
    let e = run r flag in
    let q = P.returns_value 2 in
    let contents = body r g h in
    let completion = J.body flag (half h 1) in
    let tickets = S.star (half g 0) (half h 0) in
    let prepared = S.star contents (S.star completion tickets) in
    P.allocate_invariant contents (S.star completion tickets) e q (fun i ->
      Pulse.Extrinsic.HeapLang.Invariants.allocate completion (S.star (S.inv i contents) tickets) e q
        (fun j -> run_correct i j r flag g h)
    );
    F.split #int g 0.5R 0.5R 0;
    F.split #int h 0.5R 0.5R 0;
    piece_intro r g h 0 0;
    J.initialize flag (half h 1);
    R.entails_star (piece r g h 0 0) contents (C.points_to flag 0) completion;
    R.entails_refl tickets;
    R.entails_star (S.star (piece r g h 0 0) (C.points_to flag 0))
      (S.star contents completion) tickets tickets;
    introduce forall v. S.implies (q v) (q v) with R.entails_refl (q v);
    P.consequence prepared (initialized r flag g h) e q q

(** Ghost initialization is absorbed before run's first source step. Allocate
    both cells existentially, then instantiate the already-proved initialized
    program; no ghost names or later credits are assumed in the caller's pre. *)
let from_owned (r flag:H.core_ref)
  : Lemma (P.hoare (owned r flag) (run r flag) (P.returns_value 2))
  = S.sep_laws ();
    let e = run r flag in
    let q = P.returns_value 2 in
    let physical = owned r flag in
    let ticket = fun (g:G.name) -> F.own #int g 1.0R 0 in
    assert_norm (F.allocated #int 0 ==
      S.op_exists_Star (fun (g:G.name) -> F.own #int g 1.0R 0));
    let mid = S.star (F.allocated #int 0) physical in
    F.alloc #int GS.empty 0;
    P.update_frame GS.empty GS.empty S.emp (F.allocated #int 0) physical;
    introduce forall (g:G.name). P.hoare (S.star (ticket g) physical) e q
    with (
      let first = S.star (ticket g) physical in
      let both = S.star (F.allocated #int 0) first in
      F.alloc #int GS.empty 0;
      P.update_frame GS.empty GS.empty S.emp (F.allocated #int 0) first;
      introduce forall (h:G.name). P.hoare (S.star (ticket h) first) e q
      with from_ghost_owned r flag g h;
      R.exists_elim (fun (h:G.name) -> S.star (ticket h) first) (P.wp e q);
      R.exists_star ticket first;
      P.update_hoare first both e q
    );
    R.exists_elim (fun (g:G.name) -> S.star (ticket g) physical) (P.wp e q);
    R.exists_star ticket physical;
    P.update_hoare physical mid e q

(** Open continuations for applying the let rule to program's allocations. *)
let flag_body (r:H.core_ref) : expr [TRef] TInt =
  run_at (Val r) (Var Here)
let counter_body : expr [TRef] TInt =
  let counter = Var Here in
  let! completion = alloc (int_ 0) in
  run_at (weaken counter) completion
let program : expr [] TInt =
  let! counter = alloc (int_ 0) in
  let! completion = alloc (int_ 0) in
  let counter = weaken counter in
  fork (increment_at counter >> J.signal_at completion) >>
  (increment_at counter >> (J.wait_at completion >> load counter))

(** Physical allocation supplies the counter and flag ownership. The nested
    let rules discharge their binders, leaving the proved exact result from emp.
    counter_body/flag_body above are continuation views used by those rules. *)
let program_correct ()
  : Lemma (P.hoare S.emp program (P.returns_value 2))
  = S.sep_laws ();
    let q = P.returns_value 2 in
    P.alloc 0;
    introduce forall r. P.hoare (P.allocation_post 0 r) (substitute r counter_body) q
    with (
      let point = C.points_to r 0 in
      let mid = P.framed_post (P.allocation_post 0) point in
      assert_norm (substitute r counter_body == Let (Alloc (Val 0)) (flag_body r));
      P.alloc 0;
      P.frame S.emp (Alloc (Val 0)) (P.allocation_post 0) point;
      introduce forall flag. P.hoare (mid flag) (substitute flag (flag_body r)) q
      with (
        assert_norm (substitute flag (flag_body r) == run r flag);
        from_owned r flag
      );
      P.let_rule point (Alloc (Val 0)) (flag_body r) mid q
    );
    P.let_rule S.emp (Alloc (Val 0)) counter_body (P.allocation_post 0) q
