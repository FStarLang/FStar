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
module Pulse.Extrinsic.HeapLang.Proof

open Pulse.Extrinsic.HeapLang
module S = PulseCore.IndirectionTheorySep
module C = Pulse.Extrinsic.HeapLang.Logic
module E = Pulse.Extrinsic.HeapLang.Semantics
module H = Pulse.Extrinsic.HeapLang.Rules
module K = Pulse.Extrinsic.HeapLang.Contexts
module R = Pulse.Extrinsic.Rules
module W = Pulse.Extrinsic.WP
module A = Pulse.Extrinsic.AtomicLogic

let packed_post (#t:ty) (q:post t) (v:E.packed_value) =
  let E.PackValue u v = v in
  if u = t then q v else S.pure False

let wp #t e q = W.wp E.language C.physical (E.Pack t e) (packed_post q)

let packed_mono (#t:ty) (q q':post t)
  : Lemma (requires forall v. S.implies (q v) (q' v))
      (ensures forall v. S.implies (packed_post q v) (packed_post q' v))
  = introduce forall v. S.implies (packed_post q v) (packed_post q' v)
    with (let E.PackValue u v = v in if u <> t then R.entails_refl (S.pure False))

let consequence #t p p' e q q' =
  packed_mono q q';
  R.hoare_consequence E.language C.physical p p' (E.Pack t e) (packed_post q) (packed_post q')

let packed_frame (#t:ty) (q:post t) (f:S.slprop)
  : Lemma (forall v. S.implies (W.framed_post E.language (packed_post q) f v)
      (packed_post (framed_post q f) v))
  = introduce forall v. S.implies (W.framed_post E.language (packed_post q) f v)
      (packed_post (framed_post q f) v)
    with (
      let E.PackValue u v = v in
      if u = t then R.entails_refl (S.star (q v) f)
      else (S.sep_laws (); R.entails_emp f; R.entails_refl (S.pure False);
        R.entails_star (S.pure False) (S.pure False) f S.emp)
    )

let frame #t p e q f =
  S.sep_laws ();
  R.hoare_frame E.language C.physical p (E.Pack t e) (packed_post q) f;
  packed_frame q f;
  R.entails_refl (S.star p f);
  R.hoare_consequence E.language C.physical (S.star p f) (S.star p f) (E.Pack t e)
    (W.framed_post E.language (packed_post q) f) (packed_post (framed_post q f))

let pure_pre #t p fact e q proof =
  R.hoare_pure E.language C.physical p fact (E.Pack t e) (packed_post q) proof

let value_rule #t p v q = H.wp_value p v (packed_post q)

let let_rule #a #b p bound body mid q =
  let k = K.let_context body in
  let next = W.bind_post E.language C.physical k (packed_post q) in
  introduce forall v. S.implies (packed_post mid v) (next v)
  with (
    let E.PackValue t v = v in
    if t = a then H.wp_beta (mid v) v body (packed_post q)
    else R.entails_false (next (E.PackValue t v))
  );
  W.wp_mono E.language C.physical (E.Pack a bound) (packed_post mid) next;
  R.entails_trans p (wp bound mid) (W.wp E.language C.physical (E.Pack a bound) next);
  W.wp_bind E.language C.physical k (E.Pack a bound) (packed_post q);
  R.entails_trans p (W.wp E.language C.physical (E.Pack a bound) next)
    (wp (Let bound body) q)

let sequence #t p mid first rest q =
  let k = K.seq_context rest in
  let next = W.bind_post E.language C.physical k (packed_post q) in
  introduce forall v. S.implies (packed_post (constant_post #TUnit mid) v) (next v)
  with (
    let E.PackValue u v = v in
    if u = TUnit then H.wp_sequence_value mid rest (packed_post q)
    else R.entails_false (next (E.PackValue u v))
  );
  W.wp_mono E.language C.physical (E.Pack TUnit first) (packed_post (constant_post #TUnit mid)) next;
  R.entails_trans p (wp first (constant_post mid)) (W.wp E.language C.physical (E.Pack TUnit first) next);
  W.wp_bind E.language C.physical k (E.Pack TUnit first) (packed_post q);
  R.entails_trans p (W.wp E.language C.physical (E.Pack TUnit first) next)
    (wp (Seq first rest) q)

let fork parent child e q =
  introduce forall v. S.implies (packed_post (constant_post #TUnit S.emp) v) (W.discard E.language v)
  with R.entails_emp (packed_post (constant_post #TUnit S.emp) v);
  R.entails_refl child;
  R.hoare_consequence E.language C.physical child child (E.Pack TUnit e)
    (packed_post (constant_post #TUnit S.emp)) (W.discard E.language);
  H.wp_fork parent child e (packed_post q)

let add x y =
  let q = packed_post (returns_value (x + y)) in
  S.sep_laws ();
  W.children_nil E.language (W.wp_family E.language C.physical);
  R.entails_fact S.emp (x + y == x + y);
  H.wp_value S.emp (x + y) q;
  H.wp_transition S.emp (Add (Val x) (Val y)) (Val (x + y)) [] q
    (fun m -> E.add_transition x y (C.physical m))

let atomic #t mask p e q = A.hoare E.language C.physical mask p (E.Pack t e) (packed_post q)

let atomic_consequence #t mask p p' e q q' =
  packed_mono q q';
  A.consequence E.language C.physical mask p p' (E.Pack t e) (packed_post q) (packed_post q')

let atomic_frame #t mask p e q f =
  A.frame E.language C.physical mask p (E.Pack t e) (packed_post q) f;
  packed_frame q f;
  R.entails_refl (S.star p f);
  A.consequence E.language C.physical mask (S.star p f) (S.star p f) (E.Pack t e)
    (W.framed_post E.language (packed_post q) f) (packed_post (framed_post q f))

let atomic_exists #a #t mask p e q =
  A.exists_pre E.language C.physical mask p (E.Pack t e) (packed_post q)

let atomic_invariant #t mask i p pre e q =
  let body = packed_post (prepend_post (exposed p) q) in
  let post = packed_post q in
  let body_pre = S.star (exposed p) pre in
  introduce forall v. S.implies (body v) (Pulse.Extrinsic.Atomic.exposed_post p post v)
  with (
    let E.PackValue u v = v in
    if u = t then R.entails_refl (S.star (exposed p) (q v))
    else R.entails_false (Pulse.Extrinsic.Atomic.exposed_post p post (E.PackValue u v))
  );
  R.entails_refl body_pre;
  A.consequence E.language C.physical (S.add_inv mask i) body_pre body_pre (E.Pack t e)
    body (Pulse.Extrinsic.Atomic.exposed_post p post);
  A.invariant E.language C.physical mask i p pre (E.Pack t e) post;
  packed_frame q (S.inv i p);
  S.sep_laws ();
  R.entails_refl (S.star (S.inv i p) pre);
  A.consequence E.language C.physical mask (S.star (S.inv i p) pre) (S.star (S.inv i p) pre)
    (E.Pack t e) (Pulse.Extrinsic.Atomic.protected_post i p post)
    (packed_post (prepend_post (S.inv i p) q))

let atomic_to_hoare #t p e q =
  A.to_wp E.language C.physical p (E.Pack t e) (packed_post q)

let primitive_result (#t:ty) (mask:S.inames) (q:post t) (v:value t)
  (f:S.slprop) (m next:S.full_mem) (e':E.packed_expr) (s':Pulse.Extrinsic.HeapLang.Memory.heap)
  (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_to_val e' == Some (E.PackValue t v) /\ spawned == [] /\
        C.physical next == s' /\ S.level next == S.level m /\ S.budget next == S.budget m /\
        S.inames_ok mask next /\
        S.interp (S.star (S.star (q v) f) (S.mem_invariant mask next)) next)
      (ensures A.result E.language C.physical mask (packed_post q) f m e' s' spawned)
  = introduce exists result (next:S.full_mem).
      E.packed_to_val e' == Some result /\ spawned == [] /\ C.physical next == s' /\
      S.level next <= S.level m /\ S.budget next >= S.budget m - 1 /\
      (S.level next == S.level m ==> S.budget next >= S.budget m) /\
      S.inames_ok mask next /\
      S.interp (S.star (S.star (packed_post q result) f) (S.mem_invariant mask next)) next
    with (E.PackValue t v) next and ()

let atomic_load mask r old =
  let p = C.points_to r old in
  let q = read_post r old in
  S.sep_laws ();
  A.lift E.language C.physical mask p (E.Pack TInt (Load (Val r))) (packed_post q)
    (fun f m ->
      S.destruct_star_l p (S.star f (S.mem_invariant mask m)) m;
      C.points_to_contents r old m;
      E.read_transition r old (C.physical m);
      E.pack_transition (Load (Val r)) (Val old) [] (C.physical m);
      R.fact_emp (old == old);
      introduce forall e' s' spawned.
        E.packed_step (E.Pack TInt (Load (Val r))) (C.physical m) e' s' spawned ==>
        A.result E.language C.physical mask (packed_post q) f m e' s' spawned
      with (
        if E.packed_step (E.Pack TInt (Load (Val r))) (C.physical m) e' s' spawned then
          primitive_result mask q old f m m e' s' spawned
      ))

let atomic_store mask r old desired =
  let p = C.points_to r old in
  let q = constant_post #TUnit (C.points_to r desired) in
  A.lift E.language C.physical mask p (E.Pack TUnit (Store (Val r) (Val desired))) (packed_post q)
    (fun f m ->
      let next = C.write_memory mask r old desired f m in
      E.store_atomic r desired (C.physical m) (C.physical next);
      introduce forall e' s' spawned.
        E.packed_step (E.Pack TUnit (Store (Val r) (Val desired))) (C.physical m) e' s' spawned ==>
        A.result E.language C.physical mask (packed_post q) f m e' s' spawned
      with (
        if E.packed_step (E.Pack TUnit (Store (Val r) (Val desired))) (C.physical m) e' s' spawned then
          primitive_result mask q () f m next e' s' spawned
      ))

let load r old =
  atomic_load Pulse.Lib.GhostSet.empty r old;
  atomic_to_hoare (C.points_to r old) (Load (Val r))
    (read_post r old)

let store r old desired =
  atomic_store Pulse.Lib.GhostSet.empty r old desired;
  atomic_to_hoare (C.points_to r old) (Store (Val r) (Val desired)) (constant_post (C.points_to r desired))

let allocate_invariant #t p pre e q proof =
  S.sep_laws ();
  W.wp_lift E.language C.physical (S.star p pre) (E.Pack t e) (packed_post q)
    (fun f m ->
      let (| i, next |) = Pulse.Extrinsic.Atomic.allocate_invariant p (S.star pre f) m in
      C.ghost_physical m next;
      proof i;
      H.apply_frame (S.star (S.inv i p) pre) (wp e q) (S.star f (W.invariant next)) next;
      W.wp_step E.language C.physical (E.Pack t e) (packed_post q) f next)
