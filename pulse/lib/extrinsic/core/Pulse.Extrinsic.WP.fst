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
module Pulse.Extrinsic.WP

(** Construction and structural metatheory of the resource WP.
    A fragment is tested in all lower-level full-memory completions. Each
    operational successor must have a matching full logical memory whose
    level strictly decreases and whose budget drops by at most one.

    Read completion/body_pred first, then closure and contractiveness, then
    wp_step/wp_lift. The remaining level inductions prove frame, consequence,
    and bind. Logical level justifies recursion; budget counts the source steps
    available to adequacy. They are different quantities, not program counters. *)
friend PulseCore.IndirectionTheorySep
friend Pulse.Extrinsic.Guarded

module L = Pulse.Extrinsic.Language
module S = PulseCore.IndirectionTheorySep
module G = Pulse.Extrinsic.Guarded
module K = PulseCore.KnotInstantiation
module Set = Pulse.Lib.GhostSet

(** Complete the owned fragment with a frame and the ambient closed invariants.
    Quantifying over all k <= its level makes the resulting WP hereditary;
    quantifying over all completions makes ownership compositional. *)
let completion (h:K.premem) (k:pos) (frame:S.slprop) (m:S.full_mem) : prop =
  S.level m == k /\ S.budget m > 0 /\
  (exists (rest:K.premem).
    S.disjoint_mem (K.age_to_ h k) rest /\
    S.join_premem (K.age_to_ h k) rest == m /\
    S.star frame (invariant m) rest)

let assertion_extend (p:S.slprop) (h extra:K.premem)
  : Lemma
      (requires S.disjoint_mem h extra /\ p h)
      (ensures p (S.join_premem h extra))
  = S.reveal_slprop_ok ();
    S.mem_le_iff h (S.join_premem h extra)

let completion_weaken (h h':K.premem) (k:pos) (frame:S.slprop) (m:S.full_mem)
  : Lemma
      (requires S.mem_le h h' /\ completion h' k frame m)
      (ensures completion h k frame m)
  = S.mem_le_iff h h';
    eliminate exists (extra:K.premem{S.disjoint_mem h extra}).
      S.join_premem h extra == h'
    with (
      S.age_to_join h extra k;
      eliminate exists (rest:K.premem).
        S.disjoint_mem (K.age_to_ h' k) rest /\
        S.join_premem (K.age_to_ h' k) rest == m /\
        S.star frame (invariant m) rest
      with (
        let small = K.age_to_ h k in
        let more = K.age_to_ extra k in
        S.join_premem_commutative (S.join_premem small more) rest;
        S.join_premem_associative rest small more;
        S.join_premem_commutative (S.join_premem rest small) more;
        S.join_premem_associative more rest small;
        S.join_premem_commutative (S.join_premem more rest) small;
        S.join_premem_commutative more rest;
        assertion_extend (S.star frame (invariant m)) rest more;
        S.join_premem_commutative rest more;
        introduce exists (rest':K.premem).
          S.disjoint_mem (K.age_to_ h k) rest' /\
          S.join_premem (K.age_to_ h k) rest' == m /\
          S.star frame (invariant m) rest'
        with (S.join_premem more rest) and ()
      )
    )

let rec children (l:L.language) (w:G.family (query l)) (es:list l.L.expr)
  : Tot S.slprop (decreases es)
  = match es with
    | [] -> S.emp
    | e :: es -> S.star (w (e, discard l)) (children l w es)

let children_nil l w = ()
let children_cons l w e es = assert_norm (
  children l w (e :: es) == S.star (w (e, discard l)) (children l w es))

let continuation (l:L.language) (w:G.family (query l))
  (e:l.L.expr) (q:post l) (spawned:list l.L.expr) (frame:S.slprop) (m:S.full_mem)
  : prop =
  S.interp
    (S.star (w (e, q))
      (S.star (children l w spawned) (S.star frame (invariant m)))) m

[@@"opaque_to_smt"]
let obligation (l:L.language) (physical:projection l) (w:G.family (query l))
  (e:l.L.expr) (q:post l) (k:pos) (frame:S.slprop) (m:S.full_mem) : prop =
  L.reducible l e (physical m) /\
        (forall e' s' spawned.
          l.L.prim_step e (physical m) e' s' spawned ==>
          exists (m':S.full_mem).
            physical m' == s' /\
            S.level m' < k /\
            S.budget m' >= S.budget m - 1 /\
            continuation l w e' q spawned frame m')

(** Values expose q without any step/update. Non-values quantify over possible
    environments, then obligation quantifies over physical successors. The
    existential successor memory is AFTER that universal source-step choice. *)
let body_pred (l:L.language) (physical:projection l) (w:G.family (query l))
  (eq:query l) (h:K.premem) : prop =
  let e, q = eq in
  match l.L.to_val e with
  | Some v -> q v h
  | None ->
      forall (k:pos) (frame:S.slprop) (m:S.full_mem).
        k <= K.level_ h /\ completion h k frame m ==>
        obligation l physical w e q k frame m

let body_hereditary (l:L.language) (physical:projection l)
  (w:G.family (query l)) (eq:query l) (h:K.premem)
  : Lemma
      (requires body_pred l physical w eq h)
      (ensures body_pred l physical w eq (S.age1_ h))
  =
  S.reveal_slprop_ok ();
  let e, q = eq in
  match l.L.to_val e with
   | Some _ -> ()
   | None ->
     introduce forall (k:pos) (frame:S.slprop) (m:S.full_mem).
       k <= K.level_ (S.age1_ h) /\ completion (S.age1_ h) k frame m ==>
       obligation l physical w e q k frame m
     with (
       if k <= K.level_ (S.age1_ h) then (
         S.age_to_age_to h (K.level_ (S.age1_ h)) k;
         assert (K.age_to_ (S.age1_ h) k == K.age_to_ h k)
       )
     )

let body_affine (l:L.language) (physical:projection l)
  (w:G.family (query l)) (eq:query l) (h h':K.premem)
  : Lemma
      (requires S.mem_le h h' /\ body_pred l physical w eq h)
      (ensures body_pred l physical w eq h')
  =
  S.reveal_slprop_ok ();
  S.reveal_mem_le ();
  let e, q = eq in
  match l.L.to_val e with
   | Some _ -> ()
   | None ->
     introduce forall (k:pos) (frame:S.slprop) (m:S.full_mem).
       completion h' k frame m ==> completion h k frame m
     with (
       introduce completion h' k frame m ==> completion h k frame m
       with completion_weaken h h' k frame m
     )

let body (l:L.language) (physical:projection l) (w:G.family (query l)) (eq:query l)
  : S.slprop =
  S.reveal_slprop_ok ();
  introduce forall h. body_pred l physical w eq h ==>
    body_pred l physical w eq (S.age1_ h)
  with (
    introduce body_pred l physical w eq h ==>
      body_pred l physical w eq (S.age1_ h)
    with body_hereditary l physical w eq h
  );
  introduce forall h h'. S.mem_le h h' /\ body_pred l physical w eq h ==>
    body_pred l physical w eq h'
  with (
    introduce S.mem_le h h' /\ body_pred l physical w eq h ==>
      body_pred l physical w eq h'
    with body_affine l physical w eq h h'
  );
  S.mk_slprop (body_pred l physical w eq)

let equivalent_below (n:nat) (p q:S.slprop) : prop =
  forall h. K.level_ h < n ==> (p h <==> q h)

let star_below_forward (n:nat) (p p' q q':S.slprop) (h:K.premem)
  : Lemma
      (requires equivalent_below n p p' /\ equivalent_below n q q' /\
        K.level_ h < n /\ S.star p q h)
      (ensures S.star p' q' h)
  = let h1, h2 = S.star_elim p q h in
    S.star_intro p' q' h h1 h2

let star_below (n:nat) (p p' q q':S.slprop)
  : Lemma
      (requires equivalent_below n p p' /\ equivalent_below n q q')
      (ensures equivalent_below n (S.star p q) (S.star p' q'))
  = introduce forall h. K.level_ h < n ==> (S.star p q h <==> S.star p' q' h)
    with (
      if K.level_ h < n then (
        introduce S.star p q h ==> S.star p' q' h
        with star_below_forward n p p' q q' h;
        introduce S.star p' q' h ==> S.star p q h
        with star_below_forward n p' p q' q h
      )
    )

let rec children_below (l:L.language) (n:nat)
  (w w':G.family (query l)) (es:list l.L.expr)
  : Lemma
      (requires G.agrees_below n w w')
      (ensures equivalent_below n (children l w es) (children l w' es))
      (decreases es)
  = match es with
    | [] -> ()
    | e :: es ->
        children_below l n w w' es;
        assert_norm (children l w (e :: es) ==
          S.star (w (e, discard l)) (children l w es));
        assert_norm (children l w' (e :: es) ==
          S.star (w' (e, discard l)) (children l w' es));
        star_below n (w (e, discard l)) (w' (e, discard l))
          (children l w es) (children l w' es)

let continuation_below (l:L.language) (n:nat)
  (w w':G.family (query l)) (e:l.L.expr) (q:post l)
  (spawned:list l.L.expr) (frame:S.slprop) (m:S.full_mem)
  : Lemma
      (requires G.agrees_below n w w' /\ S.level m < n)
      (ensures continuation l w e q spawned frame m <==>
               continuation l w' e q spawned frame m)
  = children_below l n w w' spawned;
    let tail = S.star frame (invariant m) in
    star_below n (children l w spawned) (children l w' spawned) tail tail;
    star_below n (w (e, q)) (w' (e, q))
      (S.star (children l w spawned) tail) (S.star (children l w' spawned) tail)

let obligation_below (l:L.language) (physical:projection l) (n:nat)
  (w w':G.family (query l)) (e:l.L.expr) (q:post l)
  (k:pos) (frame:S.slprop) (m:S.full_mem)
  : Lemma
      (requires G.agrees_below n w w' /\ k <= n)
      (ensures obligation l physical w e q k frame m <==>
               obligation l physical w' e q k frame m)
  = reveal_opaque (`%obligation) (obligation l physical w e q k frame m);
    reveal_opaque (`%obligation) (obligation l physical w' e q k frame m);
    introduce forall e' spawned (m':S.full_mem).
      S.level m' < n ==>
      (continuation l w e' q spawned frame m' <==>
       continuation l w' e' q spawned frame m')
    with (
      if S.level m' < n then continuation_below l n w w' e' q spawned frame m'
    )

(** Recursive WPs occur only in continuation at a strictly smaller level.
    The star/children lemmas transport agreement to the entire residual pool,
    establishing the contract required by Guarded.fix. *)
let body_contractive (l:L.language) (physical:projection l)
  : Lemma (G.contractive (body l physical))
  = introduce forall n (w w':G.family (query l)).
      G.agrees_below n w w' ==>
      G.agrees_below (n + 1) (body l physical w) (body l physical w')
    with (
      introduce G.agrees_below n w w' ==>
        G.agrees_below (n + 1) (body l physical w) (body l physical w')
      with (
        introduce forall (eq:query l) h.
          K.level_ h < n + 1 ==> (body l physical w eq h <==> body l physical w' eq h)
        with (
          introduce K.level_ h < n + 1 ==>
            (body l physical w eq h <==> body l physical w' eq h)
          with (
            let e, q = eq in
            match l.L.to_val e with
            | Some _ -> ()
            | None ->
                introduce forall (k:pos) frame (m:S.full_mem).
                  k <= K.level_ h ==>
                  (obligation l physical w e q k frame m <==>
                   obligation l physical w' e q k frame m)
                with (
                  if k <= K.level_ h then obligation_below l physical n w w' e q k frame m
                )
          )
        )
      )
    )

let body_operator (l:L.language) (physical:projection l) : G.operator (query l) =
  body_contractive l physical;
  body l physical

let wp_family l physical = G.fix (body_operator l physical)

let unfold_wp l physical e q =
  G.unfold_fix (body_operator l physical) (e, q);
  assert_norm (
    body_operator l physical (wp_family l physical) (e, q) ==
    body l physical (wp_family l physical) (e, q))

let wp_value l physical e v q =
  unfold_wp l physical e q;
  K.mem_pred_ext (body l physical (wp_family l physical) (e, q)) (q v)
    (fun _ -> ())

(** Elimination chooses the actual full memory as one of the universally
    quantified completions. It is the only WP unfolding adequacy needs. *)
let wp_step l physical e q frame m =
  let owned, rest =
    S.star_elim' (wp l physical e q) (S.star frame (invariant m)) m in
  let k = S.level m in
  K.mem_ext (K.age_to_ owned k) owned (fun _ -> ());
  assert (completion owned k frame m);
  unfold_wp l physical e q;
  assert (body_pred l physical (wp_family l physical) (e, q) owned);
  assert (obligation l physical (wp_family l physical) e q k frame m);
  reveal_opaque (`%obligation) (obligation l physical (wp_family l physical) e q k frame m)

let rec age_interp (p:S.slprop) (h:K.premem) (k:nat{k <= K.level_ h})
  : Lemma (requires p h) (ensures p (K.age_to_ h k))
      (decreases K.level_ h - k)
  = S.reveal_slprop_ok ();
    if k = K.level_ h then
      K.mem_ext (K.age_to_ h k) h (fun _ -> ())
    else (
      age_interp p (S.age1_ h) k;
      S.age_to_age_to h (K.level_ h - 1) k
    )

let wp_lift l physical p e q step =
  unfold_wp l physical e q;
  S.implies_intro p (wp l physical e q) (fun h ->
    introduce forall (k:pos) (frame:S.slprop) (m:S.full_mem).
      k <= K.level_ h /\ completion h k frame m ==>
      obligation l physical (wp_family l physical) e q k frame m
    with (
      introduce k <= K.level_ h /\ completion h k frame m ==>
        obligation l physical (wp_family l physical) e q k frame m
      with (
        age_interp p h k;
        eliminate exists (rest:K.premem).
          S.disjoint_mem (K.age_to_ h k) rest /\
          S.join_premem (K.age_to_ h k) rest == m /\
          S.star frame (invariant m) rest
        with (
          S.star_intro p (S.star frame (invariant m)) m (K.age_to_ h k) rest;
          step frame m;
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) e q k frame m)
        )
      )
    ))

let completion_frame (owned more h:K.premem) (p:S.slprop)
  (k:pos{k <= K.level_ h}) (frame:S.slprop) (m:S.full_mem)
  : Lemma
      (requires S.disjoint_mem owned more /\ S.join_premem owned more == h /\
        p more /\ completion h k frame m)
      (ensures completion owned k (S.star p frame) m)
  = S.sep_laws ();
    S.age_to_join owned more k;
    age_interp p more k;
    eliminate exists (rest:K.premem).
      S.disjoint_mem (K.age_to_ h k) rest /\
      S.join_premem (K.age_to_ h k) rest == m /\
      S.star frame (invariant m) rest
    with (
      let a = K.age_to_ owned k in
      let b = K.age_to_ more k in
      S.join_premem_commutative (S.join_premem a b) rest;
      S.join_premem_associative rest a b;
      S.join_premem_commutative (S.join_premem rest a) b;
      S.join_premem_associative b rest a;
      S.join_premem_commutative (S.join_premem b rest) a;
      S.star_intro p (S.star frame (invariant m)) (S.join_premem b rest) b rest;
      introduce exists (rest':K.premem).
        S.disjoint_mem (K.age_to_ owned k) rest' /\
        S.join_premem (K.age_to_ owned k) rest' == m /\
        S.star (S.star p frame) (invariant m) rest'
      with (S.join_premem b rest) and ()
    )

let joined_level (owned rest:K.premem)
  : Lemma
      (requires S.disjoint_mem owned rest)
      (ensures K.level_ (S.join_premem owned rest) == K.level_ owned)
  = ()

(** Move the extra resource into the environment when taking a step, then
    recursively attach it to the residual postcondition. Children retain
    their original resources and discard postconditions. *)
let rec frame_at (l:L.language) (physical:projection l)
  (e:l.L.expr) (q:post l) (p:S.slprop) (h:K.premem)
  : Lemma
      (requires S.star (wp l physical e q) p h)
      (ensures wp l physical e (framed_post l q p) h)
      (decreases K.level_ h)
  = S.sep_laws ();
    unfold_wp l physical e q;
    unfold_wp l physical e (framed_post l q p);
    match l.L.to_val e with
    | Some v ->
        wp_value l physical e v q;
        wp_value l physical e v (framed_post l q p)
    | None ->
      let owned, more = S.star_elim (wp l physical e q) p h in
      introduce forall (k:pos) (frame:S.slprop) (m:S.full_mem).
        k <= K.level_ h /\ completion h k frame m ==>
        obligation l physical (wp_family l physical) e (framed_post l q p) k frame m
      with (
        introduce k <= K.level_ h /\ completion h k frame m ==>
          obligation l physical (wp_family l physical) e (framed_post l q p) k frame m
        with (
          completion_frame owned more h p k frame m;
          assert (obligation l physical (wp_family l physical) e q k (S.star p frame) m);
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) e q k (S.star p frame) m);
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) e (framed_post l q p) k frame m);
          introduce forall e' s' spawned.
            l.L.prim_step e (physical m) e' s' spawned ==>
            (exists (m':S.full_mem).
              physical m' == s' /\ S.level m' < k /\
              S.budget m' >= S.budget m - 1 /\
              continuation l (wp_family l physical) e' (framed_post l q p) spawned frame m')
          with (
            introduce l.L.prim_step e (physical m) e' s' spawned ==>
              (exists (m':S.full_mem).
                physical m' == s' /\ S.level m' < k /\
                S.budget m' >= S.budget m - 1 /\
                continuation l (wp_family l physical) e' (framed_post l q p) spawned frame m')
            with (
              eliminate exists (m':S.full_mem).
                physical m' == s' /\ S.level m' < k /\
                S.budget m' >= S.budget m - 1 /\
                continuation l (wp_family l physical) e' q spawned (S.star p frame) m'
              with (
                let tail = S.star (children l (wp_family l physical) spawned)
                  (S.star frame (invariant m')) in
                let piece, rest = S.star_elim (S.star (wp l physical e' q) p) tail m' in
                joined_level piece rest;
                assert (K.level_ piece == S.level m');
                assert (K.level_ piece < K.level_ h);
                frame_at l physical e' q p piece;
                S.star_intro (wp l physical e' (framed_post l q p)) tail m' piece rest;
                introduce exists (result:S.full_mem).
                  physical result == s' /\ S.level result < k /\
                  S.budget result >= S.budget m - 1 /\
                  continuation l (wp_family l physical) e' (framed_post l q p) spawned frame result
                with m' and ()
              )
            )
          )
        )
      )

let wp_frame l physical e q frame =
  S.implies_intro (S.star (wp l physical e q) frame)
    (wp l physical e (framed_post l q frame))
    (fun h -> frame_at l physical e q frame h)

let rec mono_at (l:L.language) (physical:projection l)
  (e:l.L.expr) (q q':post l) (h:K.premem)
  : Lemma
      (requires K.level_ h > 0 /\ wp l physical e q h /\
        (forall v. S.implies (q v) (q' v)))
      (ensures wp l physical e q' h)
      (decreases K.level_ h)
  = unfold_wp l physical e q;
    unfold_wp l physical e q';
    match l.L.to_val e with
    | Some v ->
        wp_value l physical e v q;
        wp_value l physical e v q'
    | None ->
      introduce forall (k:pos) (frame:S.slprop) (m:S.full_mem).
        k <= K.level_ h /\ completion h k frame m ==>
        obligation l physical (wp_family l physical) e q' k frame m
      with (
        introduce k <= K.level_ h /\ completion h k frame m ==>
          obligation l physical (wp_family l physical) e q' k frame m
        with (
          assert (obligation l physical (wp_family l physical) e q k frame m);
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) e q k frame m);
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) e q' k frame m);
          introduce forall e' s' spawned.
            l.L.prim_step e (physical m) e' s' spawned ==>
            (exists (m':S.full_mem).
              physical m' == s' /\ S.level m' < k /\
              S.budget m' >= S.budget m - 1 /\
              continuation l (wp_family l physical) e' q' spawned frame m')
          with (
            introduce l.L.prim_step e (physical m) e' s' spawned ==>
              (exists (m':S.full_mem).
                physical m' == s' /\ S.level m' < k /\
                S.budget m' >= S.budget m - 1 /\
                continuation l (wp_family l physical) e' q' spawned frame m')
            with (
              eliminate exists (m':S.full_mem).
                physical m' == s' /\ S.level m' < k /\
                S.budget m' >= S.budget m - 1 /\
                continuation l (wp_family l physical) e' q spawned frame m'
              with (
                let tail = S.star (children l (wp_family l physical) spawned)
                  (S.star frame (invariant m')) in
                let piece, rest = S.star_elim (wp l physical e' q) tail m' in
                joined_level piece rest;
                assert (S.budget m' >= 0);
                assert (S.level m' > 0);
                assert (K.level_ piece == S.level m');
                assert (0 < K.level_ piece /\ K.level_ piece < K.level_ h);
                mono_at l physical e' q q' piece;
                S.star_intro (wp l physical e' q') tail m' piece rest;
                introduce exists (result:S.full_mem).
                  physical result == s' /\ S.level result < k /\
                  S.budget result >= S.budget m - 1 /\
                  continuation l (wp_family l physical) e' q' spawned frame result
                with m' and ()
              )
            )
          )
        )
      )

let wp_mono l physical e q q' =
  S.implies_intro (wp l physical e q) (wp l physical e q')
    (fun h -> mono_at l physical e q q' h)

(** Entailment controls positive levels only. At level one the aged memory
    has level zero, where a non-value WP is vacuous; the non-value premise in
    the interface is therefore essential, not a cosmetic restriction. *)
let later_intro l physical p e q =
  unfold_wp l physical e q;
  S.implies_intro (S.later p) (S.later (wp l physical e q)) (fun h ->
    if K.level_ h > 1 then
      assert (wp l physical e q (S.age1_ h))
    else
      assert (body_pred l physical (wp_family l physical) (e, q) (S.age1_ h)))

let context_progress (l:L.language) (k:context l) (e:l.L.expr) (s:l.L.state)
  : Lemma (requires L.reducible l e s) (ensures L.reducible l (k.plug e) s)
  = let _ = k.steps in
    eliminate exists e' s' spawned. l.L.prim_step e s e' s' spawned with (
      introduce exists next s' spawned. l.L.prim_step (k.plug e) s next s' spawned
      with (k.plug e') s' spawned and ()
    )

(** Context inversion reduces every plugged step to a hole step. Recurse on
    its strictly smaller residual level, and reassemble children/frame/world
    unchanged. At a value, the continuation WP already describes the resume. *)
let rec bind_at (l:L.language) (physical:projection l) (k:context l)
  (e:l.L.expr) (q:post l) (h:K.premem)
  : Lemma
      (requires wp l physical e (bind_post l physical k q) h)
      (ensures wp l physical (k.plug e) q h)
      (decreases K.level_ h)
  = let _ = k.values in
    let _ = k.nonvalues in
    let _ = k.inversion in
    let mid = bind_post l physical k q in
    unfold_wp l physical e mid;
    unfold_wp l physical (k.plug e) q;
    match l.L.to_val e with
    | Some v -> wp_value l physical e v mid
    | None ->
      introduce forall (n:pos) (frame:S.slprop) (m:S.full_mem).
        n <= K.level_ h /\ completion h n frame m ==>
        obligation l physical (wp_family l physical) (k.plug e) q n frame m
      with (
        introduce n <= K.level_ h /\ completion h n frame m ==>
          obligation l physical (wp_family l physical) (k.plug e) q n frame m
        with (
          assert (obligation l physical (wp_family l physical) e mid n frame m);
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) e mid n frame m);
          reveal_opaque (`%obligation)
            (obligation l physical (wp_family l physical) (k.plug e) q n frame m);
          context_progress l k e (physical m);
          introduce forall next s' spawned.
            l.L.prim_step (k.plug e) (physical m) next s' spawned ==>
            (exists (m':S.full_mem).
              physical m' == s' /\ S.level m' < n /\
              S.budget m' >= S.budget m - 1 /\
              continuation l (wp_family l physical) next q spawned frame m')
          with (
            introduce l.L.prim_step (k.plug e) (physical m) next s' spawned ==>
              (exists (m':S.full_mem).
                physical m' == s' /\ S.level m' < n /\
                S.budget m' >= S.budget m - 1 /\
                continuation l (wp_family l physical) next q spawned frame m')
            with (
              eliminate exists e'. next == k.plug e' /\
                l.L.prim_step e (physical m) e' s' spawned
              with (
                eliminate exists (m':S.full_mem).
                  physical m' == s' /\ S.level m' < n /\
                  S.budget m' >= S.budget m - 1 /\
                  continuation l (wp_family l physical) e' mid spawned frame m'
                with (
                  let tail = S.star (children l (wp_family l physical) spawned)
                    (S.star frame (invariant m')) in
                  let piece, rest = S.star_elim (wp l physical e' mid) tail m' in
                  joined_level piece rest;
                  assert (K.level_ piece == S.level m');
                  assert (K.level_ piece < K.level_ h);
                  bind_at l physical k e' q piece;
                  S.star_intro (wp l physical (k.plug e') q) tail m' piece rest;
                  introduce exists (result:S.full_mem).
                    physical result == s' /\ S.level result < n /\
                    S.budget result >= S.budget m - 1 /\
                    continuation l (wp_family l physical) next q spawned frame result
                  with m' and ()
                )
              )
            )
          )
        )
      )

let wp_bind l physical k e q =
  S.implies_intro (wp l physical e (bind_post l physical k q))
    (wp l physical (k.plug e) q) (fun h -> bind_at l physical k e q h)
