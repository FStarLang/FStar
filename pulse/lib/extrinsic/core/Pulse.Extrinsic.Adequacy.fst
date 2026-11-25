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
module Pulse.Extrinsic.Adequacy

(** Once-for-all concurrent soundness, independent of any client program.
    [pool] owns the main WP with the observed postcondition and each child's
    WP with discard. Decompose at the scheduler's chosen index, apply wp_step,
    and reassemble the pool including newly spawned children.

    A run of n steps needs initial budget n+1, leaving enough to prove safety
    at the final state. Realizability at every budget removes this finite bound
    from the theorem's premise. Results concern arbitrary finite schedules:
    neither fairness nor termination nor implicit joining follows. *)

open FStar.List.Tot
module LP = FStar.List.Tot.Properties
module L = Pulse.Extrinsic.Language
module W = Pulse.Extrinsic.WP
module S = PulseCore.IndirectionTheorySep

unfold let children (l:L.language) (physical:W.projection l) (es:list l.L.expr) =
  W.children l (W.wp_family l physical) es

let pool (l:L.language) (physical:W.projection l) (q:W.post l) (es:list l.L.expr) =
  match es with
  | [] -> S.emp
  | e :: es -> S.star (W.wp l physical e q) (children l physical es)

let selected_post (l:L.language) (q:W.post l) (before:list l.L.expr) =
  match before with | [] -> q | _ -> W.discard l

let others (l:L.language) (physical:W.projection l)
  (q:W.post l) (before after:list l.L.expr) =
  match before with
  | [] -> children l physical after
  | _ -> S.star (pool l physical q before) (children l physical after)

let rec children_append (l:L.language) (physical:W.projection l) (xs ys:list l.L.expr)
  : Lemma (children l physical (xs @ ys) ==
      S.star (children l physical xs) (children l physical ys))
      (decreases xs)
  = S.sep_laws ();
    match xs with
    | [] -> W.children_nil l (W.wp_family l physical)
    | x :: xs ->
        W.children_cons l (W.wp_family l physical) x (xs @ ys);
        W.children_cons l (W.wp_family l physical) x xs;
        children_append l physical xs ys

(** Resource selection follows the scheduler's arbitrary before/e/after split.
    Only index zero carries the observable main-thread postcondition. *)
let pool_decompose (l:L.language) (physical:W.projection l)
  (q:W.post l) (before:list l.L.expr) (e:l.L.expr) (after:list l.L.expr)
  : Lemma (
      pool l physical q (before @ (e :: after)) ==
      S.star (W.wp l physical e (selected_post l q before))
        (others l physical q before after))
  = S.sep_laws ();
    match before with
    | [] ->
        assert_norm (pool l physical q (e :: after) ==
          S.star (W.wp l physical e q) (children l physical after));
        assert_norm (selected_post l q [] == q);
        assert_norm (others l physical q [] after == children l physical after)
    | first :: rest ->
        assert_norm (pool l physical q ((first :: rest) @ (e :: after)) ==
          S.star (W.wp l physical first q) (children l physical (rest @ (e :: after))));
        assert_norm (selected_post l q (first :: rest) == W.discard l);
        assert_norm (pool l physical q (first :: rest) ==
          S.star (W.wp l physical first q) (children l physical rest));
        assert_norm (others l physical q (first :: rest) after ==
          S.star (pool l physical q (first :: rest)) (children l physical after));
        children_append l physical rest (e :: after);
        W.children_cons l (W.wp_family l physical) e after

let pool_reassemble (l:L.language) (physical:W.projection l)
  (q:W.post l) (before:list l.L.expr) (e:l.L.expr) (after spawned:list l.L.expr)
  : Lemma (
      S.star (W.wp l physical e (selected_post l q before))
        (S.star (children l physical spawned) (others l physical q before after)) ==
      pool l physical q (before @ (e :: (after @ spawned))))
  = S.sep_laws ();
    pool_decompose l physical q before e (after @ spawned);
    children_append l physical after spawned;
    match before with | [] -> () | _ -> ()

let represents (l:L.language) (physical:W.projection l)
  (q:W.post l) (c:L.config l) (m:S.full_mem) : prop =
  physical m == c.L.state /\
  S.interp (S.star (pool l physical q c.L.threads) (W.invariant m)) m

let pool_safe (l:L.language) (physical:W.projection l)
  (q:W.post l) (c:L.config l) (m:S.full_mem)
  : Lemma (requires represents l physical q c m /\ S.budget m > 0)
          (ensures L.safe l c)
  = S.sep_laws ();
    introduce forall e. memP e c.L.threads ==> L.not_stuck l e c.L.state with (
      introduce memP e c.L.threads ==> L.not_stuck l e c.L.state with (
        LP.lemma_split_using c.L.threads e;
        let before, rest = split_using c.L.threads e in
        match rest with
        | [] -> ()
        | _ :: after ->
            pool_decompose l physical q before e after;
            match l.L.to_val e with
            | Some _ -> ()
            | None ->
                W.wp_step l physical e (selected_post l q before)
                  (others l physical q before after) m
      )
    )

let pool_result (l:L.language) (physical:W.projection l)
  (q:W.post l) (c:L.config l) (m:S.full_mem) (v:l.L.value)
  : Lemma
      (requires represents l physical q c m /\ L.main_returns l c v)
      (ensures S.interp (q v) m)
  = S.sep_laws ();
    match c.L.threads with
    | [] -> ()
    | e :: rest ->
        W.wp_value l physical e v q;
        S.destruct_star_l (q v) (S.star (children l physical rest) (W.invariant m)) m

(** Retain the ambient invariant resource when observing a returned value.
    Modal postconditions need it to execute their final closed-mask update. *)
let pool_result_with_invariant (l:L.language) (physical:W.projection l)
  (q:W.post l) (c:L.config l) (m:S.full_mem) (v:l.L.value)
  : Lemma
      (requires represents l physical q c m /\ L.main_returns l c v)
      (ensures S.interp (S.star (q v) (W.invariant m)) m)
  = S.sep_laws ();
    match c.L.threads with
    | [] -> ()
    | e :: rest ->
        W.wp_value l physical e v q;
        S.destruct_star_l (S.star (q v) (W.invariant m)) (children l physical rest) m

let represents_framed (l:L.language) (physical:W.projection l)
  (q:W.post l) (frame:S.slprop) (c:L.config l) (m:S.full_mem) : prop =
  physical m == c.L.state /\
  S.interp (S.star (pool l physical q c.L.threads) (S.star frame (W.invariant m))) m

(** Other threads and the external frame are the selected thread's WP frame.
    Its successor resources account for the original pool plus every child
    emitted by this particular operational step. *)
let preserve_step_framed (l:L.language) (physical:W.projection l) (q:W.post l) (frame:S.slprop)
  (#c #c':L.config l) (step:L.pool_step l c c') (m:S.full_mem)
  : Lemma
      (requires represents_framed l physical q frame c m /\ S.budget m > 0)
      (ensures exists (m':S.full_mem).
        represents_framed l physical q frame c' m' /\ S.budget m' >= S.budget m - 1)
  = S.sep_laws ();
    let L.Schedule before e after s e' s' spawned _ = step in
    pool_decompose l physical q before e after;
    L.step_not_value l e s e' s' spawned;
    W.wp_step l physical e (selected_post l q before)
      (S.star (others l physical q before after) frame) m;
    eliminate exists (m':S.full_mem).
      physical m' == s' /\
      S.level m' < S.level m /\
      S.budget m' >= S.budget m - 1 /\
      S.interp
        (S.star (W.wp l physical e' (selected_post l q before))
          (S.star (children l physical spawned)
            (S.star (S.star (others l physical q before after) frame) (W.invariant m')))) m'
    with (
      pool_reassemble l physical q before e' after spawned;
      assert (S.interp
        (S.star (pool l physical q c'.L.threads) (S.star frame (W.invariant m'))) m');
      introduce exists (m':S.full_mem).
        represents_framed l physical q frame c' m' /\ S.budget m' >= S.budget m - 1
      with m' and ()
    )

let rec preserve_execution_framed
  (l:L.language) (physical:W.projection l) (q:W.post l) (frame:S.slprop)
  (#n:nat) (#c #c':L.config l) (run:L.execution l n c c') (m:S.full_mem)
  : Lemma
      (requires represents_framed l physical q frame c m /\ S.budget m >= n + 1)
      (ensures exists (m':S.full_mem).
        represents_framed l physical q frame c' m' /\ S.budget m' > 0)
      (decreases run)
  = match run with
    | L.Done _ ->
        introduce exists (m':S.full_mem).
          represents_framed l physical q frame c' m' /\ S.budget m' > 0
        with m and ()
    | L.Step #_ #remaining #_ #middle #_ step rest ->
        preserve_step_framed l physical q frame step m;
        eliminate exists (m1:S.full_mem).
          represents_framed l physical q frame middle m1 /\ S.budget m1 >= S.budget m - 1
        with preserve_execution_framed l physical q frame rest m1

let preserve_step (l:L.language) (physical:W.projection l) (q:W.post l)
  (#c #c':L.config l) (step:L.pool_step l c c') (m:S.full_mem)
  : Lemma
      (requires represents l physical q c m /\ S.budget m > 0)
      (ensures exists (m':S.full_mem).
        represents l physical q c' m' /\ S.budget m' >= S.budget m - 1)
  = S.sep_laws ();
    preserve_step_framed l physical q S.emp step m

let preserve_execution
  (l:L.language) (physical:W.projection l) (q:W.post l)
  (#n:nat) (#c #c':L.config l) (run:L.execution l n c c') (m:S.full_mem)
  : Lemma
      (requires represents l physical q c m /\ S.budget m >= n + 1)
      (ensures exists (m':S.full_mem).
        represents l physical q c' m' /\ S.budget m' > 0)
  = S.sep_laws ();
    preserve_execution_framed l physical q S.emp run m

let adequate
  (l:L.language) (physical:W.projection l) (q:W.post l)
  (#n:nat) (#c #c':L.config l) (run:L.execution l n c c') (m:S.full_mem)
  : Lemma
      (requires represents l physical q c m /\ S.budget m >= n + 1)
      (ensures L.safe l c' /\
        (forall v. L.main_returns l c' v ==>
          exists (m':S.full_mem). physical m' == c'.L.state /\ S.interp (q v) m'))
  = preserve_execution l physical q run m;
    eliminate exists (m':S.full_mem).
      represents l physical q c' m' /\ S.budget m' > 0
    with (
      pool_safe l physical q c' m';
      introduce forall v. L.main_returns l c' v ==>
        (exists (m':S.full_mem). physical m' == c'.L.state /\ S.interp (q v) m')
      with (
        introduce L.main_returns l c' v ==>
          (exists (m':S.full_mem). physical m' == c'.L.state /\ S.interp (q v) m')
        with (
          pool_result l physical q c' m' v;
          introduce exists (m':S.full_mem).
            physical m' == c'.L.state /\ S.interp (q v) m'
          with m' and ()
        )
      )
    )

let adequate_realizable
  (l:L.language) (physical:W.projection l) (q:W.post l)
  (#n:nat) (#c #c':L.config l) (run:L.execution l n c c')
  : Lemma
      (requires forall (budget:nat). exists (m:S.full_mem).
        represents l physical q c m /\ S.budget m >= budget)
      (ensures L.safe l c' /\
        (forall v. L.main_returns l c' v ==>
          exists (m':S.full_mem). physical m' == c'.L.state /\ S.interp (q v) m'))
  = eliminate exists (m:S.full_mem).
      represents l physical q c m /\ S.budget m >= n + 1
    with adequate l physical q run m
