module Pulse.Extrinsic.HeapLang.Spinlock

(** Derive a lock from Join by including a full fractional ghost token in
    its deposited payload. Two full tokens cannot compose, so even an empty
    protected resource cannot authorize two holders. Only the handle duplicates.

    acquire/release reuse the proved source programs, not native lock actions.
    allocate introduces the token and invariant before the client's next
    source step. with_lock_correct threads the token and handle as a frame
    across the client's entire body, then releases and returns its result. *)

open Pulse.Extrinsic.HeapLang
open FStar.Real
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module G = Pulse.Extrinsic.Ghost
module F = Pulse.Extrinsic.Ghost.Fractional
module J = Pulse.Extrinsic.HeapLang.Join
module R = Pulse.Extrinsic.Rules
module GS = Pulse.Lib.GhostSet

let token (g:G.name) = F.own #unit g 1.0R ()
let held g resource = S.star (token g) resource
let handle i g flag resource = J.handle i flag (held g resource)

let duplicate i g flag resource = S.dup_inv_equiv i (J.body flag (held g resource))

(** Fractional compatibility would require 1+1 <= 1. This impossibility
    prevents duplicate holders independently of the protected assertion. *)
let exclusive g resource =
  S.sep_laws ();
  F.agree #unit g 1.0R 1.0R () ();
  R.entails_left (S.star (token g) (token g)) (S.star resource resource);
  R.entails_trans (S.star (held g resource) (held g resource))
    (S.star (token g) (token g)) (S.pure (() == () /\ 1.0R +. 1.0R <=. 1.0R));
  R.entails_pure (() == () /\ 1.0R +. 1.0R <=. 1.0R) False;
  R.entails_trans (S.star (held g resource) (held g resource))
    (S.pure (() == () /\ 1.0R +. 1.0R <=. 1.0R)) (S.pure False)

let held_frame g resource = S.sep_laws ()

let acquire_correct i g flag resource =
  F.exposed #unit g 1.0R ();
  R.exposed_star (token g) resource;
  J.wait_correct i flag (held g resource)

let release_correct i g flag resource =
  F.exposed #unit g 1.0R ();
  R.exposed_star (token g) resource;
  J.signal_correct i flag (held g resource)

let allocate #t flag resource e q proof =
  S.sep_laws ();
  let pre = S.star (C.points_to flag 1) resource in
  let mid = S.star (F.allocated #unit ()) pre in
  F.alloc #unit GS.empty ();
  P.update_frame GS.empty GS.empty S.emp (F.allocated #unit ()) pre;
  introduce forall (g:G.name). P.hoare (S.star (token g) pre) e q
  with (
    let payload = held g resource in
    P.allocate_invariant (J.body flag payload) S.emp e q (fun i -> proof i g);
    J.initialize_ready flag payload;
    introduce forall v. S.implies (q v) (q v) with R.entails_refl (q v);
    P.consequence (J.body flag payload) (S.star (token g) pre) e q q
  );
  R.exists_elim (fun (g:G.name) -> S.star (token g) pre) (P.wp e q);
  R.exists_star token pre;
  assert_norm (F.allocated #unit () == S.op_exists_Star token);
  P.update_hoare pre mid e q

(** The client restores resource but may retain q(v). Release consumes the
    restored resource and held token, not q(v), then the value rule returns v. *)
let with_lock_correct #t i g flag resource body q =
  S.sep_laws ();
  let shared = handle i g flag resource in
  let acquired = S.star shared (held g resource) in
  let frame = S.star shared (token g) in
  let mid = P.framed_post (P.prepend_post resource q) frame in
  let post = P.prepend_post shared q in
  let tail : expr [t] t = Seq (release_at (Val flag)) (Var Here) in
  acquire_correct i g flag resource;
  P.frame resource body (P.prepend_post resource q) frame;
  introduce forall v. P.hoare (mid v) (substitute v tail) post
  with (
    release_correct i g flag resource;
    P.frame_constant acquired (release flag) shared (q v);
    R.entails_refl (S.star shared (q v));
    P.value_rule (S.star shared (q v)) v post;
    P.sequence (mid v) (S.star shared (q v)) (release flag) (Val v) post;
    assert_norm (substitute v tail == Seq (release flag) (Val v))
  );
  P.let_rule acquired body tail mid post;
  P.sequence shared acquired (acquire flag) (Let body tail) post
