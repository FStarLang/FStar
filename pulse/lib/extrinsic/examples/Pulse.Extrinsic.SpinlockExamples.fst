module Pulse.Extrinsic.SpinlockExamples

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module G = Pulse.Extrinsic.Ghost
module K = Pulse.Extrinsic.HeapLang.Spinlock

let finish_at (#ctx:list ty) (r flag:expr ctx TRef) : expr (TInt :: ctx) TInt =
  Seq (Store (rename (fun _ x -> There x) r) (Val 0))
    (Seq (K.release_at (rename (fun _ x -> There x) flag)) (Var Here))
let critical_at (#ctx:list ty) (r flag:expr ctx TRef) : expr ctx TInt =
  Seq (Store r (Val 1)) (Let (Load r) (finish_at r flag))
let client_at (#ctx:list ty) (r flag:expr ctx TRef) : expr ctx TInt =
  Seq (K.acquire_at flag) (critical_at r flag)
let client (r flag:H.core_ref) = client_at (Val #[] r) (Val flag)

let finish_correct (i:S.iref) (g:G.name) (r flag:H.core_ref) (v:int)
  : Lemma (
      let shared = K.handle i g flag (C.points_to r 0) in
      let pre = S.star shared (S.star (K.held g (C.points_to r 1)) (S.pure (v == 1))) in
      P.hoare pre (substitute v (finish_at (Val #[] r) (Val flag)))
        (P.prepend_post shared (P.returns_value 1)))
  = S.sep_laws ();
    let shared = K.handle i g flag (C.points_to r 0) in
    let fact = S.pure (v == 1) in
    let held = K.held g S.emp in
    let tail = S.star shared (S.star held fact) in
    let before = S.star (C.points_to r 1) tail in
    let restored = S.star (C.points_to r 0) tail in
    let post = P.prepend_post shared (P.returns_value 1) in
    K.held_frame g (C.points_to r 0);
    K.held_frame g (C.points_to r 1);
    C.points_to_exposed r 0;
    P.store r 1 0;
    P.frame_constant (C.points_to r 1) (Store (Val r) (Val 0)) (C.points_to r 0) tail;
    K.release_correct i g flag (C.points_to r 0);
    P.frame_constant (S.star shared (K.held g (C.points_to r 0))) (K.release flag) shared fact;
    R.entails_refl (S.star shared fact);
    P.value_rule (S.star shared fact) v post;
    P.sequence restored (S.star shared fact) (K.release flag) (Val v) post;
    P.sequence before restored (Store (Val r) (Val 0)) (Seq (K.release flag) (Val v)) post;
    assert_norm (substitute v (finish_at (Val #[] r) (Val flag)) ==
      Seq (Store (Val r) (Val 0)) (Seq (K.release flag) (Val v)))

let client_correct (i:S.iref) (g:G.name) (r flag:H.core_ref)
  : Lemma (
      let shared = K.handle i g flag (C.points_to r 0) in
      P.hoare shared (client r flag) (P.prepend_post shared (P.returns_value 1)))
  = S.sep_laws ();
    let shared = K.handle i g flag (C.points_to r 0) in
    let held = K.held g S.emp in
    let tail = S.star shared held in
    let acquired = S.star (C.points_to r 0) tail in
    let written = S.star (C.points_to r 1) tail in
    let post = P.prepend_post shared (P.returns_value 1) in
    let mid = P.framed_post (P.read_post r 1) tail in
    K.held_frame g (C.points_to r 0);
    K.held_frame g (C.points_to r 1);
    C.points_to_exposed r 0;
    K.acquire_correct i g flag (C.points_to r 0);
    P.store r 0 1;
    P.frame_constant (C.points_to r 0) (Store (Val r) (Val 1)) (C.points_to r 1) tail;
    P.load r 1;
    P.frame (C.points_to r 1) (Load (Val r)) (P.read_post r 1) tail;
    introduce forall v. P.hoare (mid v)
      (substitute v (finish_at (Val #[] r) (Val flag))) post
    with finish_correct i g r flag v;
    P.let_rule written (Load (Val r)) (finish_at (Val #[] r) (Val flag)) mid post;
    P.sequence acquired written (Store (Val r) (Val 1))
      (Let (Load (Val r)) (finish_at (Val #[] r) (Val flag))) post;
    P.sequence shared acquired (K.acquire flag) (critical_at (Val #[] r) (Val flag)) post

let concurrent_at (#ctx:list ty) (r flag:expr ctx TRef) : expr ctx TInt =
  Seq (Fork (Let (client_at r flag) (Val ()))) (client_at r flag)
let concurrent (r flag:H.core_ref) = concurrent_at (Val #[] r) (Val flag)

let concurrent_correct (i:S.iref) (g:G.name) (r flag:H.core_ref)
  : Lemma (
      let shared = K.handle i g flag (C.points_to r 0) in
      P.hoare shared (concurrent r flag) (P.prepend_post shared (P.returns_value 1)))
  = S.sep_laws ();
    let shared = K.handle i g flag (C.points_to r 0) in
    let post = P.prepend_post shared (P.returns_value 1) in
    let child = Let (client r flag) (Val ()) in
    client_correct i g r flag;
    introduce forall v. P.hoare (post v) (substitute v (Val #[TInt] ())) (P.constant_post S.emp)
    with (
      R.entails_emp (post v);
      P.value_rule (post v) () (P.constant_post S.emp)
    );
    P.let_rule shared (client r flag) (Val ()) post (P.constant_post S.emp);
    K.duplicate i g flag (C.points_to r 0);
    R.entails_refl shared;
    P.fork shared shared child (P.constant_post shared);
    P.sequence shared shared (Fork child) (client r flag) post

let from_owned (r flag:H.core_ref)
  : Lemma (P.hoare (S.star (C.points_to r 0) (C.points_to flag 1))
      (concurrent r flag) (P.returns_value 1))
  = S.sep_laws ();
    K.allocate flag (C.points_to r 0) (concurrent r flag) (P.returns_value 1)
      (fun i g ->
        let shared = K.handle i g flag (C.points_to r 0) in
        concurrent_correct i g r flag;
        R.entails_refl shared;
        introduce forall v. S.implies (P.prepend_post shared (P.returns_value 1) v)
          (P.returns_value 1 v)
        with R.entails_left (P.returns_value 1 v) shared;
        P.consequence shared shared (concurrent r flag)
          (P.prepend_post shared (P.returns_value 1)) (P.returns_value 1))

let flag_body (r:H.core_ref) : expr [TRef] TInt =
  concurrent_at (Val r) (Var Here)
let data_body : expr [TRef] TInt =
  Let (Alloc (Val 1)) (concurrent_at (Var (There Here)) (Var Here))
let program : expr [] TInt = Let (Alloc (Val 0)) data_body

let program_correct ()
  : Lemma (P.hoare S.emp program (P.returns_value 1))
  = S.sep_laws ();
    let q = P.returns_value 1 in
    P.alloc 0;
    introduce forall r. P.hoare (P.allocation_post 0 r) (substitute r data_body) q
    with (
      let point = C.points_to r 0 in
      let mid = P.framed_post (P.allocation_post 1) point in
      assert_norm (substitute r data_body == Let (Alloc (Val 1)) (flag_body r));
      P.alloc 1;
      P.frame S.emp (Alloc (Val 1)) (P.allocation_post 1) point;
      introduce forall flag. P.hoare (mid flag) (substitute flag (flag_body r)) q
      with (
        assert_norm (substitute flag (flag_body r) == concurrent r flag);
        from_owned r flag
      );
      P.let_rule point (Alloc (Val 1)) (flag_body r) mid q
    );
    P.let_rule S.emp (Alloc (Val 0)) data_body (P.allocation_post 0) q
