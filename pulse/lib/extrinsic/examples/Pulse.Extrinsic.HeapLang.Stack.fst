module Pulse.Extrinsic.HeapLang.Stack

(** Build stack operations out of the verified node/list interface.
    publish allocates x::xs while retaining the old sentinel ownership, then
    changes its link and folds contents. push_correct first reads the old
    head and uses the returned equality to instantiate publish.
    peek_correct frames the sentinel through the list head read and reassembles
    the same contents with the exact result. All reasoning is source-level. *)

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module N = Pulse.Extrinsic.HeapLang.Nodes
module LL = Pulse.Extrinsic.HeapLang.List
module R = Pulse.Extrinsic.Rules

let contents_intro root head xs =
  R.exists_intro (owned root xs) head

(** The new list owns both the new cell and the old tail. Updating root does
    not discard either; contents_intro repackages the new head existential. *)
let publish (root head:H.core_ref) (x:int) (xs:list int)
  : Lemma (P.hoare (S.star (N.node root 0 head) (LL.is_list head xs))
      (Let (NewNode (Val x) (Val head)) (WriteNext (Val root) (Var Here)))
      (P.constant_post (contents root (x :: xs))))
  = S.sep_laws ();
    let pre = S.star (N.node root 0 head) (LL.is_list head xs) in
    let post = P.constant_post #TUnit (contents root (x :: xs)) in
    let fresh = LL.list_post (x :: xs) in
    let mid = P.framed_post fresh (N.node root 0 head) in
    LL.cons_correct x head xs;
    P.frame (LL.is_list head xs) (NewNode (Val x) (Val head)) fresh (N.node root 0 head);
    introduce forall r. P.hoare (mid r) (substitute r (WriteNext (Val root) (Var Here))) post
    with (
      let e = WriteNext (Val root) (Val r) in
      let after = S.star (N.node root 0 r) (fresh r) in
      N.write_next root 0 head r;
      P.frame_constant (N.node root 0 head) e (N.node root 0 r) (fresh r);
      R.entails_refl (mid r);
      introduce forall (_:unit). S.implies after (contents root (x :: xs))
      with contents_intro root r (x :: xs);
      P.consequence (mid r) (mid r) e (P.constant_post after) post;
      assert_norm (substitute #[] r (WriteNext (Val root) (Var Here)) == e)
    );
    P.let_rule pre (NewNode (Val x) (Val head)) (WriteNext (Val root) (Var Here)) mid post

let push_correct root x xs =
  S.sep_laws ();
  let family = owned root xs in
  let tail : expr [TRef] TUnit =
    Let (NewNode (Val x) (Var Here)) (WriteNext (Val root) (Var Here)) in
  let post = P.constant_post #TUnit (contents root (x :: xs)) in
  introduce forall head. P.hoare (family head) (push root x) post
  with (
    let mid = P.framed_post (N.next_post root 0 head) (LL.is_list head xs) in
    N.read_next root 0 head;
    P.frame (N.node root 0 head) (ReadNext (Val root)) (N.next_post root 0 head) (LL.is_list head xs);
    introduce forall v. P.hoare (mid v) (substitute v tail) post
    with P.pure_pre (family head) (v == head) (substitute v tail) post (fun _ ->
      publish root head x xs;
      assert_norm (substitute head tail ==
        Let (NewNode (Val x) (Val head)) (WriteNext (Val root) (Var Here))));
    P.let_rule (family head) (ReadNext (Val root)) tail mid post;
    assert_norm (push root x == Let (ReadNext (Val root)) tail)
  );
  R.exists_elim family (P.wp (push root x) post)

let peek_correct root x xs =
  S.sep_laws ();
  let family = owned root (x :: xs) in
  let contents = contents root (x :: xs) in
  let post = P.prepend_post contents (P.returns_value x) in
  introduce forall head. P.hoare (family head) (peek root) post
  with (
    let mid = P.framed_post (N.next_post root 0 head) (LL.is_list head (x :: xs)) in
    N.read_next root 0 head;
    P.frame (N.node root 0 head) (ReadNext (Val root)) (N.next_post root 0 head) (LL.is_list head (x :: xs));
    introduce forall v. P.hoare (mid v) (substitute v (ReadData (Var Here))) post
    with P.pure_pre (family head) (v == head) (ReadData (Val v)) post (fun _ ->
      let list = LL.is_list head (x :: xs) in
      let raw = P.framed_post (P.prepend_post list (P.returns_value x)) (N.node root 0 head) in
      LL.head_correct head x xs;
      P.frame list (ReadData (Val head)) (P.prepend_post list (P.returns_value x)) (N.node root 0 head);
      R.entails_refl (family head);
      introduce forall value. S.implies (raw value) (post value)
      with (
        contents_intro root head (x :: xs);
        R.entails_refl (S.pure (value == x));
        R.entails_star (family head) contents (S.pure (value == x)) (S.pure (value == x))
      );
      P.consequence (family head) (family head) (ReadData (Val head)) raw post);
    P.let_rule (family head) (ReadNext (Val root)) (ReadData (Var Here)) mid post
  );
  R.exists_elim family (P.wp (peek root) post)

let exposed root xs =
  introduce forall head. S.implies
    (P.exposed (S.star (N.node root 0 head) (LL.is_list head xs)))
    (S.star (N.node root 0 head) (LL.is_list head xs))
  with (
    N.exposed root 0 head;
    LL.exposed head xs;
    R.exposed_star (N.node root 0 head) (LL.is_list head xs)
  );
  R.exposed_exists (owned root xs)
