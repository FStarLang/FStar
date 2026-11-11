module Pulse.Extrinsic.LinkedConcurrent

(** Concurrent insertion and peek over a genuinely linked heap structure.
    A lock protects exists n:pos. contents root (ones n), ensuring that every
    reachable state has a nonempty all-ones list. Push allocates a node and
    publishes its actual reference; peek follows the header and reads its head.

    push_shared/peek_shared establish invariant-preserving exclusive triples;
    concurrent_correct uses the abstract lock to compose them with fork.
    from_owned and program_correct install all resources from physical
    allocation. The parent returns 1 whether it reads the old or the new head,
    so no join is needed. This is lock-based insertion, not lock-free CAS or
    reclamation; the child may remain active when the parent returns. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module R = Pulse.Extrinsic.Rules
module G = Pulse.Extrinsic.Ghost
module N = Pulse.Extrinsic.HeapLang.Nodes
module LL = Pulse.Extrinsic.HeapLang.List
module ST = Pulse.Extrinsic.HeapLang.Stack
module K = Pulse.Extrinsic.HeapLang.Spinlock
module B = Pulse.Extrinsic.ListExamples

let rec ones (n:nat) : Tot (list int) (decreases n) =
  if n = 0 then [] else 1 :: ones (n - 1)
let family (root:H.core_ref) (n:pos) = ST.contents root (ones n)
let resource (root:H.core_ref) = S.op_exists_Star (family root)

(** Existential n is local to this critical section. Push establishes n+1;
    no caller relies on retaining the old witness after releasing the lock. *)
let push_shared (root:H.core_ref)
  : Lemma (P.hoare (resource root) (ST.push root 1) (P.constant_post (resource root)))
  = let post = P.constant_post #TUnit (resource root) in
    introduce forall (n:pos). P.hoare (family root n) (ST.push root 1) post
    with (
      ST.push_correct root 1 (ones n);
      assert (ones (n + 1) == 1 :: ones n);
      R.entails_refl (family root n);
      introduce forall (_:unit). S.implies (ST.contents root (1 :: ones n)) (resource root)
      with R.exists_intro (family root) (n + 1);
      P.consequence (family root n) (family root n) (ST.push root 1)
        (P.constant_post (ST.contents root (1 :: ones n))) post
    );
    R.exists_elim (family root) (P.wp (ST.push root 1) post)

let peek_shared (root:H.core_ref)
  : Lemma (P.hoare (resource root) (ST.peek root)
      (P.prepend_post (resource root) (P.returns_value 1)))
  = let post = P.prepend_post (resource root) (P.returns_value 1) in
    introduce forall (n:pos). P.hoare (family root n) (ST.peek root) post
    with (
      assert (ones n == 1 :: ones (n - 1));
      ST.peek_correct root 1 (ones (n - 1));
      R.entails_refl (family root n);
      introduce forall v. S.implies
        (P.prepend_post (family root n) (P.returns_value 1) v) (post v)
      with (
        R.exists_intro (family root) n;
        R.entails_refl (S.pure (v == 1));
        R.entails_star (family root n) (resource root) (S.pure (v == 1)) (S.pure (v == 1))
      );
      P.consequence (family root n) (family root n) (ST.peek root)
        (P.prepend_post (family root n) (P.returns_value 1)) post
    );
    R.exists_elim (family root) (P.wp (ST.peek root) post)

let resource_exposed (root:H.core_ref)
  : Lemma (S.implies (P.exposed (resource root)) (resource root))
  = introduce forall (n:pos). S.implies (P.exposed (family root n)) (family root n)
    with ST.exposed root (ones n);
    R.exposed_exists (family root)

let concurrent_at (#ctx:list ty) (root flag:expr ctx TRef) : expr ctx TInt =
  fork (K.with_lock_at flag (ST.push_at root 1)) >>
  K.with_lock_at flag (ST.peek_at root)
let concurrent (root flag:H.core_ref) = concurrent_at (Val #[] root) (Val flag)

(** Bracket ordinary multi-step structure operations with the derived lock
    rule, then fork using duplicated handles. The protected list ownership
    transfers on acquire/release and is never duplicated between threads. *)
let concurrent_correct (i:S.iref) (g:G.name) (root flag:H.core_ref)
  : Lemma (P.hoare (K.handle i g flag (resource root)) (concurrent root flag) (P.returns_value 1))
  = S.sep_laws ();
    let payload = resource root in
    let shared = K.handle i g flag payload in
    let child = K.with_lock flag (ST.push root 1) in
    let parent = K.with_lock flag (ST.peek root) in
    let child_post = P.prepend_post shared (P.constant_post #TUnit S.emp) in
    let parent_post = P.prepend_post shared (P.returns_value 1) in
    resource_exposed root;
    push_shared root;
    R.entails_refl payload;
    introduce forall (_:unit). S.implies payload
      (P.prepend_post payload (P.constant_post #TUnit S.emp) ())
    with R.entails_refl payload;
    P.consequence payload payload (ST.push root 1) (P.constant_post payload)
      (P.prepend_post payload (P.constant_post S.emp));
    K.with_lock_correct i g flag payload (ST.push root 1) (P.constant_post S.emp);
    R.entails_refl shared;
    introduce forall v. S.implies (child_post v) S.emp with R.entails_emp (child_post v);
    P.consequence shared shared child child_post (P.constant_post S.emp);
    peek_shared root;
    K.with_lock_correct i g flag payload (ST.peek root) (P.returns_value 1);
    introduce forall v. S.implies (parent_post v) (P.returns_value 1 v)
    with R.entails_left (P.returns_value 1 v) shared;
    P.consequence shared shared parent parent_post (P.returns_value 1);
    K.duplicate i g flag payload;
    P.fork shared shared child (P.constant_post shared);
    P.sequence shared shared (Fork child) parent (P.returns_value 1)

let from_owned (root flag:H.core_ref)
  : Lemma (P.hoare (S.star (ST.contents root [1]) (C.points_to flag 1))
      (concurrent root flag) (P.returns_value 1))
  = S.sep_laws ();
    let pre = S.star (resource root) (C.points_to flag 1) in
    K.allocate flag (resource root) (concurrent root flag) (P.returns_value 1)
      (fun i g -> concurrent_correct i g root flag);
    R.exists_intro (family root) 1;
    R.entails_refl (C.points_to flag 1);
    R.entails_star (ST.contents root [1]) (resource root) (C.points_to flag 1) (C.points_to flag 1);
    introduce forall v. S.implies (P.returns_value 1 v) (P.returns_value 1 v)
    with R.entails_refl (P.returns_value 1 v);
    P.consequence pre (S.star (ST.contents root [1]) (C.points_to flag 1))
      (concurrent root flag) (P.returns_value 1) (P.returns_value 1)

let with_flag_at (#ctx:list ty) (root:expr ctx TRef) : expr ctx TInt =
  let! flag = alloc (int_ 1) in
  concurrent_at (weaken root) flag

let with_flag_correct (root:H.core_ref)
  : Lemma (P.hoare (ST.contents root [1]) (with_flag_at (Val #[] root)) (P.returns_value 1))
  = S.sep_laws ();
    let pre = ST.contents root [1] in
    let mid = P.framed_post (P.allocation_post 1) pre in
    let body : expr [TRef] TInt = concurrent_at (Val root) (Var Here) in
    P.alloc 1;
    P.frame S.emp (Alloc (Val 1)) (P.allocation_post 1) pre;
    introduce forall flag. P.hoare (mid flag) (substitute flag body) (P.returns_value 1)
    with (
      from_owned root flag;
      assert_norm (substitute flag body == concurrent root flag)
    );
    P.let_rule pre (Alloc (Val 1)) body mid (P.returns_value 1)

(** Continuation after building the initial list, for the outer let rule. *)
let head_body : expr [TRef] TInt =
  let head = Var Here in
  let! root = node (int_ 0) head in
  with_flag_at root
let program : expr [] TInt =
  let! head = B.build [1] in
  let! root = node (int_ 0) head in
  let! flag = alloc (int_ 1) in
  concurrent_at (weaken root) flag

let program_correct ()
  : Lemma (P.hoare S.emp program (P.returns_value 1))
  = S.sep_laws ();
    B.build_correct [1];
    introduce forall head. P.hoare (LL.is_list head [1]) (substitute head head_body) (P.returns_value 1)
    with (
      let pre = LL.is_list head [1] in
      let mid = P.framed_post (N.allocated 0 head) pre in
      let body : expr [TRef] TInt = with_flag_at (Var Here) in
      N.new_node 0 head;
      P.frame S.emp (NewNode (Val 0) (Val head)) (N.allocated 0 head) pre;
      introduce forall root. P.hoare (mid root) (substitute root body) (P.returns_value 1)
      with (
        with_flag_correct root;
        ST.contents_intro root head [1];
        introduce forall v. S.implies (P.returns_value 1 v) (P.returns_value 1 v)
        with R.entails_refl (P.returns_value 1 v);
        P.consequence (ST.contents root [1]) (mid root) (with_flag_at (Val #[] root))
          (P.returns_value 1) (P.returns_value 1);
        assert_norm (substitute #[] root (with_flag_at (Var Here)) == with_flag_at (Val #[] root))
      );
      P.let_rule pre (NewNode (Val 0) (Val head)) body mid (P.returns_value 1);
      assert_norm (substitute head head_body == Let (NewNode (Val 0) (Val head)) body)
    );
    P.let_rule S.emp (B.build [1]) head_body (LL.list_post [1]) (P.returns_value 1)
