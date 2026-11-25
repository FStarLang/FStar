module Pulse.Extrinsic.HeapLang.List

(** Source proofs by existential decomposition of list ownership.
    Each cons witness identifies the next pointer and gives exclusive node
    ownership. Frame the tail through the primitive node operation, use its
    exact returned-value fact, then fold or expose the list as promised.
    exposed is structural induction on the mathematical list, not a proof over
    execution traces. Named postconditions avoid repeated function-eta goals. *)

open Pulse.Extrinsic.HeapLang
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module N = Pulse.Extrinsic.HeapLang.Nodes
module R = Pulse.Extrinsic.Rules

(** Keep the recursive predicate's one-step unfolding explicit. Clients need
    only this equation's consequences, not its logical-memory representation. *)
let cons_unfold (r:H.core_ref) (x:int) (xs:list int)
  : Lemma (is_list r (x :: xs) ==
      S.op_exists_Star (next_post r x xs))
  = assert_norm (is_list r (x :: xs) ==
      S.op_exists_Star (next_post r x xs))

let cons_intro r x next xs =
  cons_unfold r x xs;
  R.exists_intro (next_post r x xs) next

let cons_correct x next xs =
  S.sep_laws ();
  let e = NewNode (Val x) (Val next) in
  let pre = is_list next xs in
  let raw = P.framed_post (N.allocated x next) pre in
  N.new_node x next;
  P.frame S.emp e (N.allocated x next) pre;
  R.entails_refl pre;
  introduce forall r. S.implies (raw r) (is_list r (x :: xs))
  with cons_intro r x next xs;
  P.consequence pre pre e raw (list_post (x :: xs))

let head_correct r x xs =
  S.sep_laws ();
  cons_unfold r x xs;
  let pre = is_list r (x :: xs) in
  let piece = next_post r x xs in
  let post = P.prepend_post pre (P.returns_value x) in
  let e = ReadData (Val r) in
  introduce forall next. P.hoare (piece next) e post
  with (
    let tail = is_list next xs in
    let raw = P.framed_post (N.data_post r x next) tail in
    N.read_data r x next;
    P.frame (N.node r x next) e (N.data_post r x next) tail;
    R.entails_refl (piece next);
    introduce forall v. S.implies (raw v) (post v)
    with (
      cons_intro r x next xs;
      R.entails_refl (S.pure (v == x));
      R.entails_star (piece next) pre (S.pure (v == x)) (S.pure (v == x))
    );
    P.consequence (piece next) (piece next) e raw post
  );
  R.exists_elim piece (P.wp e post)

let next_correct r x xs =
  S.sep_laws ();
  cons_unfold r x xs;
  let piece = next_post r x xs in
  let e = ReadNext (Val r) in
  introduce forall next. P.hoare (piece next) e piece
  with (
    let tail = is_list next xs in
    let raw = P.framed_post (N.next_post r x next) tail in
    N.read_next r x next;
    P.frame (N.node r x next) e (N.next_post r x next) tail;
    R.entails_refl (piece next);
    introduce forall v. S.implies (raw v) (piece v)
    with R.pure_elim (piece next) (piece v) (v == next)
      (fun _ -> R.entails_refl (piece next));
    P.consequence (piece next) (piece next) e raw piece
  );
  R.exists_elim piece (P.wp e piece)

let rec exposed (r:H.core_ref) (xs:list int)
  : Lemma (S.implies (P.exposed (is_list r xs)) (is_list r xs)) (decreases xs)
  =
  match xs with
  | [] -> R.exposed_pure (r == H.core_ref_null)
  | x :: tail ->
      cons_unfold r x tail;
      introduce forall next. S.implies
        (P.exposed (S.star (N.node r x next) (is_list next tail)))
        (S.star (N.node r x next) (is_list next tail))
      with (
        N.exposed r x next;
        exposed next tail;
        R.exposed_star (N.node r x next) (is_list next tail)
      );
      R.exposed_exists (next_post r x tail)
