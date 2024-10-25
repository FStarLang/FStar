module Pulse.Lib.Array.MergeSort
#lang-pulse
open Pulse.Lib.Pervasives
include Pulse.Lib.Array

module SM = Pulse.Lib.SeqMatch.Util
module AS = Pulse.Lib.ArraySwap
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I16 = FStar.Int16

[@@noextract_to "krml"] noextract
let rec spec_merge
  (#t: Type)
  (compare: t -> t -> int)
  (accu: list t)
  (l1: list t)
  (l2: list t)
: Tot (bool & list t)
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  |  x1 :: l1', x2 :: l2' ->
    begin let c = compare x1 x2 in
      if c = 0
      then (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
      else if c < 0
      then spec_merge compare (accu `List.Tot.append` [x1]) l1' l2
      else
        spec_merge compare (accu `List.Tot.append` [x2]) l1 l2'
     end
  | [], _ -> (true, accu `List.Tot.append` l2)
  | _, [] -> (true, accu `List.Tot.append` l1)

let rec list_sorted_append_elim
  (#t: Type)
  (order: t -> t -> bool)
  (l1 l2: list t)
: Lemma
  (requires (List.Tot.sorted order (l1 `List.Tot.append` l2)))
  (ensures (
    List.Tot.sorted order l1 /\
    List.Tot.sorted order l2
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | [_] -> ()
  | a :: b :: q ->
    list_sorted_append_elim order (b :: q) l2

let rec list_sorted_append_chunk_intro
  (#t: Type)
  (order: t -> t -> bool)
  (l1 l2 l3: list t)
: Lemma
  (requires (
    List.Tot.sorted order (l1 `List.Tot.append` l2) /\
    List.Tot.sorted order (l2 `List.Tot.append` l3) /\
    Cons? l2
  ))
  (ensures (
    List.Tot.sorted order (l1 `List.Tot.append` (l2 `List.Tot.append` l3))
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | [a] -> () // because of List.Tot.sorted (l2 `List.Tot.append` l3) and Cons? l2
  | a :: l1' -> list_sorted_append_chunk_intro order l1' l2 l3

let rec list_index_append_r
  (#t: Type)
  (l1 l2: list t)
  (i: nat)
: Lemma
  (requires i < List.Tot.length l2)
  (ensures List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2 /\
    List.Tot.index (List.Tot.append l1 l2) (List.Tot.length l1 + i) == List.Tot.index l2 i
  )
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_index_append_r q l2 i

#push-options "--z3rlimit 16"

#restart-solver
let rec spec_merge_correct
  (#t: Type)
  (order: t -> t -> bool)
  (compare: t -> t -> int)
  (accu: list t)
  (l1: list t)
  (l2: list t)
: Lemma
  (requires (
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0)) /\
    List.Tot.sorted order (accu `List.Tot.append` l1) /\
    List.Tot.sorted order (accu `List.Tot.append` l2)
  ))
  (ensures (
    let (sorted, res) = spec_merge compare accu l1 l2 in
    List.Tot.length res == List.Tot.length accu + List.Tot.length l1 + List.Tot.length l2 /\
    (forall x . List.Tot.memP x res <==> List.Tot.memP x (accu `List.Tot.append` (l1 `List.Tot.append` l2))) /\
    (if sorted
    then List.Tot.sorted order res
    else exists x1 x2 . (List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0)
    )
  ))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  | [], _ -> List.Tot.append_length accu l2
  | _, [] -> List.Tot.append_l_nil l1; List.Tot.append_length accu l1
  | x1 :: l1', x2 :: l2' ->
    let c = compare x1 x2 in
    if c = 0
    then begin
      List.Tot.append_length l1 l2;
      List.Tot.append_length accu (List.Tot.append l1 l2)
    end
    else if c < 0
    then begin
      let accu' = accu `List.Tot.append` [x1] in
      List.Tot.append_length accu [x1];
      List.Tot.append_assoc accu l1 l2;
      List.Tot.append_assoc accu [x1] l1';
      List.Tot.append_assoc accu' l1' l2;
      List.Tot.append_assoc accu [x1] l2;
      list_sorted_append_elim order accu' l1';
      list_sorted_append_elim order accu l2;
      list_sorted_append_chunk_intro order accu [x1] l2;
      spec_merge_correct order compare accu' l1' l2
    end
    else begin
      let accu' = accu `List.Tot.append` [x2] in
      List.Tot.append_length accu [x2];
      List.Tot.append_memP_forall l1 l2;
      List.Tot.append_memP_forall accu (l1 `List.Tot.append` l2);
      List.Tot.append_memP_forall accu [x2];
      List.Tot.append_memP_forall l1 l2';
      List.Tot.append_memP_forall accu' (l1 `List.Tot.append` l2');
      List.Tot.append_assoc accu [x2] l2';
      list_sorted_append_elim order accu' l2';
      list_sorted_append_elim order accu l1;
      list_sorted_append_chunk_intro order accu [x2] l1;
      List.Tot.append_assoc accu [x2] l1;
      spec_merge_correct order compare accu' l1 l2'
    end

#pop-options

let rec list_splitAt_length
  (#t: Type)
  (n: nat)
  (l: list t)
: Lemma
  (requires (List.Tot.length l >= n))
  (ensures (
    let (l1, l2) = List.Tot.splitAt n l in
    List.Tot.length l1 == n /\
    List.Tot.length l1 + List.Tot.length l2 == List.Tot.length l
  ))
  [SMTPat (List.Tot.splitAt n l)]
= if n = 0 then () else list_splitAt_length (n - 1) (List.Tot.tl l)

let rec list_splitAt_append
  (#t: Type)
  (n: nat)
  (l: list t)
: Lemma
  (ensures (let (l1, l2) = List.Tot.splitAt n l in
    l == l1 `List.Tot.append` l2
  ))
  [SMTPat (List.Tot.splitAt n l)]
= match l with
  | [] -> ()
  | a :: q ->
    if n = 0 then () else list_splitAt_append (n - 1) q

[@@noextract_to "krml"] noextract
let rec spec_sort
  (#t: Type)
  (compare: t -> t -> int)
  (l: list t)
: Tot (bool & list t)
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then (true, l)
  else
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    let _ = list_splitAt_length (len / 2) l in
    let _ = assert (List.Tot.length l1 == len / 2) in
    let (res, l1') = spec_sort compare l1 in
    if not res
    then (false, l1' `List.Tot.append` l2)
    else
      let (res, l2') = spec_sort compare l2 in
      if not res
      then (false, l1' `List.Tot.append` l2')
      else spec_merge compare [] l1' l2'

let exists4_elim
  (#t1 #t2 #t3 #t4: Type)
  (p: t1 -> t2 -> t3 -> t4 -> prop)
  (q: prop)
  (prf: (x1: t1) -> (x2: t2) -> (x3: t3) -> (x4: t4) -> Lemma
    (requires p x1 x2 x3 x4)
    (ensures q)
  )
: Lemma
  (requires exists x1 x2 x3 x4 . p x1 x2 x3 x4)
  (ensures q)
= Classical.forall_intro_4 (fun x1 x2 x3 x4 -> Classical.move_requires (prf x1 x2 x3) x4)

#push-options "--split_queries always"

#restart-solver
let rec spec_sort_correct
  (#t: Type)
  (order: t -> t -> bool)
  (compare: t -> t -> int)
  (l: list t)
: Lemma
  (requires (
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))
  ))
  (ensures (let q = spec_sort compare l in
    let res : bool = fst q in
    let l'  = snd q in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (if res then
      List.Tot.sorted order l'
    else exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0
    ))
  )
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then ()
  else begin
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    list_splitAt_append (len / 2) l;
    List.Tot.append_length l1 l2;
    List.Tot.append_memP_forall l1 l2;
    let (res, l1') = spec_sort compare l1 in
    spec_sort_correct order compare l1;
    List.Tot.append_memP_forall l1' l2;
    if not res
    then begin
      let prf
        (l1_1 l1_2: list t)
        (x1 x2: t)
      : Lemma
        (requires (l1 == List.Tot.append l1_1 l1_2 /\ List.Tot.memP x1 l1_1 /\ List.Tot.memP x2 l1_2 /\ compare x1 x2 == 0))
        (ensures (l == List.Tot.append l1_1 (List.Tot.append l1_2 l2) /\ List.Tot.memP x1 l1_1 /\ List.Tot.memP x2 (List.Tot.append l1_2 l2) /\ compare x1 x2 == 0))
      = List.Tot.append_assoc l1_1 l1_2 l2;
        List.Tot.append_memP_forall l1_2 l2
      in
      exists4_elim (fun l1_1 l1_2 x1 x2 -> l1 == List.Tot.append l1_1 l1_2 /\ List.Tot.memP x1 l1_1 /\ List.Tot.memP x2 l1_2 /\ compare x1 x2 == 0)
        (exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0)
        (fun l1_1 l1_2 x1 x2 -> prf l1_1 l1_2 x1 x2);
      List.Tot.append_length l1' l2
    end
    else begin
      let (res, l2') = spec_sort compare l2 in
      spec_sort_correct order compare l2;
      List.Tot.append_memP_forall l1' l2';
      if not res
      then begin
        let prf
          (l2_1 l2_2: list t)
          (x1 x2: t)
        : Lemma
          (requires (l2 == List.Tot.append l2_1 l2_2 /\ List.Tot.memP x1 l2_1 /\ List.Tot.memP x2 l2_2 /\ compare x1 x2 == 0))
          (ensures (l == List.Tot.append (List.Tot.append l1 l2_1) l2_2 /\ List.Tot.memP x1 (List.Tot.append l1 l2_1) /\ List.Tot.memP x2 l2_2 /\ compare x1 x2 == 0))
        = List.Tot.append_assoc l1 l2_1 l2_2;
          List.Tot.append_memP_forall l1 l2_1
        in
        exists4_elim (fun l2_1 l2_2 x1 x2 ->  l2 == List.Tot.append l2_1 l2_2 /\ List.Tot.memP x1 l2_1 /\ List.Tot.memP x2 l2_2 /\ compare x1 x2 == 0)
          (exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0)
          (fun l1_1 l1_2 x1 x2 -> prf l1_1 l1_2 x1 x2);
        List.Tot.append_length l1' l2'
      end
      else begin
        let (res, l') = spec_merge compare [] l1' l2' in
        assert (spec_sort compare l == (res, l'));
        spec_merge_correct order compare [] l1' l2';
        assert (forall x . List.Tot.memP x l' <==> (List.Tot.memP x l1' \/ List.Tot.memP x l2'));
        assert (forall x . List.Tot.memP x l' <==> List.Tot.memP x l);
        if res
        then begin
          assert (List.Tot.sorted order l')
        end
        else ()
      end
    end
  end

#pop-options

let merge_invariant_prop
    (#t: Type)
    (compare: t -> t -> int)
    (lo: SZ.t)
    (hi: SZ.t)
    (l1_0: Ghost.erased (list t))
    (l2_0: Ghost.erased (list t))
    (cont: bool)
    i1 i2 (res: bool) accu l1 l2
: Tot prop
=
            SZ.v lo <= SZ.v i1 /\
            SZ.v i1 <= SZ.v i2 /\
            SZ.v i2 <= SZ.v hi /\
            spec_merge compare [] l1_0 l2_0 == (
                if res
                then spec_merge compare accu l1 l2
                else (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
            ) /\
            cont == (res && not (i1 = i2 || i2 = hi))

let merge_invariant // FIXME: WHY WHY WHY?
    (#tl #th: Type)
    (vmatch: tl -> th -> slprop)
    (compare: th -> th -> int)
    (a: array tl)
    (c1_0 c2_0: (Seq.seq tl))
    (lo: SZ.t)
    (hi: SZ.t)
    (l1_0: (list th))
    (l2_0: (list th))
    (pi1: R.ref SZ.t)
    (pi2: R.ref SZ.t)
    (pres: R.ref bool)
    (cont: bool)
    i1 i2 (res: bool) c c1 c2 accu l1 l2
: Tot slprop
=
        R.pts_to pi1 i1 ** R.pts_to pi2 i2 ** R.pts_to pres res **
        pts_to_range a (SZ.v lo) (SZ.v i1) c **
        SM.seq_list_match c accu vmatch **
        pts_to_range a (SZ.v i1) (SZ.v i2) c1 **
        SM.seq_list_match c1 l1 vmatch **
        pts_to_range a (SZ.v i2) (SZ.v hi) c2 **
        SM.seq_list_match c2 l2 vmatch **
        Trade.trade
          (SM.seq_list_match c accu vmatch ** (SM.seq_list_match c1 l1 vmatch ** SM.seq_list_match c2 l2 vmatch))
          (SM.seq_list_match c1_0 l1_0 vmatch ** SM.seq_list_match c2_0 l2_0 vmatch) **
        pure (merge_invariant_prop compare lo hi l1_0 l2_0 cont i1 i2 res accu l1 l2)

inline_for_extraction noextract [@@noextract_to "krml"]
let size_eq (x1 x2: SZ.t) : Tot bool = x1 = x2

//
// Solver has trouble proving these in the middle of merge
//
let seq_helper_1 (#a:Type) (s:Seq.seq a) (x:a)
  : Lemma (requires 0 < Seq.length s /\ Seq.head s == x)
          (ensures Seq.slice s 0 1 `Seq.equal` Seq.cons x Seq.empty) = ()

let seq_helper_2 (#a:Type) (s:Seq.seq a) (x:a)
  : Lemma (requires 0 < Seq.length s /\ Seq.head s == x)
          (ensures s `Seq.equal` Seq.cons x (Seq.tail s)) = ()

inline_for_extraction
let impl_compare_t
  (#tl #th: Type)
  (vmatch: tl -> th -> slprop)
  (compare: th -> th -> int)
= (x1: tl) ->
  (x2: tl) ->
  (#y1: Ghost.erased th) ->
  (#y2: Ghost.erased th) ->
  stt I16.t
    (vmatch x1 y1 ** vmatch x2 y2)
    (fun res -> vmatch x1 y1 ** vmatch x2 y2 ** pure (
      let v = compare y1 y2 in
      (v < 0 <==> I16.v res < 0) /\
      (v > 0 <==> I16.v res > 0)
    ))

ghost
fn merge_aux_consume_1
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (c: Seq.seq tl)
  (accu: list th)
  (c1: Seq.seq tl)
  (v1: list th)
  (c2: Seq.seq tl)
  (v2: list th)
  (x1: tl)
  (sq: squash (
    Cons? v1 /\
    Seq.length c1 > 0 /\
    x1 == Seq.index c1 0
  ))
requires
  SM.seq_list_match c accu vmatch **
  SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match c2 v2 vmatch
ensures
  SM.seq_list_match (Seq.append c (Seq.cons x1 Seq.empty)) (List.Tot.append accu [List.Tot.hd v1]) vmatch **
    SM.seq_list_match (Seq.tail c1) (List.Tot.tl v1) vmatch ** SM.seq_list_match c2 v2 vmatch **
  Trade.trade
    (SM.seq_list_match (Seq.append c (Seq.cons x1 Seq.empty)) (List.Tot.append accu [List.Tot.hd v1]) vmatch **
      (SM.seq_list_match (Seq.tail c1) (List.Tot.tl v1) vmatch ** SM.seq_list_match c2 v2 vmatch)
    )
    (SM.seq_list_match c accu vmatch **
      (SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match c2 v2 vmatch)
    )
{
  let _ = SM.seq_list_match_cons_elim_trade c1 v1 vmatch;
  Trade.rewrite_with_trade
    (vmatch (Seq.head c1) (List.Tot.hd v1))
    (vmatch x1 (List.Tot.hd v1));
  Trade.trans_hyp_l _ _ _ (SM.seq_list_match c1 v1 vmatch);
  SM.seq_list_match_singleton_intro_trade x1 (List.Tot.hd v1) vmatch;
  Trade.trans_hyp_l _ (vmatch x1 (List.Tot.hd v1)) _ _;
  Trade.reg_l (SM.seq_list_match c accu vmatch) _ (SM.seq_list_match c1 v1 vmatch);
  Trade.assoc_hyp_l _ _ _ (_ ** SM.seq_list_match c1 v1 vmatch);
  SM.seq_list_match_append_intro_trade vmatch c accu (Seq.cons x1 Seq.empty) [List.Tot.hd v1];
  Trade.trans_hyp_l _ _ _ (_ ** SM.seq_list_match c1 v1 vmatch);
  Trade.reg_r _ _ (SM.seq_list_match c2 v2 vmatch);
  Trade.assoc_hyp_r _ _ _ _;
  Trade.assoc_concl_l _ _ _ _;
}

ghost
fn trade_comm_hyp_intro_r
  (p q r: slprop)
requires emp
ensures
  Trade.trade (p ** (q ** r)) (p ** (r ** q))
{
  Trade.refl (q ** r);
  Trade.comm_r _ q r;
  Trade.reg_l p (q ** r) _;
}

ghost
fn merge_aux_consume_2
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (c: Seq.seq tl)
  (accu: list th)
  (c1: Seq.seq tl)
  (v1: list th)
  (c2: Seq.seq tl)
  (v2: list th)
  (x2: tl)
  (sq: squash (
    Cons? v2 /\
    Seq.length c2 > 0 /\
    x2 == Seq.index c2 0
  ))
requires
  SM.seq_list_match c accu vmatch **
    SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match c2 v2 vmatch
ensures
  SM.seq_list_match (Seq.append c (Seq.cons x2 Seq.empty)) (List.Tot.append accu [List.Tot.hd v2]) vmatch **
      SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match (Seq.tail c2) (List.Tot.tl v2) vmatch **
  Trade.trade
    (SM.seq_list_match (Seq.append c (Seq.cons x2 Seq.empty)) (List.Tot.append accu [List.Tot.hd v2]) vmatch **
      (SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match (Seq.tail c2) (List.Tot.tl v2) vmatch)
    )
    (SM.seq_list_match c accu vmatch **
      (SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match c2 v2 vmatch)
    )
{
  merge_aux_consume_1
    vmatch
    c
    accu
    c2
    v2
    c1
    v1
    x2
    ();
  trade_comm_hyp_intro_r
    (SM.seq_list_match c accu vmatch)
    (SM.seq_list_match c2 v2 vmatch)
    (SM.seq_list_match c1 v1 vmatch);
  Trade.trans _ _ 
    (SM.seq_list_match c accu vmatch **
      (SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match c2 v2 vmatch)
    );
  trade_comm_hyp_intro_r
    (SM.seq_list_match (Seq.append c (Seq.cons x2 Seq.empty)) (List.Tot.append accu [List.Tot.hd v2]) vmatch)
    (SM.seq_list_match c1 v1 vmatch)
    (SM.seq_list_match (Seq.tail c2) (List.Tot.tl v2) vmatch);
  Trade.trans _ _ 
    (SM.seq_list_match c accu vmatch **
      (SM.seq_list_match c1 v1 vmatch ** SM.seq_list_match c2 v2 vmatch)
    );
}

inline_for_extraction
fn merge
    (#tl #th: Type0)
    (vmatch: tl -> th -> slprop)
    (compare: Ghost.erased (th -> th -> int))
    (impl_compare: impl_compare_t vmatch compare)
    (a: array tl)
    (lo: SZ.t)
    (mi: SZ.t)
    (hi: SZ.t)
    (#c1: Ghost.erased (Seq.seq tl))
    (#c2: Ghost.erased (Seq.seq tl))
    (#l1_0: Ghost.erased (list th))
    (#l2_0: Ghost.erased (list th))
requires
    pts_to_range a (SZ.v lo) (SZ.v mi) c1 **
    pts_to_range a (SZ.v mi) (SZ.v hi) c2 **
    SM.seq_list_match c1 l1_0 vmatch **
    SM.seq_list_match c2 l2_0 vmatch
returns res: bool
ensures exists* c l .
    pts_to_range a (SZ.v lo) (SZ.v hi) c **
    SM.seq_list_match c l vmatch **
    Trade.trade
      (SM.seq_list_match c l vmatch)
      (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch) **
    pure (
        spec_merge compare [] l1_0 l2_0 == (res, l)
    )
{
    let mut pi1 = lo;
    pts_to_range_prop a #(SZ.v lo) #(SZ.v mi);
    pts_to_range_prop a #(SZ.v mi) #(SZ.v hi);
    pts_to_range_split a (SZ.v lo) (SZ.v lo) (SZ.v mi);
    with c1l . assert (pts_to_range a (SZ.v lo) (SZ.v lo) c1l);
    with c1r . assert (pts_to_range a (SZ.v lo) (SZ.v mi) c1r);
    assert (pure (Seq.equal c1r c1));
    rewrite (pts_to_range a (SZ.v lo) (SZ.v mi) c1r) as (pts_to_range a (SZ.v lo) (SZ.v mi) c1);
    Trade.refl (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
    SM.seq_list_match_nil_intro_trade c1l [] vmatch (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch) (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
    SM.seq_list_match_nil_intro c1l [] vmatch;
    let mut pi2 = mi;
    let mut pres = true;
    fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres
        (not (lo = mi || mi = hi))
        lo mi true
        c1l c1 c2 [] l1_0 l2_0
    );
    while (
        with gcont gi1 gi2 gres c c1' c2' accu l1' l2' .
            assert (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gcont gi1 gi2 gres c c1' c2' accu l1' l2');
        unfold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gcont gi1 gi2 gres c c1' c2' accu l1' l2');
        let i1 = !pi1;
        let i2 = !pi2;
        let res = !pres;
        let cont = (res && not (i1 = i2 || i2 = hi));
        fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres cont gi1 gi2 gres c c1' c2' accu l1' l2');
        cont
    )
    invariant cont . exists* i1 i2 res c c1' c2' accu l1' l2' .
        merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres cont i1 i2 res c c1' c2' accu l1' l2'
    {
        with gi1 gi2 gres c c1' c2' accu l1 l2 .
            assert (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres true gi1 gi2 gres c c1' c2' accu l1 l2);
        unfold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres true gi1 gi2 gres c c1' c2' accu l1 l2);
        let prf_res : squash (gres == true) = ();
        SM.seq_list_match_length vmatch c1' l1;
        SM.seq_list_match_length vmatch c2' l2;
        pts_to_range_prop a #(SZ.v gi1) #(SZ.v gi2);
        pts_to_range_prop a #(SZ.v gi2) #(SZ.v hi);
        let prf1 = SM.seq_list_match_cons_elim_trade c1' l1 vmatch;
        let prf2 = SM.seq_list_match_cons_elim_trade c2' l2 vmatch;
        let i1 = !pi1;
        rewrite (pts_to_range a (SZ.v gi1) (SZ.v gi2) c1') // FIXME: WHY WHY WHY?
            as (pts_to_range a (Ghost.reveal (SZ.v gi1)) (Ghost.reveal (SZ.v gi2)) c1');
        let x1 = pts_to_range_index a i1 #(SZ.v gi1) #(SZ.v gi2);
        let i2 = !pi2;
        rewrite (pts_to_range a (SZ.v gi2) (SZ.v hi) c2') // FIXME: WHY WHY WHY?
            as (pts_to_range a (Ghost.reveal (SZ.v gi2)) (Ghost.reveal (SZ.v hi)) c2');
        let x2 = pts_to_range_index a i2 #(SZ.v gi2) #(SZ.v hi);
        Trade.rewrite_with_trade (vmatch (Seq.head c1') (List.Tot.hd l1))
            (vmatch x1 (List.Tot.hd l1));
        Trade.trans_hyp_l (vmatch x1 (List.Tot.hd l1)) _ _ _;
        Trade.rewrite_with_trade (vmatch (Seq.head c2') (List.Tot.hd l2))
            (vmatch x2 (List.Tot.hd l2));
        Trade.trans_hyp_l (vmatch x2 (List.Tot.hd l2)) _ _ _;
        let comp = impl_compare x1 x2;
        let prf_c1': squash (c1' `Seq.equal` Seq.cons x1 (Seq.tail c1')) = ();
        let _p : squash (Seq.head c2' == x2) = ();
        let prf_c2': squash (c2' `Seq.equal` Seq.cons x2 (Seq.tail c2')) =
          seq_helper_2 c2' x2;
        Trade.elim (vmatch x1 (List.Tot.hd l1) ** _) _;
        Trade.elim (vmatch x2 (List.Tot.hd l2) ** _) _;
        if (comp = 0s) {
            pres := false;
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres false gi1 gi2 false c
                c1'
                c2'
                accu
                l1
                l2
            )
        } else if (comp `I16.lt` 0s) {
            let i1' = SZ.add i1 1sz;
            pi1 := i1';
            pts_to_range_split a (Ghost.reveal (SZ.v gi1)) (SZ.v i1') (Ghost.reveal (SZ.v gi2));
            let _p : squash (Seq.head c1' == x1) = ();
            let prf_c1' : squash (Seq.slice c1' 0 1 `Seq.equal` Seq.cons x1 Seq.empty) =
              seq_helper_1 c1' x1;
            rewrite (pts_to_range a (Ghost.reveal (SZ.v gi1)) (SZ.v i1') (Seq.slice c1' 0 (SZ.v i1' - SZ.v gi1)))
                as (pts_to_range a (SZ.v gi1) (SZ.v i1') (Seq.cons x1 Seq.empty));
            pts_to_range_join a (SZ.v lo) (SZ.v gi1) (SZ.v i1');
            merge_aux_consume_1 vmatch c accu c1' l1 c2' l2 x1 ();
            Trade.trans _ _ (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
            rewrite (pts_to_range a (Ghost.reveal (SZ.v gi2)) (Ghost.reveal (SZ.v hi)) c2')
                as (pts_to_range a (SZ.v gi2) (SZ.v hi) c2');
            rewrite (pts_to_range a (SZ.v i1') (Ghost.reveal (SZ.v gi2)) (Seq.tail c1'))
                as (pts_to_range a (SZ.v i1') (SZ.v gi2) (Seq.tail c1'));
            let gcont' = Ghost.hide (gres && not (i1' `size_eq` gi2 || gi2 `size_eq` hi));
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gcont' i1' gi2 gres
                (Seq.append c (Seq.cons x1 Seq.empty))
                (Seq.tail c1')
                c2'
                (accu `List.Tot.append` [List.Tot.hd l1])
                (List.Tot.tl l1)
                l2
            )
        } else {
            let i2' = SZ.add i2 1sz;
            rewrite (pts_to_range a (Ghost.reveal (SZ.v gi1)) (Ghost.reveal (SZ.v gi2)) c1')
                as (pts_to_range a (SZ.v i1) (SZ.v i2) (Seq.cons x1 (Seq.tail c1')));
            let prf_c2' : squash (Seq.slice c2' 0 1 `Seq.equal` Seq.cons x2 Seq.empty) = seq_helper_1 c2' x2;
            pts_to_range_split a (Ghost.reveal (SZ.v gi2)) (SZ.v i2') (Ghost.reveal (SZ.v hi));
            rewrite (pts_to_range a (Ghost.reveal (SZ.v gi2)) (SZ.v i2') (Seq.slice c2' 0 1))
                as (pts_to_range a (SZ.v i2) (SZ.v i2') (Seq.cons x2 Seq.empty));
            rewrite (pts_to_range a (SZ.v i2') (Ghost.reveal (SZ.v hi)) (Seq.tail c2'))
                as (pts_to_range a (SZ.v i2') (SZ.v hi) (Seq.tail c2'));
            let i1' = AS.array_swap a i1 i2' i2;
            rewrite (pts_to_range a (SZ.v lo) (SZ.v gi1) c)
                as (pts_to_range a (SZ.v lo) (SZ.v i1) c);
            pts_to_range_join a (SZ.v lo) (SZ.v i1) (SZ.v i1');
            pi1 := i1';
            pi2 := i2';
            merge_aux_consume_2 vmatch c accu c1' l1 c2' l2 x2 ();
            Trade.trans _ _ (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
            let gcont' = Ghost.hide (gres && not (i1' `size_eq` i2' || i2' `size_eq` hi));
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gcont' i1' i2' gres
                (Seq.append c (Seq.cons x2 Seq.empty))
                c1'
                (Seq.tail c2')
                (accu `List.Tot.append` [List.Tot.hd l2])
                l1
                (List.Tot.tl l2)
            )
        }
    };
    with i1 i2 res c c1' c2' accu l1' l2' .
        assert (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres false i1 i2 res c c1' c2' accu l1' l2');
    unfold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres false i1 i2 res c c1' c2' accu l1' l2');
    SM.seq_list_match_length vmatch c1' l1';
    SM.seq_list_match_length vmatch c2' l2';
    List.Tot.append_l_nil l1';
    pts_to_range_prop a #(SZ.v i1) #(SZ.v i2);
    pts_to_range_prop a #(SZ.v i2) #(SZ.v hi);
    pts_to_range_join a (SZ.v i1) (SZ.v i2) (SZ.v hi);
    SM.seq_list_match_append_intro_trade vmatch c1' l1' c2' l2';
    Trade.trans_hyp_r (SM.seq_list_match c accu vmatch) (SM.seq_list_match (Seq.append c1' c2') (List.Tot.append l1' l2') vmatch) (SM.seq_list_match c1' l1' vmatch ** SM.seq_list_match c2' l2' vmatch) _;
    pts_to_range_join a (SZ.v lo) (SZ.v i1) (SZ.v hi);
    SM.seq_list_match_append_intro_trade vmatch c accu (c1' `Seq.append` c2') (l1' `List.Tot.append` l2');
    Trade.trans _ _ (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
    !pres
}

let sort_aux_post
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: th -> th -> int)
    (a: array tl)
    (lo: SZ.t)
    (hi: SZ.t)
    (c: Seq.seq tl)
    (l: list th)
    (res: bool)
: Tot slprop
= exists* (c': Seq.seq tl) (l': list th).
    pts_to_range a (SZ.v lo) (SZ.v hi) c' **
    SM.seq_list_match c' l' vmatch **
    Trade.trade
      (SM.seq_list_match c' l' vmatch)
      (SM.seq_list_match c l vmatch) **
    pure (
        spec_sort compare l == (res, l')
    )

inline_for_extraction
let sort_aux_t
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: th -> th -> int)
=
    (a: array tl) ->
    (lo: SZ.t) ->
    (hi: SZ.t) ->
    (#c: Ghost.erased (Seq.seq tl)) ->
    (#l: Ghost.erased (list th)) ->
stt bool
  (
    pts_to_range a (SZ.v lo) (SZ.v hi) c **
    SM.seq_list_match c l vmatch
  )
  (fun res -> sort_aux_post vmatch compare a lo hi c l res)

inline_for_extraction
fn sort_aux
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: impl_compare_t #tl #th vmatch compare)
  (sort_aux: sort_aux_t #tl #th vmatch compare)
: sort_aux_t #tl #th vmatch compare
= 
    (a: array tl)
    (lo: SZ.t)
    (hi: SZ.t)
    (#c: Ghost.erased (Seq.seq tl))
    (#l: Ghost.erased (list th))
{
    pts_to_range_prop a;
    SM.seq_list_match_length vmatch c l;
    let len = hi `SZ.sub` lo;
    if (len `SZ.lt` 2sz) {
        Trade.refl (SM.seq_list_match c l vmatch);
        fold (sort_aux_post vmatch compare a lo hi c l true);
        true
    } else {
        let len_half = len `SZ.div` 2sz;
        let mi = lo `SZ.add` len_half;
        pts_to_range_split a (SZ.v lo) (SZ.v mi) (SZ.v hi);
        with c1 . assert (pts_to_range a (SZ.v lo) (SZ.v mi) c1);
        with c2 . assert (pts_to_range a (SZ.v mi) (SZ.v hi) c2);
        let l1l2 = Ghost.hide (List.Tot.splitAt (SZ.v len_half) l);
        let l1 = Ghost.hide (fst l1l2);
        let l2 = Ghost.hide (snd l1l2);
        Trade.rewrite_with_trade (SM.seq_list_match c l vmatch)
          (SM.seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) vmatch);
        SM.seq_list_match_append_elim_trade vmatch c1 l1 c2 l2;
        Trade.trans _ _ (SM.seq_list_match c l vmatch);
        let res = sort_aux a lo mi;
        unfold (sort_aux_post vmatch compare a lo mi c1 l1);
        with c1' l1' . assert (pts_to_range a (SZ.v lo) (SZ.v mi) c1' ** SM.seq_list_match c1' l1' vmatch);
        Trade.trans_hyp_l (SM.seq_list_match c1' l1' vmatch) (SM.seq_list_match c1 l1 vmatch) (SM.seq_list_match c2 l2 vmatch) (SM.seq_list_match c l vmatch);
        if (not res) {
            pts_to_range_join a (SZ.v lo) (SZ.v mi) (SZ.v hi);
            SM.seq_list_match_append_intro_trade vmatch c1' l1' c2 l2;
            Trade.trans _ _ (SM.seq_list_match c l vmatch);
            fold (sort_aux_post vmatch compare a lo hi c l false);
            false
        } else {
            let res = sort_aux a mi hi;
            unfold (sort_aux_post vmatch compare a mi hi c2 l2);
            with c2' l2' . assert (pts_to_range a (SZ.v mi) (SZ.v hi) c2' ** SM.seq_list_match c2' l2' vmatch);
            Trade.trans_hyp_r (SM.seq_list_match c1' l1' vmatch) (SM.seq_list_match c2' l2' vmatch) (SM.seq_list_match c2 l2 vmatch) (SM.seq_list_match c l vmatch);
            if (not res) {
                pts_to_range_join a (SZ.v lo) (SZ.v mi) (SZ.v hi);
                SM.seq_list_match_append_intro_trade vmatch c1' l1' c2' l2';
                Trade.trans _ _ (SM.seq_list_match c l vmatch);
                fold (sort_aux_post vmatch compare a lo hi c l false);
                false
            } else {
                let res = merge vmatch compare impl_compare a lo mi hi;
                Trade.trans _ _ (SM.seq_list_match c l vmatch);
                fold (sort_aux_post vmatch compare a lo hi c l res);
                res
            }
        }
    }
}

inline_for_extraction
let sort_t
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: (th -> th -> int))
=
    (a: array tl) ->
    (len: SZ.t) ->
    (#c: Ghost.erased (Seq.seq tl)) ->
    (#l: Ghost.erased (list th)) ->
    stt bool
    (pts_to a c **
      SM.seq_list_match c l vmatch **
      pure (SZ.v len == length a \/ SZ.v len == Seq.length c \/ SZ.v len == List.Tot.length l)
    )
    (fun res -> exists* c' l' .
      pts_to a c' **
      SM.seq_list_match c' l' vmatch **
      Trade.trade
        (SM.seq_list_match c' l' vmatch)
        (SM.seq_list_match c l vmatch) **
      pure (
           spec_sort compare l == (res, l')
      )
    )

inline_for_extraction
fn sort
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: Ghost.erased (th -> th -> int))
  (sort_aux: sort_aux_t #tl #th vmatch compare)
: sort_t #_ #_ vmatch compare
=
    (a: array tl)
    (len: SZ.t)
    (#c: Ghost.erased (Seq.seq tl))
    (#l: Ghost.erased (list th))
{
    pts_to_len a;
    SM.seq_list_match_length vmatch c l;
    pts_to_range_intro a 1.0R c;
    rewrite (pts_to_range a 0 (length a) c)
      as (pts_to_range a (SZ.v 0sz) (SZ.v len) c);
    let res = sort_aux a 0sz len;
    unfold (sort_aux_post vmatch compare a 0sz len c l res);
    with c' . assert (pts_to_range a (SZ.v 0sz) (SZ.v len) c');
    rewrite (pts_to_range a (SZ.v 0sz) (SZ.v len) c')
        as (pts_to_range a 0 (length a) c');
    pts_to_range_elim a 1.0R c';
    res
}
