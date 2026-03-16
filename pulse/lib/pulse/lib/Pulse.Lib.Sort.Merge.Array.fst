module Pulse.Lib.Sort.Merge.Array
#lang-pulse
open Pulse.Lib.Pervasives
include Pulse.Lib.Sort.Base
include Pulse.Lib.Sort.Merge.Spec
include Pulse.Lib.Array
open Pulse.Lib.Sort.Merge.Common

module SM = Pulse.Lib.SeqMatch.Util
module AS = Pulse.Lib.Swap.Array
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I16 = FStar.Int16

let merge_invariant_prop
    (#t: Type)
    (compare: t -> t -> int)
    (lo: SZ.t)
    (hi: SZ.t)
    (l1_0: Ghost.erased (list t))
    (l2_0: Ghost.erased (list t))
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
            )

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
        pure (merge_invariant_prop compare lo hi l1_0 l2_0 i1 i2 res accu l1 l2)

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
        lo mi true
        c1l c1 c2 [] l1_0 l2_0
    );
    while (
        unfold merge_invariant;
        let i1 = !pi1;
        let i2 = !pi2;
        let res = !pres;
        (res && not (i1 = i2 || i2 = hi))
    )
    invariant exists* i1 i2 res c c1' c2' accu l1' l2'.
        merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres i1 i2 res c c1' c2' accu l1' l2'
    {
        with gi1 gi2 gres c c1' c2' accu l1 l2 .
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gi1 gi2 gres c c1' c2' accu l1 l2);
        unfold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gi1 gi2 gres c c1' c2' accu l1 l2);
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
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres gi1 gi2 false c
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
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres i1' gi2 gres
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
            fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres i1' i2' gres
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
        fold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres i1 i2 res c c1' c2' accu l1' l2');
    unfold (merge_invariant vmatch compare a c1 c2 lo hi l1_0 l2_0 pi1 pi2 pres i1 i2 res c c1' c2' accu l1' l2');
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
