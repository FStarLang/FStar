module Pulse.Lib.Sort.Merge.Slice
#lang-pulse
open Pulse.Lib.Pervasives
include Pulse.Lib.Sort.Base
include Pulse.Lib.Sort.Merge.Spec
include Pulse.Lib.Slice.Util
open Pulse.Lib.Sort.Merge.Common

module SM = Pulse.Lib.SeqMatch.Util
module S = Pulse.Lib.Slice.Util
module AS = Pulse.Lib.Swap.Slice
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module Trade = Pulse.Lib.Trade.Util
module I16 = FStar.Int16

let merge_invariant_prop
    (#t: Type)
    (compare: t -> t -> int)
    (len: SZ.t)
    (l1_0: Ghost.erased (list t))
    (l2_0: Ghost.erased (list t))
    (cont: bool)
    i1 i2 (res: bool) accu l1 l2
: Tot prop
=
            SZ.v i1 <= SZ.v i2 /\
            SZ.v i2 <= SZ.v len /\
            SZ.v i1 == List.Tot.length accu /\
            SZ.v i2 - SZ.v i1 == List.Tot.length l1 /\
            SZ.v len - SZ.v i2 == List.Tot.length l2 /\
            spec_merge compare [] l1_0 l2_0 == (
                if res
                then spec_merge compare accu l1 l2
                else (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
            ) /\
            cont == (res && not (i1 = i2 || i2 = len))

let merge_invariant
    (#tl #th: Type)
    (vmatch: tl -> th -> slprop)
    (compare: th -> th -> int)
    (a: slice tl)
    (c1_0 c2_0: (Seq.seq tl))
    (l1_0: (list th))
    (l2_0: (list th))
    (pi1: R.ref SZ.t)
    (pi2: R.ref SZ.t)
    (pres: R.ref bool)
    (cont: bool)
    i1 i2 (res: bool) c c1 c2 accu l1 l2
: Tot slprop
= exists* ca .
        R.pts_to pi1 i1 ** R.pts_to pi2 i2 ** R.pts_to pres res **
        pts_to a ca **
        SM.seq_list_match c accu vmatch **
        SM.seq_list_match c1 l1 vmatch **
        SM.seq_list_match c2 l2 vmatch **
        Trade.trade
          (SM.seq_list_match c accu vmatch ** (SM.seq_list_match c1 l1 vmatch ** SM.seq_list_match c2 l2 vmatch))
          (SM.seq_list_match c1_0 l1_0 vmatch ** SM.seq_list_match c2_0 l2_0 vmatch) **
        pure (ca == (Seq.append c (Seq.append c1 c2))) **
        pure (merge_invariant_prop compare (S.len a) l1_0 l2_0 cont i1 i2 res accu l1 l2)

let merge_case_1
  (#t: Type)
  (c: Seq.seq t)
  (x1: t)
  (c1' c2': Seq.seq t)
: Lemma
  (requires Seq.length c1' > 0 /\ x1 == Seq.head c1')
  (ensures (
    Seq.append c (Seq.append c1' c2') `Seq.equal` Seq.append (Seq.append c (Seq.cons x1 Seq.empty)) (Seq.append (Seq.tail c1') c2')
  ))
= ()

let merge_case_2_pre
  (#t: Type)
  (c c1': Seq.seq t)
  (x2: t)
  (c2': Seq.seq t)
: Lemma
  (requires Seq.length c2' > 0 /\ x2 == Seq.head c2')
  (ensures (
    Seq.append c (Seq.append c1' c2') `Seq.equal` Seq.append (Seq.append c (Seq.append c1' (Seq.cons x2 Seq.empty))) (Seq.tail c2')
  ))
= ()

let merge_case_2_post
  (#t: Type)
  (c c1': Seq.seq t)
  (x2: t)
  (c2': Seq.seq t)
: Lemma
  (requires Seq.length c2' > 0 /\ x2 == Seq.head c2')
  (ensures (
    Seq.append (Seq.append c (Seq.cons x2 Seq.empty)) (Seq.append c1' (Seq.tail c2')) `Seq.equal` Seq.append (Seq.append c (Seq.append (Seq.cons x2 Seq.empty) c1')) (Seq.tail c2')  
  ))
= ()

inline_for_extraction
fn merge
    (#tl #th: Type0)
    (vmatch: tl -> th -> slprop)
    (compare: Ghost.erased (th -> th -> int))
    (impl_compare: impl_compare_t vmatch compare)
    (a: S.slice tl)
    (mi: SZ.t)
    (c1: Ghost.erased (Seq.seq tl))
    (c2: Ghost.erased (Seq.seq tl))
    (#l1_0: Ghost.erased (list th))
    (#l2_0: Ghost.erased (list th))
requires
    pts_to a (Seq.append c1 c2) **
    SM.seq_list_match c1 l1_0 vmatch **
    SM.seq_list_match c2 l2_0 vmatch **
    pure (SZ.v mi == Seq.length c1)
  returns res: bool
  ensures exists* c l .
    pts_to a c **
    SM.seq_list_match c l vmatch **
    Trade.trade
      (SM.seq_list_match c l vmatch)
      (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch) **
    pure (
        spec_merge compare [] l1_0 l2_0 == (res, l) /\
        List.Tot.length l == List.Tot.length l1_0 + List.Tot.length l2_0
    )
{
    S.pts_to_len a;
    let mut pi1 = 0sz;
    SM.seq_list_match_length vmatch c1 l1_0;
    SM.seq_list_match_length vmatch c2 l2_0;
    Seq.append_empty_l (Seq.append c1 c2);
    rewrite (pts_to a (Seq.append c1 c2)) as (pts_to a (Seq.append Seq.empty (Seq.append c1 c2)));
    Trade.refl (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
    SM.seq_list_match_nil_intro_trade Seq.empty [] vmatch (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch) (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
    SM.seq_list_match_nil_intro Seq.empty [] vmatch;
    let mut pi2 = mi;
    let mut pres = true;
    fold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres
        (not (0sz = mi || mi = S.len a))
        0sz mi true
        Seq.empty c1 c2 [] l1_0 l2_0
    );
    while (
        with gcont gi1 gi2 gres c c1' c2' accu l1' l2' .
            assert (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres gcont gi1 gi2 gres c c1' c2' accu l1' l2');
        unfold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres gcont gi1 gi2 gres c c1' c2' accu l1' l2');
        let i1 = !pi1;
        let i2 = !pi2;
        let res = !pres;
        let cont = (res && not (i1 = i2 || i2 = S.len a));
        fold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres cont gi1 gi2 gres c c1' c2' accu l1' l2');
        cont
    )
    invariant cont . exists* i1 i2 res c c1' c2' accu l1' l2' .
        merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres cont i1 i2 res c c1' c2' accu l1' l2'
    {
        with gi1 gi2 gres c c1' c2' accu l1 l2 .
            assert (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres true gi1 gi2 gres c c1' c2' accu l1 l2);
        unfold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres true gi1 gi2 gres c c1' c2' accu l1 l2);
        let prf_res : squash (gres == true) = ();
        S.pts_to_len a;
        SM.seq_list_match_length vmatch c accu;
        SM.seq_list_match_length vmatch c1' l1;
        SM.seq_list_match_length vmatch c2' l2;
        let prf1 = SM.seq_list_match_cons_elim_trade c1' l1 vmatch;
        let prf2 = SM.seq_list_match_cons_elim_trade c2' l2 vmatch;
        let i1 = !pi1;
        let x1 = S.op_Array_Access a i1;
        let i2 = !pi2;
        let x2 = S.op_Array_Access a i2;
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
            fold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 (* pc pc1 pc2 *) pi1 pi2 pres false gi1 gi2 false c
                c1'
                c2'
                accu
                l1
                l2
            )
        }
        else if (comp `I16.lt` 0s) {
            let i1' = SZ.add i1 1sz;
            pi1 := i1';
            let _p : squash (Seq.head c1' == x1) = ();
            let prf_c1' : squash (Seq.slice c1' 0 1 `Seq.equal` Seq.cons x1 Seq.empty) =
              seq_helper_1 c1' x1;
            merge_aux_consume_1 vmatch c accu c1' l1 c2' l2 x1 ();
            Trade.trans _ _ (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
            let gcont' = Ghost.hide (gres && not (i1' `size_eq` gi2 || gi2 `size_eq` S.len a));
            List.Tot.append_assoc accu l1 l2;
            List.Tot.append_assoc accu [List.Tot.hd l1] (List.Tot.tl l1);
            List.Tot.append_assoc (List.Tot.append accu [List.Tot.hd l1]) (List.Tot.tl l1) l2;
            merge_case_1 c x1 c1' c2';
            fold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres gcont' i1' gi2 gres
                (Seq.append c (Seq.cons x1 Seq.empty))
                (Seq.tail c1')
                c2'
                (accu `List.Tot.append` [List.Tot.hd l1])
                (List.Tot.tl l1)
                l2
            )
        } else {
            let i2' = SZ.add i2 1sz;
            let prf_c2' : squash (Seq.slice c2' 0 1 `Seq.equal` Seq.cons x2 Seq.empty) = seq_helper_1 c2' x2;
            merge_case_2_pre c c1' x2 c2';
            let ac01, ac2 = S.append_split a i2' #(Seq.append c (Seq.append c1' (Seq.cons x2 Seq.empty))) #(Seq.tail c2');
            let ac, ac1 = S.append_split ac01 i1 #c #(Seq.append c1' (Seq.cons x2 Seq.empty));
            AS.slice_swap' ac1 (SZ.sub i2 i1) c1' (Seq.cons x2 Seq.empty);
            S.join ac ac1 ac01;
            S.join ac01 ac2 a;
            merge_case_2_post c c1' x2 c2';
            let i1' = SZ.add i1 1sz;
            pi1 := i1';
            pi2 := i2';
            merge_aux_consume_2 vmatch c accu c1' l1 c2' l2 x2 ();
            Trade.trans _ _ (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
            let gcont' = Ghost.hide (gres && not (i1' `size_eq` i2' || i2' `size_eq` S.len a));
            List.Tot.append_assoc l1 [List.Tot.hd l2] (List.Tot.tl l2);
            List.Tot.append_assoc accu (List.Tot.append l1 [List.Tot.hd l2]) (List.Tot.tl l2);
            List.Tot.append_assoc accu l1 [List.Tot.hd l2];
            List.Tot.append_assoc accu [List.Tot.hd l2] l1;
            List.Tot.append_assoc (List.Tot.append accu [List.Tot.hd l2]) l1 (List.Tot.tl l2);
            fold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres gcont' i1' i2' gres
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
        assert (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres false i1 i2 res c c1' c2' accu l1' l2');
    unfold (merge_invariant vmatch compare a c1 c2 l1_0 l2_0 pi1 pi2 pres false i1 i2 res c c1' c2' accu l1' l2');
    SM.seq_list_match_append_intro_trade vmatch c1' l1' c2' l2';
    List.Tot.append_length l1' l2';
    Trade.trans_hyp_r (SM.seq_list_match c accu vmatch) (SM.seq_list_match (Seq.append c1' c2') (List.Tot.append l1' l2') vmatch) (SM.seq_list_match c1' l1' vmatch ** SM.seq_list_match c2' l2' vmatch) _;
    SM.seq_list_match_append_intro_trade vmatch c accu (c1' `Seq.append` c2') (l1' `List.Tot.append` l2');
    List.Tot.append_length accu (List.Tot.append l1' l2');
    Trade.trans _ _ (SM.seq_list_match c1 l1_0 vmatch ** SM.seq_list_match c2 l2_0 vmatch);
    with va. assert pts_to a va; rewrite each Seq.Base.append c (Seq.Base.append c1' c2') as va;
    !pres
}

let sort_aux_post
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: th -> th -> int)
    (a: S.slice tl)
    (c: Seq.seq tl)
    (l: list th)
    (res: bool)
: Tot slprop
= exists* (c': Seq.seq tl) (l': list th).
    pts_to a c' **
    SM.seq_list_match c' l' vmatch **
    Trade.trade
      (SM.seq_list_match c' l' vmatch)
      (SM.seq_list_match c l vmatch) **
    pure (
        spec_sort compare l == (res, l') /\
        List.Tot.length l' == List.Tot.length l
    )

inline_for_extraction
let sort_aux_t
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: th -> th -> int)
=
    (a: S.slice tl) ->
    (#c: Ghost.erased (Seq.seq tl)) ->
    (#l: Ghost.erased (list th)) ->
stt bool
  (
    pts_to a c **
    SM.seq_list_match c l vmatch
  )
  (fun res -> sort_aux_post vmatch compare a c l res)

inline_for_extraction
fn sort_aux
  (#tl #th: Type0)
  (vmatch: tl -> th -> slprop)
  (compare: Ghost.erased (th -> th -> int))
  (impl_compare: impl_compare_t #tl #th vmatch compare)
  (sort_aux: sort_aux_t #tl #th vmatch compare)
: sort_aux_t #tl #th vmatch compare
= 
    (a: S.slice tl)
    (#c: Ghost.erased (Seq.seq tl))
    (#l: Ghost.erased (list th))
{
    S.pts_to_len a;
    SM.seq_list_match_length vmatch c l;
    let len = S.len a;
    if (len `SZ.lt` 2sz) {
        Trade.refl (SM.seq_list_match c l vmatch);
        fold (sort_aux_post vmatch compare a c l true);
        true
    } else {
        let len_half = len `SZ.div` 2sz;
        let mi = len_half;
        let a1, a2 = S.split a mi;
        Seq.lemma_split c (SZ.v mi);
        with c1 . assert (pts_to a1 c1);
        with c2 . assert (pts_to a2 c2);
        let l1l2 = Ghost.hide (List.Tot.splitAt (SZ.v len_half) l);
        let l1 = Ghost.hide (fst l1l2);
        let l2 = Ghost.hide (snd l1l2);
        Trade.rewrite_with_trade (SM.seq_list_match c l vmatch)
          (SM.seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) vmatch);
        SM.seq_list_match_append_elim_trade vmatch c1 l1 c2 l2;
        Trade.trans _ _ (SM.seq_list_match c l vmatch);
        let res = sort_aux a1;
        unfold (sort_aux_post vmatch compare a1 c1 l1);
        with c1' l1' . assert (pts_to a1 c1' ** SM.seq_list_match c1' l1' vmatch);
        SM.seq_list_match_length vmatch c1' l1';
        Trade.trans_hyp_l (SM.seq_list_match c1' l1' vmatch) (SM.seq_list_match c1 l1 vmatch) (SM.seq_list_match c2 l2 vmatch) (SM.seq_list_match c l vmatch);
        if (not res) {
            S.join a1 a2 a;
            SM.seq_list_match_append_intro_trade vmatch c1' l1' c2 l2;
            Trade.trans _ _ (SM.seq_list_match c l vmatch);
            List.Tot.append_length l1'  l2;
            fold (sort_aux_post vmatch compare a c l false);
            false
        } else {
            let res = sort_aux a2;
            unfold (sort_aux_post vmatch compare a2 c2 l2);
            with c2' l2' . assert (pts_to a2 c2' ** SM.seq_list_match c2' l2' vmatch);
            SM.seq_list_match_length vmatch c2' l2';
            Trade.trans_hyp_r (SM.seq_list_match c1' l1' vmatch) (SM.seq_list_match c2' l2' vmatch) (SM.seq_list_match c2 l2 vmatch) (SM.seq_list_match c l vmatch);
            S.join a1 a2 a;
            List.Tot.append_length l1'  l2';
           if (not res) {
                SM.seq_list_match_append_intro_trade vmatch c1' l1' c2' l2';
                Trade.trans _ _ (SM.seq_list_match c l vmatch);
                fold (sort_aux_post vmatch compare a c l false);
                false
            } else {
                let res = merge vmatch compare impl_compare a mi c1' c2';
                Trade.trans _ _ (SM.seq_list_match c l vmatch);
                SM.seq_list_match_length vmatch _ _;
                fold (sort_aux_post vmatch compare a c l res);
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
    (a: S.slice tl) ->
    (#c: Ghost.erased (Seq.seq tl)) ->
    (#l: Ghost.erased (list th)) ->
    stt bool
    (pts_to a c **
      SM.seq_list_match c l vmatch
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
    (a: S.slice tl)
    (#c: Ghost.erased (Seq.seq tl))
    (#l: Ghost.erased (list th))
{
    S.pts_to_len a;
    SM.seq_list_match_length vmatch c l;
    let res = sort_aux a;
    unfold (sort_aux_post vmatch compare a c l res);
    res
}
