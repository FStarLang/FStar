module Pulse.Lib.Sort.Merge.Common
#lang-pulse
open Pulse.Lib.Pervasives

module SM = Pulse.Lib.SeqMatch.Util
module SZ = FStar.SizeT
module Trade = Pulse.Lib.Trade.Util

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
