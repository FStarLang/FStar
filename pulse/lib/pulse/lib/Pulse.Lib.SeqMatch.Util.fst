module Pulse.Lib.SeqMatch.Util
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade
include Pulse.Lib.SeqMatch
module Trade = Pulse.Lib.Trade.Util

ghost
fn seq_list_match_nil_elim_trade
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
  (p q: slprop)
requires
    Trade.trade
      (seq_list_match c v item_match ** p)
      q **
    pure (
      c `Seq.equal` Seq.empty /\
      Nil? v
    )
ensures
    Trade.trade p q
{
  seq_list_match_nil_intro c v item_match;
  Trade.elim_hyp_l _ p q
}

ghost
fn seq_list_match_nil_intro_trade
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
  (p q: slprop)
requires
    Trade.trade p q **
    pure (
      c `Seq.equal` Seq.empty /\
      Nil? v
    )
ensures
    Trade.trade (seq_list_match c v item_match ** p) q
{
  ghost
  fn aux (_: unit)
  requires
    Trade.trade p q ** (seq_list_match c v item_match ** p)
  ensures
    q
  {
    seq_list_match_nil_elim c v item_match;
    Trade.elim _ _;
  };
  Trade.intro _ _ _ aux
}

ghost
fn seq_list_match_cons_elim_trade
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t' { Cons? v \/ Seq.length c > 0 })
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
requires
    (seq_list_match c v item_match)
returns res: (squash (Cons? v /\ Seq.length c > 0))
ensures
    (item_match (Seq.head c) (List.Tot.hd v) **
      seq_list_match (Seq.tail c) (List.Tot.tl v) item_match **
      trade
        (item_match (Seq.head c) (List.Tot.hd v) **
          seq_list_match (Seq.tail c) (List.Tot.tl v) item_match
        )
        (seq_list_match c v item_match)
    )
{
  seq_list_match_cons_elim c v item_match;
  ghost
  fn aux ()
    requires emp **
      (item_match (Seq.head c) (List.Tot.hd v) **
          seq_list_match (Seq.tail c) (List.Tot.tl v) item_match
      )
    ensures
      (seq_list_match c v item_match)
  {
    Seq.cons_head_tail c;
    seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match
  };
  Trade.intro _ _ _ aux;
  ()
}

ghost
fn seq_list_match_cons_intro_trade
  (#t #t': Type0)
  (a: t)
  (a' : t')
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << a' :: v }) -> slprop))
requires
    (item_match a a' ** seq_list_match c v item_match)
ensures
    (seq_list_match (Seq.cons a c) (a' :: v) item_match **
      Trade.trade
        (seq_list_match (Seq.cons a c) (a' :: v) item_match)
        (item_match a a' ** seq_list_match c v item_match)
    )
{
  seq_list_match_cons_intro a a' c v item_match;
  ghost fn aux (_: unit)
  requires
    emp ** seq_list_match (Seq.cons a c) (a' :: v) item_match
  ensures
    item_match a a' ** seq_list_match c v item_match
  {
    let _ = seq_list_match_cons_elim (Seq.cons a c) (a' :: v) item_match;
    rewrite (item_match (Seq.head (Seq.cons a c)) (List.Tot.hd (a' :: v))) as (item_match a a');
    Seq.lemma_tl a c;
    rewrite (seq_list_match (Seq.tail (Seq.cons a c)) (List.Tot.tl (a' :: v)) item_match) as (seq_list_match c v item_match)
  };
  Trade.intro _ _ _ aux
}

ghost
fn seq_list_match_singleton_intro_trade
  (#t #t': Type0)
  (a: t)
  (a': t')
  (item_match: (t -> (v': t' { v' << [a'] }) -> slprop))
requires
  item_match a a'
ensures
  seq_list_match (Seq.cons a Seq.empty) [a'] item_match **
  Trade.trade
    (seq_list_match (Seq.cons a Seq.empty) [a'] item_match)
    (item_match a a')
{
  seq_list_match_nil_intro Seq.empty [] item_match;
  seq_list_match_cons_intro_trade a a' Seq.empty [] item_match;
  ghost fn aux (_: unit)
  requires
    Trade.trade
      (seq_list_match (Seq.cons a Seq.empty) [a'] item_match)
      (item_match a a' ** seq_list_match Seq.empty [] item_match) **
    seq_list_match (Seq.cons a Seq.empty) [a'] item_match
  ensures
    item_match a a'
  {
    Trade.elim _ _;
    seq_list_match_nil_elim Seq.empty [] item_match
  };
  Trade.intro _ _ _ aux
}

ghost
fn
seq_list_match_append_intro_trade
  (#t #t': Type0) // FIXME: universe polymorphism
  (item_match: (t -> t' -> slprop))
  (c1: Seq.seq t)
  (l1: list t')
  (c2: Seq.seq t)
  (l2: list t')
requires
    (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match)
ensures
    seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match **
    Trade.trade
      (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match)
      (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match)
{
  seq_list_match_length item_match c1 l1;
  seq_list_match_append_intro item_match c1 l1 c2 l2;
  ghost fn aux (_: unit)
  requires
    emp ** seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match
  ensures
    seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match
  {
    seq_list_match_append_elim item_match c1 l1 c2 l2
  };
  Trade.intro _ _ _ aux
}

ghost
fn seq_list_match_append_elim_trade
  (#t #t': Type0) // FIXME: universe polymorphism
  (item_match: (t -> t' -> slprop))
  (c1: Seq.seq t)
  (l1: list t')
  (c2: Seq.seq t)
  (l2: list t')
requires
    (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match **
    pure (Seq.length c1 == List.Tot.length l1 \/
      Seq.length c2 == List.Tot.length l2))
ensures
    seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match **
    Trade.trade
      (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match)
      (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match) **
    pure (
      Seq.length c1 == List.Tot.length l1 /\
      Seq.length c2 == List.Tot.length l2
    )
{
  seq_list_match_append_elim item_match c1 l1 c2 l2;
  ghost fn aux (_: unit)
  requires
    emp ** (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match)
  ensures
    seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match
  {
    seq_list_match_append_intro item_match c1 l1 c2 l2
  };
  Trade.intro _ _ _ aux
}

open Pulse.Lib.Stick

ghost
fn seq_list_match_index_trade
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: list t2)
  (i: nat)
requires
    (seq_list_match s1 s2 p ** pure (
      (i < Seq.length s1 \/ i < List.Tot.length s2)
    ))
returns res: (squash (i < Seq.length s1 /\ List.Tot.length s2 == Seq.length s1))
ensures
    (
      p (Seq.index s1 i) (List.Tot.index s2 i) **
      (p (Seq.index s1 i) (List.Tot.index s2 i) `Trade.trade`
        seq_list_match s1 s2 p)
    )
{
  seq_list_match_index p s1 s2 i;
  ghost fn aux (_: unit)
  requires
    (p (Seq.index s1 i) (List.Tot.index s2 i) @==>
      (seq_list_match s1 s2 p)) **
    p (Seq.index s1 i) (List.Tot.index s2 i)
  ensures
    seq_list_match s1 s2 p
  {
    Pulse.Lib.Stick.elim_stick (p (Seq.index s1 i) (List.Tot.index s2 i)) (seq_list_match s1 s2 p);
  };
  Trade.intro _ _ _ aux;
  ()
}
