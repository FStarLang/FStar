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
    requires no_extrude <| emp **
      (item_match (Seq.head c) (List.Tot.hd v) **
          seq_list_match (Seq.tail c) (List.Tot.tl v) item_match
      )
    ensures
      (seq_list_match c v item_match)
  {
    Seq.cons_head_tail c;
    seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match;
    rewrite each (Seq.cons (Seq.head c) (Seq.tail c)) as c;
    ()
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
  requires no_extrude <|
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
  requires no_extrude <|
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
  requires no_extrude <|
    emp ** (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match)
  ensures
    seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match
  {
    seq_list_match_append_intro item_match c1 l1 c2 l2
  };
  Trade.intro _ _ _ aux
}

open Pulse.Lib.Trade

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
    Pulse.Lib.Trade.elim_trade (p (Seq.index s1 i) (List.Tot.index s2 i)) (seq_list_match s1 s2 p);
  };
  Trade.intro _ _ _ aux;
  ()
}

ghost fn seq_seq_match_seq_list_match_trade
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (s: Seq.seq t2)
requires
    (seq_seq_match p c s 0 (Seq.length s) ** pure (
      (Seq.length c == Seq.length s)
    ))
ensures
    (seq_list_match c (Seq.seq_to_list s) p **
      Trade.trade
        (seq_list_match c (Seq.seq_to_list s) p)
        (seq_seq_match p c s 0 (Seq.length s))
    )
{
  seq_seq_match_seq_list_match p c (Seq.seq_to_list s);
  ghost fn aux (_: unit)
  requires no_extrude <| emp ** seq_list_match c (Seq.seq_to_list s) p
  ensures seq_seq_match p c s 0 (Seq.length s)
  {
    seq_list_match_seq_seq_match p c (Seq.seq_to_list s)
  };
  Trade.intro _ _ _ aux
}

ghost fn seq_list_match_seq_seq_match_trade
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
requires
    (seq_list_match c l p)
ensures
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) **
      Trade.trade
        (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
        (seq_list_match c l p)
    )
{
  seq_list_match_seq_seq_match p c l;
  ghost fn aux (_: unit)
  requires no_extrude <| emp ** seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)
  ensures seq_list_match c l p
  {
    seq_seq_match_seq_list_match p c l
  };
  Trade.intro _ _ _ aux
}

ghost fn seq_seq_match_empty_intro_trade
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
requires
  emp
ensures
  (seq_seq_match p s1 s2 i i **
    Trade.trade (seq_seq_match p s1 s2 i i) emp
  )
{
  seq_seq_match_empty_intro p s1 s2 i;
  ghost fn aux (_: unit)
  requires no_extrude <| emp ** seq_seq_match p s1 s2 i i
  ensures emp
  {
    seq_seq_match_empty_elim p s1 s2 i
  };
  Trade.intro _ _ _ aux
}

ghost fn seq_seq_match_enqueue_left_trade
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat { i > 0 /\ i <= Seq.length s1 /\ i <= Seq.length s2 })
  (j: nat)
  (x1: t1)
  (x2: t2)
requires
    (seq_seq_match p s1 s2 i j ** p x1 x2 ** pure (x1 == Seq.index s1 (i - 1) /\ x2 == Seq.index s2 (i - 1)))
ensures
    (seq_seq_match p s1 s2 (i - 1) j **
    Trade.trade
      (seq_seq_match p s1 s2 (i - 1) j)
      (seq_seq_match p s1 s2 i j ** p x1 x2)
    )
{
  seq_seq_match_length p s1 s2 i j;
  seq_seq_match_enqueue_left p s1 s2 i j x1 x2;
  ghost fn aux (_: unit)
  requires no_extrude <| emp ** seq_seq_match p s1 s2 (i - 1) j
  ensures seq_seq_match p s1 s2 i j ** p x1 x2
  {
    seq_seq_match_dequeue_left p s1 s2 (i - 1) j;
    rewrite (p (Seq.index s1 (i - 1)) (Seq.index s2 (i - 1))) as (p x1 x2);
    ()
  };
  Trade.intro _ _ _ aux
}

ghost fn seq_seq_match_enqueue_right_trade
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (j: nat { j < Seq.length s1 /\ j < Seq.length s2 })
  (x1: t1)
  (x2: t2)
requires
    (seq_seq_match p s1 s2 i j ** p x1 x2 ** pure (x1 == Seq.index s1 j /\ x2 == Seq.index s2 j))
ensures
    (seq_seq_match p s1 s2 i (j + 1) **
      Trade.trade
        (seq_seq_match p s1 s2 i (j + 1))
        (seq_seq_match p s1 s2 i j ** p x1 x2)
    )
{
  seq_seq_match_length p s1 s2 i j;
  seq_seq_match_enqueue_right p s1 s2 i j x1 x2;
  ghost fn aux (_: unit)
  requires no_extrude <| emp ** seq_seq_match p s1 s2 i (j + 1)
  ensures seq_seq_match p s1 s2 i j ** p x1 x2
  {
    seq_seq_match_dequeue_right p s1 s2 i (j + 1);
    rewrite (p (Seq.index s1 (j + 1 - 1)) (Seq.index s2 (j + 1 - 1))) as (p x1 x2)
  };
  Trade.intro _ _ _ aux
}

ghost fn seq_seq_match_rewrite_seq_trade
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
requires
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ (i == j \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j <= Seq.length c1' /\ j <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
      )))
    ))
ensures
    (seq_seq_match p c1' c2' i j **
      Trade.trade
        (seq_seq_match p c1' c2' i j)
        (seq_seq_match p c1 c2 i j)
    )
{
  seq_seq_match_rewrite_seq p c1 c1' c2 c2' i j;
  ghost fn aux (_: unit)
  requires no_extrude <| emp ** seq_seq_match p c1' c2' i j
  ensures seq_seq_match p c1 c2 i j
  {
    seq_seq_match_rewrite_seq p c1' c1 c2' c2 i j;
  };
  Trade.intro _ _ _ aux
}

ghost
fn seq_seq_match_index_trade
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j k: nat)
requires
    (seq_seq_match p s1 s2 i k ** pure (
      i <= j /\ j < k
    ))
  returns res: (squash (i <= j /\ j < k /\ k <= Seq.length s1 /\ k <= Seq.length s2))
ensures
      p (Seq.index s1 j) (Seq.index s2 j) **
      Trade.trade
        (p (Seq.index s1 j) (Seq.index s2 j))
        (seq_seq_match p s1 s2 i k)
{
  seq_seq_match_split p s1 s2 i j k;
  seq_seq_match_dequeue_left p s1 s2 j k;
  ghost fn aux (_: unit)
  requires no_extrude (seq_seq_match p s1 s2 i j ** seq_seq_match p s1 s2 (j + 1) k) ** p (Seq.index s1 j) (Seq.index s2 j)
  ensures seq_seq_match p s1 s2 i k
  {
    seq_seq_match_enqueue_left p s1 s2 (j + 1) k (Seq.index s1 j) (Seq.index s2 j);
    seq_seq_match_join p s1 s2 i j k
  };
  Trade.intro _ _ _ aux;
  ()
}
