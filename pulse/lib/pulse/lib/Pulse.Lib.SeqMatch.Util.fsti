module Pulse.Lib.SeqMatch.Util

#lang-pulse
open Pulse
open Pulse.Lib.Trade
module Trade = Pulse.Lib.Trade.Util
include Pulse.Lib.SeqMatch
open Pulse.Lib.Trade

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
