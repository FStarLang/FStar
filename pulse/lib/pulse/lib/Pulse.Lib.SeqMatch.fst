(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.SeqMatch
#lang-pulse
open Pulse.Lib.OnRange
open Pulse.Lib.Stick.Util

module Seq = FStar.Seq

(* `seq_list_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a list of high-level
values. `seq_list_match` is carefully designed to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values.  *)

let rec seq_list_match
  (#t #t': Type)
  ([@@@mkey]c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
: Tot slprop
  (decreases v)
= match v with
  | [] -> pure (c `Seq.equal` Seq.empty)
  | a :: q -> exists* c1 c2 .
    item_match c1 a **
    seq_list_match c2 q item_match **
    pure (c `Seq.equal` Seq.cons c1 c2)

ghost
fn seq_list_match_nil_intro
  (#t: Type0) (#t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
requires
    (pure (c `Seq.equal` Seq.empty /\
      Nil? v))
ensures
    seq_list_match c v item_match
{
  fold (seq_list_match c [] item_match);
  rewrite seq_list_match c [] item_match
       as seq_list_match c v item_match;
}

ghost
fn seq_list_match_nil_elim
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
requires
    (seq_list_match c v item_match ** pure (
      c `Seq.equal` Seq.empty \/
      Nil? v
    ))
ensures
    (pure (
      c `Seq.equal` Seq.empty /\
      Nil? v
    ))
{
  match v {
    [] -> {
      unfold (seq_list_match c [] item_match);
    }
    a :: q -> {
      unfold (seq_list_match c (a :: q) item_match);
      unreachable()
    }
  }
}

ghost
fn seq_list_match_cons_intro
  (#t #t': Type0)
  (a: t)
  (a' : t')
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << a' :: v }) -> slprop))
requires
    (item_match a a' ** seq_list_match c v item_match)
ensures
    (seq_list_match (Seq.cons a c) (a' :: v) item_match)
{
  fold (seq_list_match (Seq.cons a c) (a' :: v) item_match)
}

ghost
fn seq_list_match_cons_elim
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t' { Cons? v \/ Seq.length c > 0 })
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
requires
    (seq_list_match c v item_match)
returns res: (squash (Cons? v /\ Seq.length c > 0))
ensures
    (item_match (Seq.head c) (List.Tot.hd v) **
      seq_list_match (Seq.tail c) (List.Tot.tl v) item_match
    )
{
  if (Seq.length c = 0 || Nil? v) {
    seq_list_match_nil_elim c v item_match;
    unreachable()
  } else {
    let res : squash (Cons? v /\ Seq.length c > 0) = ();
    rewrite each v as (List.Tot.hd v :: List.Tot.tl v);
    unfold (seq_list_match c (List.Tot.hd v :: List.Tot.tl v) item_match);
    with c1 . assert (item_match c1 (List.Tot.hd v));
    with c2 . assert (seq_list_match c2 (List.Tot.tl v) item_match);
    assert (pure (c2 `Seq.equal` Seq.tail c));
    rewrite (item_match c1 (List.Tot.hd v)) as (item_match (Seq.head c) (List.Tot.hd v));
    rewrite each c2 as Seq.tail c;
    res
  }
}

// this one cannot be proven with seq_seq_match because of the << refinement in the type of item_match
ghost
fn rec seq_list_match_weaken
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match1 item_match2: (t -> (v': t' { v' << v }) -> slprop))
  (prf: (
    (c': t) ->
    (v': t' { v' << v }) ->
    stt_ghost unit emp_inames
      (item_match1 c' v')
      (fun _ -> item_match2 c' v')
  ))
requires
    (seq_list_match c v item_match1)
ensures
    (seq_list_match c v item_match2)
decreases v
{
  if Nil? v {
    seq_list_match_nil_elim c v item_match1;
    seq_list_match_nil_intro c v item_match2;
  } else {
    list_cons_precedes (List.Tot.hd v) (List.Tot.tl v);
    let _ : squash (List.Tot.tl v << v) = ();
    seq_list_match_cons_elim c v item_match1;
    prf (Seq.head c) (List.Tot.hd v);
    ghost fn prf'
      (c': t)
      (v': t' { v' << List.Tot.tl v })
    requires
      item_match1 c' v'
    ensures
      item_match2 c' v'
    {
      prf c' v'
    };
    seq_list_match_weaken (Seq.tail c) (List.Tot.tl v) item_match1 item_match2 prf';
    Seq.cons_head_tail c;
    seq_list_match_cons_intro (Seq.head c) (List.Tot.hd v) (Seq.tail c) (List.Tot.tl v) item_match2;
    rewrite each Seq.cons (Seq.head c) (Seq.tail c) as c;
    ()
  }
}

(* `seq_seq_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a sequence of high-level
values. Contrary to `seq_list_match`, `seq_seq_match` is not meant to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values, because no lemma ensures that `Seq.index s i << s`  *)

let seq_seq_match_item
  (#t1 #t2: Type)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i: nat)
: Tot slprop
= if i < Seq.length c && i < Seq.length l
  then
    p (Seq.index c i) (Seq.index l i)
  else
    pure False

let seq_seq_match_item_tail
  (#t1 #t2: Type)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (delta: nat)
  (i: nat)
: Lemma
  (requires (
    i + delta <= Seq.length c /\
    i + delta <= Seq.length l
  ))
  (ensures (
    seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) i ==
      seq_seq_match_item p c l (i + delta)
  ))
= ()

let seq_seq_match
  (#t1 #t2: Type)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i j: nat)
: Tot slprop
= on_range (seq_seq_match_item p c l) i j

ghost
fn seq_seq_match_length
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
requires
    (seq_seq_match p s1 s2 i j)
ensures
    (seq_seq_match p s1 s2 i j ** pure (i <= j /\ (i == j \/ (j <= Seq.length s1 /\ j <= Seq.length s2))))
{
  unfold (seq_seq_match p s1 s2 i j);
  on_range_le (seq_seq_match_item p s1 s2) #i #j;
  if (i = j) {
    fold (seq_seq_match p s1 s2 i j)
  } else {
    let j' = j - 1;
    if (j' < Seq.length s1 && j' < Seq.length s2) {
      fold (seq_seq_match p s1 s2 i j);
    } else {
      on_range_unsnoc
        ()
        #(seq_seq_match_item p s1 s2)
        #i #j;
      rewrite
        (seq_seq_match_item p s1 s2 (j - 1))
        as
        (pure False);
      unreachable()
    }
  }
}

ghost fn seq_seq_match_empty_intro
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
requires
    emp
ensures
    (seq_seq_match p s1 s2 i i)
{
  on_range_empty (seq_seq_match_item p s1 s2) i;
  fold (seq_seq_match p s1 s2 i i)
}

ghost fn seq_seq_match_empty_elim
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
requires
    (seq_seq_match p s1 s2 i i)
ensures
    (emp)
{
  unfold (seq_seq_match p s1 s2 i i);
  on_range_empty_elim (seq_seq_match_item p s1 s2) i;
}

ghost fn seq_seq_match_join
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j k: nat)
requires
    (seq_seq_match p s1 s2 i j ** seq_seq_match p s1 s2 j k)
ensures
    (seq_seq_match p s1 s2 i k)
{
  unfold (seq_seq_match p s1 s2 i j);
  unfold (seq_seq_match p s1 s2 j k);
  on_range_join i j k;
  fold (seq_seq_match p s1 s2 i k)
}

ghost fn seq_seq_match_split
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j k: nat)
requires
    (seq_seq_match p s1 s2 i k ** pure (i <= j /\ j <= k))
ensures
    (seq_seq_match p s1 s2 i j ** seq_seq_match p s1 s2 j k)
{
  unfold (seq_seq_match p s1 s2 i k);
  on_range_split j;
  fold (seq_seq_match p s1 s2 i j);
  fold (seq_seq_match p s1 s2 j k)
}

ghost fn seq_seq_match_singleton_intro
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (x1: t1)
  (x2: t2)
requires
    (p x1 x2 ** pure (i < Seq.length s1 /\ i < Seq.length s2 /\ x1 == Seq.index s1 i /\ x2 == Seq.index s2 i))
ensures
    (seq_seq_match p s1 s2 i (i + 1))
{
  rewrite p x1 x2 as seq_seq_match_item p s1 s2 i;
  on_range_singleton_intro (seq_seq_match_item p s1 s2) i;
  fold (seq_seq_match p s1 s2 i (i + 1))
}


assume val foo : slprop
assume val bar : slprop

ghost
fn seq_seq_match_singleton_elim
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (x1: t1)
  (x2: t2)
requires
  (seq_seq_match p s1 s2 i (i + 1))
returns _: (squash (i < Seq.length s1 /\ i < Seq.length s2))
ensures
  (p (Seq.index s1 i) (Seq.index s2 i))
{
  seq_seq_match_length p s1 s2 i (i + 1);
  unfold (seq_seq_match p s1 s2 i (i + 1));
  on_range_singleton_elim ();
  // unfold (seq_seq_match_item p s1 s2 i);
  let b = StrongExcludedMiddle.strong_excluded_middle (i < Seq.length s1 && i < Seq.length s2);
  if b {
    assert (pure (i < Seq.length s1 && i < Seq.length s2));
    rewrite each x1 as Seq.index s1 i;
    rewrite each x2 as Seq.index s2 i;
    rewrite seq_seq_match_item p s1 s2 i as p (Seq.index s1 i) (Seq.index s2 i);
    ()
  } else {
    unreachable()
  }
}

ghost fn seq_seq_match_enqueue_left
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
    (seq_seq_match p s1 s2 (i - 1) j)
{
  unfold (seq_seq_match p s1 s2 i j);
  rewrite p x1 x2 as seq_seq_match_item p s1 s2 (i - 1);
  on_range_cons (i - 1);
  fold (seq_seq_match p s1 s2 (i - 1) j)
}

ghost fn seq_seq_match_enqueue_right
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
    (seq_seq_match p s1 s2 i (j + 1))
{
  unfold (seq_seq_match p s1 s2 i j);
  rewrite p x1 x2 as seq_seq_match_item p s1 s2 j;
  on_range_snoc ();
  fold (seq_seq_match p s1 s2 i (j + 1))
}

ghost fn seq_seq_match_dequeue_left
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (j: nat)
requires
   (seq_seq_match p s1 s2 i j ** pure (i < j))
returns _: squash (i < j /\ j <= Seq.length s1 /\ j <= Seq.length s2)
ensures
   seq_seq_match p s1 s2 (i + 1) j ** p (Seq.index s1 i) (Seq.index s2 i)
{
  seq_seq_match_length p s1 s2 i j;
  unfold (seq_seq_match p s1 s2 i j);
  on_range_uncons ();
  fold (seq_seq_match p s1 s2 (i + 1) j);
  rewrite (seq_seq_match_item p s1 s2 i) as (p (Seq.index s1 i) (Seq.index s2 i));
}

ghost fn seq_seq_match_dequeue_right
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (j: nat)
requires
    (seq_seq_match p s1 s2 i j ** pure (i < j))
returns _: (squash (i < j /\ j <= Seq.length s1 /\ j <= Seq.length s2))
ensures
    (seq_seq_match p s1 s2 i (j - 1) ** p (Seq.index s1 (j - 1)) (Seq.index s2 (j - 1)))
{
  seq_seq_match_length p s1 s2 i j;
  unfold (seq_seq_match p s1 s2 i j);
  on_range_unsnoc ();
  fold (seq_seq_match p s1 s2 i (j - 1));
  rewrite (seq_seq_match_item p s1 s2 (j-1)) as (p (Seq.index s1 (j - 1)) (Seq.index s2 (j - 1)))
}


ghost fn seq_seq_match_weaken
  (#t1 #t2: Type0)
  (p p': t1 -> t2 -> slprop)
  (w: ((x1: t1) -> (x2: t2) -> stt_ghost unit emp_inames
    (p x1 x2) (fun _ -> p' x1 x2)
  ))
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
    (seq_seq_match p' c1' c2' i j)
{
  unfold (seq_seq_match p c1 c2 i j);
  ghost fn aux
    (k: (k: nat { i <= k /\ k < j }))
  requires
    seq_seq_match_item p c1 c2 k
  ensures
    seq_seq_match_item p' c1' c2' k
  {
    rewrite (seq_seq_match_item p c1 c2 k)
      as (p (Seq.index (Seq.slice c1 i j) (k - i)) (Seq.index (Seq.slice c2 i j) (k - i)));
    w _ _;
    rewrite (p' (Seq.index (Seq.slice c1 i j) (k - i)) (Seq.index (Seq.slice c2 i j) (k - i)))
      as (seq_seq_match_item p' c1' c2' k)
  };
  on_range_weaken
    (seq_seq_match_item p c1 c2)
    (seq_seq_match_item p' c1' c2')
    i j
    aux;
  fold (seq_seq_match p' c1' c2' i j)
}

ghost fn seq_seq_match_rewrite_seq
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
    (seq_seq_match p c1' c2' i j)
{
  ghost fn aux (x1: t1) (x2: t2)
  requires p x1 x2
  ensures p x1 x2
  {
    ()
  };
  seq_seq_match_weaken p p aux c1 c1' c2 c2' i j
}

ghost fn seq_seq_match_weaken_with_implies
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
      (seq_seq_match p c1' c2' i j @==> seq_seq_match p c1 c2 i j)
    )
{
  ghost fn aux1
    (x1: t1) (x2: t2)
  requires (p x1 x2)
  ensures (p x1 x2)
  {
    ()
  };
  seq_seq_match_weaken
    p p aux1
    c1 c1'
    c2 c2'
    i j;
  ghost fn aux2 (_: unit)
    requires emp ** (seq_seq_match p c1' c2' i j)
    ensures seq_seq_match p c1 c2 i j
  {
      seq_seq_match_weaken
        p p aux1
        c1' c1
        c2' c2
        i j
  };
  intro_stick
    (seq_seq_match p c1' c2' i j)
    (seq_seq_match p c1 c2 i j)
    emp
    aux2
}

(* Going between `seq_list_match` and `seq_seq_match` *)

ghost fn seq_seq_match_tail_elim
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: Seq.seq (t2))
  (delta: nat {
    delta <= Seq.length c /\
    delta <= Seq.length l
  })
  (i j: nat)
requires
    (seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) i j)
ensures
    (seq_seq_match p c l (i + delta) (j + delta))
{
  unfold (seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) i j);
  on_range_le (seq_seq_match_item p _ _);
  ghost fn aux
    (k: nat { i <= k /\ k < j })
  requires
    seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k
  ensures
    seq_seq_match_item p c l (k + delta)
  {
    if (k < Seq.length c - delta && k < Seq.length l - delta) {
       seq_seq_match_item_tail p c l delta k;
       rewrite
         (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k)
       as
       (seq_seq_match_item p c l (k + delta))
    } else {
      rewrite
        (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k)
        as
        (pure False);
      unreachable()
    }
  };
  on_range_weaken_and_shift
    (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)))
    (seq_seq_match_item p c l)
    delta
    i j
    aux;
  fold (seq_seq_match p c l (i + delta) (j + delta))
}

ghost fn seq_seq_match_tail_intro
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (delta: nat {
    delta <= Seq.length c /\
    delta <= Seq.length l
  })
  (i: nat {
    delta <= i
  })
  (j: nat)
requires
    (seq_seq_match p c l i j)
returns res: squash (i <= j)
ensures
    (seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (i - delta) (j - delta))
{
  unfold (seq_seq_match p c l i j);
  on_range_le (seq_seq_match_item p _ _);
  ghost fn aux
    (k: nat { i <= k /\ k < j })
  requires
    seq_seq_match_item p c l k
  ensures
    seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (k + (0 - delta))
  {
      if (k < Seq.length c && k < Seq.length l) {
        seq_seq_match_item_tail p c l delta (k - delta);
        rewrite
          (seq_seq_match_item p c l k)
          as
          (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (k + (0 - delta)))
      } else {
        rewrite
          (seq_seq_match_item p c l k)
          as
          (pure False);
        unreachable()
      }
  };
  on_range_weaken_and_shift
    (seq_seq_match_item p c l)
    (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)))
    (0 - delta)
    i j
    aux;
  fold (seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (i - delta) (j - delta));
  ()
}

ghost fn seq_seq_match_move
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c1: Seq.seq t1)
  (c2: Seq.seq t2)
  (i j: nat)
  (c1': Seq.seq t1)
  (c2': Seq.seq t2)
  (i' j': nat)
requires
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ i' <= j' /\ ((i == j /\ i' == j') \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j' <= Seq.length c1' /\ j' <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i' j' /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i' j'
      )))
    ))
ensures
    (seq_seq_match p c1' c2' i' j')
{
  if (i = j) {
    seq_seq_match_empty_elim p c1 c2 i;
    seq_seq_match_empty_intro p c1' c2' i';
  } else {
    assert (pure (Seq.length (Seq.slice c1 i j) == Seq.length (Seq.slice c1' i' j')));
    assert (pure (j - i == j' - i'));
    seq_seq_match_length p c1 c2 i j;
    seq_seq_match_tail_intro p c1 c2 i i j;
    seq_seq_match_rewrite_seq p (Seq.slice c1 i (Seq.length c1)) (Seq.slice c1' i' (Seq.length c1')) (Seq.slice c2 i (Seq.length c2)) (Seq.slice c2' i' (Seq.length c2')) 0 (j - i);
    seq_seq_match_tail_elim p c1' c2' i' 0 (j - i)
  }
}

ghost fn rec seq_seq_match_seq_list_match
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
requires
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      (Seq.length c == List.Tot.length l)
    ))
ensures
    (seq_list_match c l p)
decreases l
{
  match l {
    [] -> {
      on_range_eq_emp (seq_seq_match_item p c (Seq.seq_of_list l)) 0 (List.Tot.length l);
      rewrite (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
        as emp;
      seq_list_match_nil_intro c l p
    }
    a :: q -> {
      unfold (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l));
      Seq.lemma_seq_of_list_induction (a :: q);
      on_range_uncons ();
      rewrite
        (seq_seq_match_item p c (Seq.seq_of_list l) 0)
        as
        (p (Seq.head c) (List.Tot.hd l));
      fold (seq_seq_match p c (Seq.seq_of_list l) 1 (List.Tot.length l));
      let _ = seq_seq_match_tail_intro
        p c (Seq.seq_of_list l) 1 1 (List.Tot.length l);
      rewrite
        (seq_seq_match p (Seq.slice c 1 (Seq.length c)) (Seq.slice (Seq.seq_of_list l) 1 (Seq.length (Seq.seq_of_list l))) (1 - 1) (List.Tot.length l - 1))
        as
        (seq_seq_match p (Seq.tail c) (Seq.seq_of_list (List.Tot.tl l)) 0 (List.Tot.length (List.Tot.tl l)));
      seq_seq_match_seq_list_match p _ (List.Tot.tl l);
      Seq.cons_head_tail c;
      seq_list_match_cons_intro (Seq.head c) (List.Tot.hd l) (Seq.tail c) (List.Tot.tl l) p;
      rewrite each (Seq.cons (Seq.head c) (Seq.tail c)) as c;
    }
  }
}

ghost fn rec seq_list_match_seq_seq_match
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
requires
    (seq_list_match c l p)
ensures
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      Seq.length c == List.Tot.length l
    ))
decreases l
{
  match l {
    [] -> {
      seq_list_match_nil_elim c l p;
    on_range_empty
      (seq_seq_match_item p c (Seq.seq_of_list l))
      0;
    fold (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    }
    a :: q -> {
      Seq.lemma_seq_of_list_induction (a :: q);
      seq_list_match_cons_elim c l p;
      Seq.cons_head_tail c;
      seq_list_match_seq_seq_match p (Seq.tail c) (List.Tot.tl l);
      rewrite
        (seq_seq_match p (Seq.tail c) (Seq.seq_of_list (List.Tot.tl l)) 0 (List.Tot.length (List.Tot.tl l)))
        as
        (seq_seq_match p (Seq.slice c 1 (Seq.length c)) (Seq.slice (Seq.seq_of_list l) 1 (Seq.length (Seq.seq_of_list l))) 0 (List.Tot.length (List.Tot.tl l)));
      let _ = seq_seq_match_tail_elim
        p c (Seq.seq_of_list l) 1 0 (List.Tot.length (List.Tot.tl l))
      ;
      unfold (seq_seq_match p c (Seq.seq_of_list l) 1 (List.Tot.length l));
      rewrite
        (p (Seq.head c) (List.Tot.hd l))
        as
        (seq_seq_match_item p c (Seq.seq_of_list l) 0);
      on_range_cons 0;
      fold (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    }
  }
}

ghost fn seq_seq_match_seq_list_match_with_implies
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
requires
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      (Seq.length c == List.Tot.length l)
    ))
ensures
    (seq_list_match c l p ** (seq_list_match c l p @==> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)))
{
  seq_seq_match_seq_list_match p c l;
  ghost fn aux (_: unit)
  requires
    emp ** seq_list_match c l p
  ensures
    seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)
  {
    seq_list_match_seq_seq_match p c l
  };
  intro_stick
    (seq_list_match c l p)
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    emp
    aux
}

ghost fn seq_list_match_seq_seq_match_with_implies
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
requires
    (seq_list_match c l p)
ensures
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) @==> seq_list_match c l p) ** pure (
      Seq.length c == List.Tot.length l
    ))
{
  seq_list_match_seq_seq_match p c l; 
  ghost fn aux (_: unit)
  requires
    emp ** seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)
  ensures
    seq_list_match c l p
  {
    seq_seq_match_seq_list_match p c l
  }; 
  intro_stick
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (seq_list_match c l p)
    emp
    aux
}

ghost fn seq_list_match_length
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
requires
    (seq_list_match c l p)
ensures
    (seq_list_match c l p ** pure (
      Seq.length c == List.Tot.length l
    ))
{
  seq_list_match_seq_seq_match_with_implies p c l;
  seq_seq_match_length p _ _ _ _;
  elim_stick
    (seq_seq_match p _ _ _ _)
    (seq_list_match c l p)
}

ghost fn seq_list_match_index
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
      (p (Seq.index s1 i) (List.Tot.index s2 i) @==>
        seq_list_match s1 s2 p)
    )
{
  seq_list_match_seq_seq_match_with_implies p s1 s2;
  let res : squash (i < Seq.length s1 /\ List.Tot.length s2 == Seq.length s1) = ();
  rewrite_with_stick
    (seq_seq_match p s1 (Seq.seq_of_list s2) 0 (List.Tot.length s2))
    (on_range (seq_seq_match_item p s1 (Seq.seq_of_list s2)) 0 (List.Tot.length s2));
  trans _ _ (seq_list_match s1 s2 p);
  on_range_focus i;
  trans _ _ (seq_list_match s1 s2 p);
  rewrite_with_stick
    (seq_seq_match_item p _ _ _)
    (p (Seq.index s1 i) (List.Tot.index s2 i));
  trans _ _ (seq_list_match s1 s2 p);
  res
}

(* Random array access

Since `seq_list_match` is defined recursively on the list of
high-level values, it is used naturally left-to-right. By contrast,
in practice, an application may populate an array in a different
order, or even out-of-order. `seq_seq_match` supports that scenario
better, as we show below.

*)

ghost fn seq_seq_match_item_match_option_elim
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
requires
    (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
ensures
    (seq_seq_match p s1 s2 i j)
{
  ghost fn aux
    (k: (k: nat { i <= k /\ k < j }))
  requires
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2)) k
  ensures
    (seq_seq_match_item p s1 s2) k
  {
      rewrite
        (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2) k)
        as
        (seq_seq_match_item p s1 s2 k)
  };
  unfold (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j);
  on_range_weaken
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2))
    (seq_seq_match_item p s1 s2)
    i j
    aux;
  fold (seq_seq_match p s1 s2 i j)
}

ghost fn seq_seq_match_item_match_option_intro
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
requires
    (seq_seq_match p s1 s2 i j)
ensures
    (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
{
  ghost fn aux
    (k: (k: nat { i <= k /\ k < j }))
  requires
    (seq_seq_match_item p s1 s2) k
  ensures
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2)) k
  {
      rewrite
        (seq_seq_match_item p s1 s2 k)
        as
        (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2) k)
  };
  unfold (seq_seq_match p s1 s2 i j);
  on_range_weaken
    (seq_seq_match_item p s1 s2)
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2))
    i j
    aux;
  fold (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
}

ghost fn rec seq_seq_match_item_match_option_init
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s: Seq.seq t1)
requires
    emp
ensures
    (seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))
decreases (Seq.length s)
{
  if (Seq.length s = 0) {
    on_range_empty (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None)) 0;
    fold (seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))
  } else {
    seq_seq_match_item_match_option_init p (Seq.tail s);
    unfold (seq_seq_match (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None) 0 (Seq.length (Seq.tail s)));
    ghost fn aux
      (k: (k: nat { 0 <= k /\ k < Seq.length (Seq.tail s) }))
    requires
      (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None)) k
    ensures
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None)) (k + 1)
    {
        rewrite
          (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None) k)
          as
          (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None) (k + 1))
    };
    on_range_weaken_and_shift
      (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None))
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None))
      1
      0
      (Seq.length (Seq.tail s))
      aux;
    rewrite
      emp
      as
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None) 0);
    on_range_cons 0;
    fold (seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))
  }
}

ghost fn seq_seq_match_upd
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
  (k: nat {
    i <= j /\ j < k
  })
  (x1: t1)
  (x2: t2)
requires
    (seq_seq_match p s1 s2 i k ** p x1 x2)
returns res: (squash (j < Seq.length s1 /\ j < Seq.length s2))
ensures
    (
      seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i k **
      p (Seq.index s1 j) (Seq.index s2 j) // retrieve the occurrence before update
    )
{
  seq_seq_match_length p s1 s2 i k;
  unfold (seq_seq_match p s1 s2 i k);
  on_range_get j;
  let res : squash (j < Seq.length s1 /\ j < Seq.length s2) = ();
  rewrite (seq_seq_match_item p s1 s2 j) as (p (Seq.index s1 j) (Seq.index s2 j));
  rewrite
    (p x1 x2)
    as
    (seq_seq_match_item p (Seq.upd s1 j x1) (Seq.upd s2 j x2) j);
  ghost fn aux
    (x1: t1)
    (x2: t2)
  requires p x1 x2
  ensures p x1 x2
  {
    ()
  };
  fold (seq_seq_match p s1 s2 i j);
  seq_seq_match_weaken
    p p aux
    s1 (Seq.upd s1 j x1)
    s2 (Seq.upd s2 j x2)
    i j;
  fold (seq_seq_match p s1 s2 (j + 1) k);
  seq_seq_match_weaken
    p p aux
    s1 (Seq.upd s1 j x1)
    s2 (Seq.upd s2 j x2)
    (j + 1) k;
  unfold (seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i j);
  unfold (seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) (j + 1) k);
  on_range_put
    i j k;
  fold (seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i k);
  res
}

ghost fn seq_seq_match_item_match_option_upd_none
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k /\ 
    (j < Seq.length s2 ==> None? (Seq.index s2 j)) // condition necessary to avoid resource leakage
  })
  (x1: t1)
  (x2: t2)
requires
    (seq_seq_match (item_match_option p) s1 s2 i k ** p x1 x2)
returns res: (squash (j < Seq.length s1 /\ j < Seq.length s2))
ensures
    (
      seq_seq_match (item_match_option p) (Seq.upd s1 j x1) (Seq.upd s2 j (Some x2)) i k
    )
{
  rewrite
    (p x1 x2)
    as
    (item_match_option p x1 (Some x2));
  seq_seq_match_upd (item_match_option p) s1 s2 i j k x1 (Some x2);
  rewrite (item_match_option p (Seq.index s1 j) (Seq.index s2 j)) as emp
}

ghost fn seq_seq_match_item_match_option_index
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k /\
    (j < Seq.length s2 ==> Some? (Seq.index s2 j))
  })
requires
    (seq_seq_match (item_match_option p) s1 s2 i k)
returns res: (squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j)))
ensures
    (
      seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i k **
      p (Seq.index s1 j) (Some?.v (Seq.index s2 j))
    )
{
  seq_seq_match_length (item_match_option p) s1 s2 i k;
  unfold (seq_seq_match (item_match_option p) s1 s2 i k);
  on_range_get j;
  let res : squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j)) = ();
  rewrite
    (seq_seq_match_item (item_match_option p) s1 s2 j)
    as
    (p (Seq.index s1 j) (Some?.v (Seq.index s2 j)));
  rewrite
    emp
    as
    (seq_seq_match_item (item_match_option p) s1 (Seq.upd s2 j None) j);
  ghost fn aux
    (x1: t1)
    (x2: option t2)
  requires item_match_option p x1 x2
  ensures item_match_option p x1 x2
  {
    ()
  };
  fold (seq_seq_match (item_match_option p) s1 s2 i j);
  seq_seq_match_weaken
    (item_match_option p) (item_match_option p) aux
    s1 s1
    s2 (Seq.upd s2 j None)
    i j;
  fold (seq_seq_match (item_match_option p) s1 s2 (j + 1) k);
  seq_seq_match_weaken
    (item_match_option p) (item_match_option p) aux
    s1 s1
    s2 (Seq.upd s2 j None)
    (j + 1) k;
  unfold (seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i j);
  unfold (seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) (j + 1) k);
  on_range_put
    i j k;
  fold (seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i k);
  res
}

ghost
fn seq_seq_match_item_match_option_upd_some
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k /\ 
    (j < Seq.length s2 ==> Some? (Seq.index s2 j))
  })
  (x1: t1)
  (x2: t2)
  requires
    seq_seq_match (item_match_option p) s1 s2 i k ** p x1 x2
  returns res: squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j))
  ensures
    seq_seq_match (item_match_option p) (Seq.upd s1 j x1) (Seq.upd s2 j (Some x2)) i k **
    p (Seq.index s1 j) (Some?.v (Seq.index s2 j))
{
  seq_seq_match_item_match_option_index p s1 s2 i j k;
  seq_seq_match_item_match_option_upd_none p s1 (Seq.upd s2 j None) i j k x1 x2;
  assert (pure (Seq.upd (Seq.upd s2 j None) j (Some x2) `Seq.equal` Seq.upd s2 j (Some x2)));
  ()
}
