(*
   Copyright 2023 Microsoft Research

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
include Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Seq = FStar.Seq

(* `seq_list_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a list of high-level
values. `seq_list_match` is carefully designed to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values.  *)

val seq_list_match
  (#t #t': Type)
  ([@@@mkey] c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
: Tot slprop

val seq_list_match_nil_intro
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
: stt_ghost unit emp_inames
    (pure (c `Seq.equal` Seq.empty /\
      Nil? v))
    (fun _ -> seq_list_match c v item_match)

val seq_list_match_nil_elim
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
: stt_ghost unit emp_inames
    (seq_list_match c v item_match ** pure (
      c `Seq.equal` Seq.empty \/
      Nil? v
    ))
    (fun _ -> pure (
      c `Seq.equal` Seq.empty /\
      Nil? v
    ))

let list_cons_precedes
  (#t: Type)
  (a: t)
  (q: list t)
: Lemma
  ((a << a :: q) /\ (q << a :: q))
  [SMTPat (a :: q)]
= assert (List.Tot.hd (a :: q) << (a :: q));
  assert (List.Tot.tl (a :: q) << (a :: q))

val seq_list_match_cons_intro
  (#t #t': Type0)
  (a: t)
  (a' : t')
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << a' :: v }) -> slprop))
: stt_ghost unit emp_inames
    (item_match a a' ** seq_list_match c v item_match)
    (fun _ -> seq_list_match (Seq.cons a c) (a' :: v) item_match)

val seq_list_match_cons_elim
  (#t #t': Type0)
  (c: Seq.seq t)
  (v: list t' { Cons? v \/ Seq.length c > 0 })
  (item_match: (t -> (v': t' { v' << v }) -> slprop))
: stt_ghost (squash (Cons? v /\ Seq.length c > 0))
    emp_inames
    (seq_list_match c v item_match)
    (fun _ -> item_match (Seq.head c) (List.Tot.hd v) **
      seq_list_match (Seq.tail c) (List.Tot.tl v) item_match)

// this one cannot be proven with seq_seq_match because of the << refinement in the type of item_match
val seq_list_match_weaken
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
: stt_ghost unit emp_inames
    (seq_list_match c v item_match1)
    (fun _ -> seq_list_match c v item_match2)

(* `seq_seq_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a sequence of high-level
values. Contrary to `seq_list_match`, `seq_seq_match` is not meant to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values, because no lemma ensures that `Seq.index s i << s`  *)

val seq_seq_match
  (#t1 #t2: Type)
  (p: t1 -> t2 -> slprop)
  ([@@@mkey] c : Seq.seq t1)
  (l : Seq.seq t2)
  (i j: nat)
: Tot slprop

val seq_seq_match_length
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match p s1 s2 i j ** pure (i <= j /\ (i == j \/ (j <= Seq.length s1 /\ j <= Seq.length s2))))

val seq_seq_match_empty_intro
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
: stt_ghost unit emp_inames
    emp
    (fun _ -> seq_seq_match p s1 s2 i i)

val seq_seq_match_empty_elim
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i i)
    (fun _ -> emp)

val seq_seq_match_join
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j k: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i j ** seq_seq_match p s1 s2 j k)
    (fun _ -> seq_seq_match p s1 s2 i k)

val seq_seq_match_split
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j k: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i k ** pure (i <= j /\ j <= k))
    (fun _ -> seq_seq_match p s1 s2 i j ** seq_seq_match p s1 s2 j k)

val seq_seq_match_singleton_intro
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (x1: t1)
  (x2: t2)
: stt_ghost unit emp_inames
    (p x1 x2 ** pure (i < Seq.length s1 /\ i < Seq.length s2 /\ x1 == Seq.index s1 i /\ x2 == Seq.index s2 i))
    (fun _ -> seq_seq_match p s1 s2 i (i + 1))

val seq_seq_match_singleton_elim
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (x1: t1)
  (x2: t2)
: stt_ghost (squash (i < Seq.length s1 /\ i < Seq.length s2)) emp_inames
    (seq_seq_match p s1 s2 i (i + 1))
    (fun _ -> p (Seq.index s1 i) (Seq.index s2 i))

val seq_seq_match_enqueue_left
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat { i > 0 /\ i <= Seq.length s1 /\ i <= Seq.length s2 })
  (j: nat)
  (x1: t1)
  (x2: t2)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i j ** p x1 x2 ** pure (x1 == Seq.index s1 (i - 1) /\ x2 == Seq.index s2 (i - 1)))
    (fun _ -> seq_seq_match p s1 s2 (i - 1) j)

val seq_seq_match_enqueue_right
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (j: nat { j < Seq.length s1 /\ j < Seq.length s2 })
  (x1: t1)
  (x2: t2)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i j ** p x1 x2 ** pure (x1 == Seq.index s1 j /\ x2 == Seq.index s2 j))
    (fun _ -> seq_seq_match p s1 s2 i (j + 1))

val seq_seq_match_dequeue_left
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (j: nat)
: stt_ghost (squash (i < j /\ j <= Seq.length s1 /\ j <= Seq.length s2)) emp_inames
    (seq_seq_match p s1 s2 i j ** pure (i < j))
    (fun _ -> seq_seq_match p s1 s2 (i + 1) j ** p (Seq.index s1 i) (Seq.index s2 i))

val seq_seq_match_dequeue_right
(#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i: nat)
  (j: nat)
: stt_ghost (squash (i < j /\ j <= Seq.length s1 /\ j <= Seq.length s2)) emp_inames
    (seq_seq_match p s1 s2 i j ** pure (i < j))
    (fun _ -> seq_seq_match p s1 s2 i (j - 1) ** p (Seq.index s1 (j - 1)) (Seq.index s2 (j - 1)))

val seq_seq_match_weaken
  (#t1 #t2: Type0)
  (p p': t1 -> t2 -> slprop)
  (w: ((x1: t1) -> (x2: t2) -> stt_ghost unit emp_inames
    (p x1 x2) (fun _ -> p' x1 x2)
  ))
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ (i == j \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j <= Seq.length c1' /\ j <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
      )))
    ))
    (fun _ -> seq_seq_match p' c1' c2' i j)

val seq_seq_match_rewrite_seq
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ (i == j \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j <= Seq.length c1' /\ j <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
      )))
    ))
    (fun _ -> seq_seq_match p c1' c2' i j)

val seq_seq_match_weaken_with_implies
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ (i == j \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j <= Seq.length c1' /\ j <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
      )))
    ))
    (fun _ -> seq_seq_match p c1' c2' i j **
      (seq_seq_match p c1' c2' i j @==> seq_seq_match p c1 c2 i j)
    )

val seq_seq_match_move
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c1: Seq.seq t1)
  (c2: Seq.seq t2)
  (i j: nat)
  (c1': Seq.seq t1)
  (c2': Seq.seq t2)
  (i' j': nat)
: stt_ghost unit emp_inames
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ i' <= j' /\ ((i == j /\ i' == j') \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j' <= Seq.length c1' /\ j' <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i' j' /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i' j'
      )))
    ))
    (fun _ -> seq_seq_match p c1' c2' i' j')

(* Going between `seq_list_match` and `seq_seq_match` *)

val seq_seq_match_seq_list_match
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit emp_inames
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      (Seq.length c == List.Tot.length l)
    ))
    (fun _ -> seq_list_match c l p)

val seq_list_match_seq_seq_match
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit emp_inames
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      Seq.length c == List.Tot.length l
    ))

val seq_seq_match_seq_list_match_with_implies
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit emp_inames
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      (Seq.length c == List.Tot.length l)
    ))
    (fun _ -> seq_list_match c l p ** (seq_list_match c l p @==> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)))

val seq_list_match_seq_seq_match_with_implies
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit emp_inames
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) @==> seq_list_match c l p) ** pure (
      Seq.length c == List.Tot.length l
    ))

val seq_list_match_length
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit emp_inames
    (seq_list_match c l p)
    (fun _ -> seq_list_match c l p ** pure (
      Seq.length c == List.Tot.length l
    ))

val seq_list_match_index
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: list t2)
  (i: nat)
: stt_ghost (squash (i < Seq.length s1 /\ List.Tot.length s2 == Seq.length s1))
    emp_inames
    (seq_list_match s1 s2 p ** pure (
      (i < Seq.length s1 \/ i < List.Tot.length s2)
    ))
    (fun _ ->
      p (Seq.index s1 i) (List.Tot.index s2 i) **
      (p (Seq.index s1 i) (List.Tot.index s2 i) @==>
        seq_list_match s1 s2 p)
    )


ghost
fn rec
seq_list_match_append_intro
  (#t #t': Type0) // FIXME: universe polymorphism
  (item_match: (t -> t' -> slprop))
  (c1: Seq.seq t)
  (l1: list t')
  (c2: Seq.seq t)
  (l2: list t')
requires
    (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match)
ensures
    (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match)
decreases
  l1
{
  seq_list_match_length item_match c1 l1;
  if (Nil? l1) {
    let prf : squash (c1 `Seq.equal` Seq.empty) = ();
    let prf2 = Seq.append_empty_l c2;
    seq_list_match_nil_elim c1 l1 item_match;
    rewrite (seq_list_match c2 l2 item_match)
      as (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match)
  } else {
    let prf1 = seq_list_match_cons_elim c1 l1 item_match;
    seq_list_match_append_intro #t #t' item_match (Seq.tail c1) (List.Tot.tl l1) c2 l2; // FIXME: WHY WHY WHY do I need to provide those implicit arguments t, t'?
    seq_list_match_cons_intro (Seq.head c1) (List.Tot.hd l1) (Seq.tail c1 `Seq.append` c2) (List.Tot.tl l1 `List.Tot.append` l2) item_match;
    let prf2: squash (Seq.cons (Seq.head c1) (Seq.tail c1 `Seq.append` c2) `Seq.equal` (c1 `Seq.append` c2)) = ();
    rewrite
      (seq_list_match (Seq.cons (Seq.head c1) (Seq.tail c1 `Seq.append` c2)) (List.Tot.hd l1 :: (List.Tot.tl l1 `List.Tot.append` l2)) item_match)
      as (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match)
  }
}



ghost
fn rec
seq_list_match_append_elim
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
    (seq_list_match c1 l1 item_match ** seq_list_match c2 l2 item_match ** pure (
      Seq.length c1 == List.Tot.length l1 /\
      Seq.length c2 == List.Tot.length l2
    ))
decreases
  l1
{
  seq_list_match_length item_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2);
  let prf_len_c = Seq.lemma_len_append c1 c2;
  let prf_len_l = List.Tot.append_length l1 l2;
  let prf : squash (Seq.length c1 == List.Tot.length l1 /\ Seq.length c2 == List.Tot.length l2) = ();
  if (Nil? l1) {
    let prf : squash (c1 `Seq.equal` Seq.empty) = ();
    let prf2 = Seq.append_empty_l c2;
    seq_list_match_nil_intro c1 l1 item_match;
    rewrite (seq_list_match (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match)
      as (seq_list_match c2 l2 item_match)
  } else {
    let prf1 = seq_list_match_cons_elim (c1 `Seq.append` c2) (l1 `List.Tot.append` l2) item_match;
    let prf_tl_c : squash (Seq.tail (c1 `Seq.append` c2) `Seq.equal` (Seq.tail c1 `Seq.append` c2)) = ();
    rewrite
      (seq_list_match (Seq.tail (c1 `Seq.append` c2)) (List.Tot.tl (l1 `List.Tot.append` l2)) item_match)
      as (seq_list_match (Seq.tail c1 `Seq.append` c2) (List.Tot.tl l1 `List.Tot.append` l2) item_match);
    seq_list_match_append_elim #t #t' item_match (Seq.tail c1) (List.Tot.tl l1) c2 l2; // FIXME: WHY WHY WHY do I need to provide those implicit arguments t, t'?
    seq_list_match_cons_intro (Seq.head (c1 `Seq.append` c2)) (List.Tot.hd (l1 `List.Tot.append` l2)) (Seq.tail c1) (List.Tot.tl l1) item_match;
    rewrite
      (seq_list_match (Seq.cons (Seq.head (c1 `Seq.append` c2)) (Seq.tail c1)) (List.Tot.hd (l1 `List.Tot.append` l2) :: List.Tot.tl l1) item_match)
      as (seq_list_match c1 l1 item_match)
  }
}


(* Random array access

Since `seq_list_match` is defined recursively on the list of
high-level values, it is used naturally left-to-right. By contrast,
in practice, an application may populate an array in a different
order, or even out-of-order. `seq_seq_match` supports that scenario
better, as we show below.

*)

let seq_map (#t1 #t2: Type) (f: t1 -> t2) (s: Seq.seq t1) : Tot (Seq.seq t2) =
  Seq.init (Seq.length s) (fun i -> f (Seq.index s i))

let item_match_option
  (#t1 #t2: Type)
  (p: t1 -> t2 -> slprop)
  (x1: t1)
  (x2: option t2)
: Tot slprop
= match x2 with
  | None -> emp
  | Some x2' -> p x1 x2'

val seq_seq_match_item_match_option_elim
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: stt_ghost unit emp_inames
    (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
    (fun _ -> seq_seq_match p s1 s2 i j)

val seq_seq_match_item_match_option_intro
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: stt_ghost unit emp_inames
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)

val seq_seq_match_item_match_option_init
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s: Seq.seq t1)
: stt_ghost unit emp_inames
    emp
    (fun _ -> seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))

val seq_seq_match_upd
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
: stt_ghost (squash (j < Seq.length s1 /\ j < Seq.length s2))
    emp_inames
    (seq_seq_match p s1 s2 i k ** p x1 x2)
    (fun _ -> 
      seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i k **
      p (Seq.index s1 j) (Seq.index s2 j) // retrieve the occurrence before update
    )
    
val seq_seq_match_item_match_option_upd_none
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
: stt_ghost (squash (j < Seq.length s1 /\ j < Seq.length s2))
    emp_inames
    (seq_seq_match (item_match_option p) s1 s2 i k ** p x1 x2)
    (fun _ -> 
      seq_seq_match (item_match_option p) (Seq.upd s1 j x1) (Seq.upd s2 j (Some x2)) i k
    )

val seq_seq_match_item_match_option_index
  (#t1 #t2: Type0)
  (p: t1 -> t2 -> slprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k /\
    (j < Seq.length s2 ==> Some? (Seq.index s2 j))
  })
: stt_ghost (squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j)))
    emp_inames
    (seq_seq_match (item_match_option p) s1 s2 i k)
    (fun _ -> 
      seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i k **
      p (Seq.index s1 j) (Some?.v (Seq.index s2 j))
    )

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
