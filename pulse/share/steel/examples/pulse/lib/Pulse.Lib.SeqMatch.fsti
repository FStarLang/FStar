module Pulse.Lib.SeqMatch
include Pulse.Lib.Pervasives
open Pulse.Lib.Stick

module Seq = FStar.Seq
module SZ = FStar.SizeT

(* `seq_list_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a list of high-level
values. `seq_list_match` is carefully designed to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values.  *)

val seq_list_match
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> vprop))
: Tot vprop

// this one cannot be proven with seq_seq_match because of the << refinement in the type of item_match
val seq_list_match_weaken
  (#opened: _)
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match1 item_match2: (t -> (v': t' { v' << v }) -> vprop))
  (prf: (
    (#opened: _) ->
    (c': t) ->
    (v': t' { v' << v }) ->
    stt_ghost unit opened
      (item_match1 c' v')
      (fun _ -> item_match2 c' v')
  ))
: stt_ghost unit opened
    (seq_list_match c v item_match1)
    (fun _ -> seq_list_match c v item_match2)

(* `seq_seq_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a sequence of high-level
values. Contrary to `seq_list_match`, `seq_seq_match` is not meant to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values, because no lemma ensures that `Seq.index s i << s`  *)

val seq_seq_match
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i j: nat)
: Tot vprop

val seq_seq_match_length
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: stt_ghost unit opened
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match p s1 s2 i j ** pure (i <= j /\ (i == j \/ (j <= Seq.length s1 /\ j <= Seq.length s2))))

val seq_seq_match_weaken
  (#opened: _)
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> vprop)
  (w: ((x1: t1) -> (x2: t2) -> stt_ghost unit opened
    (p x1 x2) (fun _ -> p' x1 x2)
  ))
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: stt_ghost unit opened
    (seq_seq_match p c1 c2 i j ** pure (
      (i <= j /\ (i == j \/ (
        j <= Seq.length c1 /\ j <= Seq.length c2 /\
        j <= Seq.length c1' /\ j <= Seq.length c2' /\
        Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
        Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
      )))
    ))
    (fun _ -> seq_seq_match p' c1' c2' i j)

val seq_seq_match_weaken_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: stt_ghost unit opened
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

(* Going between `seq_list_match` and `seq_seq_match` *)

val seq_seq_match_seq_list_match
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit opened
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      (Seq.length c == List.Tot.length l)
    ))
    (fun _ -> seq_list_match c l p)

val seq_list_match_seq_seq_match
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      Seq.length c == List.Tot.length l
    ))

val seq_seq_match_seq_list_match_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit opened
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** pure (
      (Seq.length c == List.Tot.length l)
    ))
    (fun _ -> seq_list_match c l p ** (seq_list_match c l p @==> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)))

val seq_list_match_seq_seq_match_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) ** (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) @==> seq_list_match c l p) ** pure (
      Seq.length c == List.Tot.length l
    ))

val seq_list_match_length
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: stt_ghost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_list_match c l p ** pure (
      Seq.length c == List.Tot.length l
    ))

val seq_list_match_index
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: list t2)
  (i: nat)
: stt_ghost (squash (i < Seq.length s1 /\ List.Tot.length s2 == Seq.length s1)) opened
    (seq_list_match s1 s2 p ** pure (
      (i < Seq.length s1 \/ i < List.Tot.length s2)
    ))
    (fun _ ->
      p (Seq.index s1 i) (List.Tot.index s2 i) **
      (p (Seq.index s1 i) (List.Tot.index s2 i) @==>
        seq_list_match s1 s2 p)
    )

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
  (p: t1 -> t2 -> vprop)
  (x1: t1)
  (x2: option t2)
: Tot vprop
= match x2 with
  | None -> emp
  | Some x2' -> p x1 x2'

val seq_seq_match_item_match_option_elim
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: stt_ghost unit opened
    (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
    (fun _ -> seq_seq_match p s1 s2 i j)

val seq_seq_match_item_match_option_intro
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: stt_ghost unit opened
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)

val seq_seq_match_item_match_option_init
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s: Seq.seq t1)
: stt_ghost unit opened
    emp
    (fun _ -> seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))

val seq_seq_match_upd
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
  (k: nat {
    i <= j /\ j < k
  })
  (x1: t1)
  (x2: t2)
: stt_ghost (squash (j < Seq.length s1 /\ j < Seq.length s2)) opened
    (seq_seq_match p s1 s2 i k ** p x1 x2)
    (fun _ -> 
      seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i k
    )
    
val seq_seq_match_item_match_option_upd
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k
  })
  (x1: t1)
  (x2: t2)
: stt_ghost (squash (j < Seq.length s1 /\ j < Seq.length s2)) opened
    (seq_seq_match (item_match_option p) s1 s2 i k ** p x1 x2)
    (fun _ -> 
      seq_seq_match (item_match_option p) (Seq.upd s1 j x1) (Seq.upd s2 j (Some x2)) i k
    )

val seq_seq_match_item_match_option_index
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq (option t2))
  (i j: nat)
  (k: nat {
    i <= j /\ j < k /\
    (j < Seq.length s2 ==> Some? (Seq.index s2 j))
  })
: stt_ghost (squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j))) opened
    (seq_seq_match (item_match_option p) s1 s2 i k)
    (fun _ -> 
      seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i k **
      p (Seq.index s1 j) (Some?.v (Seq.index s2 j))
    )
