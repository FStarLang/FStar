module Steel.ST.SeqMatch
include Steel.ST.OnRange
open Steel.ST.GenElim

module Seq = FStar.Seq
module SZ = FStar.SizeT

(* `seq_list_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a list of high-level
values. `seq_list_match` is carefully designed to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values.  *)

[@@__reduce__]
let seq_list_match_nil0
  (#t: Type)
  (c: Seq.seq t)
: Tot vprop
= pure (c `Seq.equal` Seq.empty)

[@@__reduce__]
let seq_list_match_cons0
  (#t #t': Type)
  (c: Seq.seq t)
  (l: list t' { Cons? l })
  (item_match: (t -> (v': t' { v' << l }) -> vprop))
  (seq_list_match: (Seq.seq t -> (v': list t') -> (raw_data_item_match: (t -> (v'': t' { v'' << v' }) -> vprop) { v' << l }) ->
vprop))
: Tot vprop
= exists_ (fun (c1: t) -> exists_ (fun (c2: Seq.seq t) ->
    item_match c1 (List.Tot.hd l) `star`
    seq_list_match c2 (List.Tot.tl l) item_match `star`
    pure (c `Seq.equal` Seq.cons c1 c2)
  ))

let rec seq_list_match
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> vprop))
: Tot vprop
  (decreases v)
= if Nil? v
  then seq_list_match_nil0 c
  else seq_list_match_cons0 c v item_match seq_list_match

let seq_list_match_cons_eq
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match: (t -> (v': t' { v' << v }) -> vprop))
: Lemma
  (requires (Cons? v))
  (ensures (
    seq_list_match c v item_match ==
    seq_list_match_cons0 c v item_match seq_list_match
  ))
= let a :: q = v in
  assert_norm (seq_list_match c (a :: q) item_match ==
    seq_list_match_cons0 c (a :: q) item_match seq_list_match
  )

// this one cannot be proven with seq_seq_match because of the << refinement in the type of item_match
let rec seq_list_match_weaken
  (#opened: _)
  (#t #t': Type)
  (c: Seq.seq t)
  (v: list t')
  (item_match1 item_match2: (t -> (v': t' { v' << v }) -> vprop))
  (prf: (
    (#opened: _) ->
    (c': t) ->
    (v': t' { v' << v }) ->
    STGhostT unit opened
      (item_match1 c' v')
      (fun _ -> item_match2 c' v')
  ))
: STGhostT unit opened
    (seq_list_match c v item_match1)
    (fun _ -> seq_list_match c v item_match2)
    (decreases v)
= if Nil? v
  then
    rewrite (seq_list_match c v item_match1) (seq_list_match c v item_match2)
  else begin
    let _ : squash (Cons? v) = () in
    seq_list_match_cons_eq c v item_match1;
    seq_list_match_cons_eq c v item_match2;
    rewrite
      (seq_list_match c v item_match1)
      (seq_list_match_cons0 c v item_match1 seq_list_match);
    let _ = gen_elim () in
    prf _ _;
    seq_list_match_weaken _ (List.Tot.tl v) item_match1 item_match2 prf;
    rewrite
      (seq_list_match_cons0 c v item_match2 seq_list_match)
      (seq_list_match c v item_match2)
  end

(* `seq_seq_match` describes how to match a sequence of low-level
values (the low-level contents of an array) with a sequence of high-level
values. Contrary to `seq_list_match`, `seq_seq_match` is not meant to be usable within
(mutually) recursive definitions of matching functions on the type of
high-level values, because no lemma ensures that `Seq.index s i << s`  *)

let seq_seq_match_item
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i: nat)
: Tot vprop
= if i < Seq.length c && i < Seq.length l
  then
    p (Seq.index c i) (Seq.index l i)
  else
    pure (squash False)

let seq_seq_match_item_tail
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
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

[@@__reduce__]
let seq_seq_match
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq t2)
  (i j: nat)
: Tot vprop
= on_range (seq_seq_match_item p c l) i j

let seq_seq_match_length
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: STGhost unit opened
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match p s1 s2 i j)
    True
    (fun _ -> i <= j /\ (i == j \/ (j <= Seq.length s1 /\ j <= Seq.length s2)))
= on_range_le (seq_seq_match_item p s1 s2) i j;
  if i = j
  then noop ()
  else begin
    let j' = j - 1 in
    if j' < Seq.length s1 && j' < Seq.length s2
    then noop ()
    else begin
      on_range_unsnoc
        (seq_seq_match_item p s1 s2)
        i j' j;
      rewrite
        (seq_seq_match_item p _ _ _)
        (pure (squash False));
      let _ = gen_elim () in
      rewrite
        (seq_seq_match p s1 s2 i j')
        (seq_seq_match p s1 s2 i j) // by contradiction
    end
  end

let seq_seq_match_weaken
  (#opened: _)
  (#t1 #t2: Type)
  (p p': t1 -> t2 -> vprop)
  (w: ((x1: t1) -> (x2: t2) -> STGhostT unit opened
    (p x1 x2) (fun _ -> p' x1 x2)
  ))
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: STGhost unit opened
    (seq_seq_match p c1 c2 i j)
    (fun _ -> seq_seq_match p' c1' c2' i j)
    (i <= j /\ (i == j \/ (
      j <= Seq.length c1 /\ j <= Seq.length c2 /\
      j <= Seq.length c1' /\ j <= Seq.length c2' /\
      Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
      Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
    )))
    (fun _ -> True)
=
  on_range_weaken
    (seq_seq_match_item p c1 c2)
    (seq_seq_match_item p' c1' c2')
    i j
    (fun k ->
       rewrite (seq_seq_match_item p c1 c2 k) (p (Seq.index (Seq.slice c1 i j) (k - i)) (Seq.index (Seq.slice c2 i j) (k - i)));
       w _ _;
       rewrite (p' _ _) (seq_seq_match_item p' c1' c2' k)
    )

let seq_seq_match_weaken_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c1 c1': Seq.seq t1)
  (c2 c2': Seq.seq t2)
  (i j: nat)
: STGhost unit opened
    (seq_seq_match p c1 c2 i j)
    (fun _ -> seq_seq_match p c1' c2' i j `star`
      (seq_seq_match p c1' c2' i j `implies_` seq_seq_match p c1 c2 i j)
    )
    (i <= j /\ (i == j \/ (
      j <= Seq.length c1 /\ j <= Seq.length c2 /\
      j <= Seq.length c1' /\ j <= Seq.length c2' /\
      Seq.slice c1 i j `Seq.equal` Seq.slice c1' i j /\
      Seq.slice c2 i j `Seq.equal` Seq.slice c2' i j
    )))
    (fun _ -> True)
= seq_seq_match_weaken
    p p (fun _ _ -> noop ())
    c1 c1'
    c2 c2'
    i j;
  intro_implies
    (seq_seq_match p c1' c2' i j)
    (seq_seq_match p c1 c2 i j)
    emp
    (fun _ ->
      seq_seq_match_weaken
        p p (fun _ _ -> noop ())
        c1' c1
        c2' c2
        i j
    )

(* Going between `seq_list_match` and `seq_seq_match` *)

let seq_seq_match_tail_elim
  (#t1 #t2: Type)
  (#opened: _)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: Seq.seq (t2))
  (delta: nat {
    delta <= Seq.length c /\
    delta <= Seq.length l
  })
  (i j: nat)
: STGhostT unit opened
    (seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) i j)
    (fun _ -> seq_seq_match p c l (i + delta) (j + delta))
= on_range_le (seq_seq_match_item p _ _) _ _;
  on_range_weaken_and_shift
    (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)))
    (seq_seq_match_item p c l)
    delta
    i j
    (fun k ->
       if k < Seq.length c - delta && k < Seq.length l - delta
       then begin
         seq_seq_match_item_tail p c l delta k;
         rewrite
           (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k)
           (seq_seq_match_item p c l (k + delta))
       end else begin
         rewrite
           (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) k)
           (pure (squash False));
         let _ = gen_elim () in
         rewrite
           emp
           (seq_seq_match_item p c l (k + delta)) // by contradiction
       end
    )
    (i + delta) (j + delta)

let seq_seq_match_tail_intro
  (#t1 #t2: Type)
  (#opened: _)
  (p: t1 -> t2 -> vprop)
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
: STGhostT (squash (i <= j)) opened
    (seq_seq_match p c l i j)
    (fun _ -> seq_seq_match p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (i - delta) (j - delta))
= on_range_le (seq_seq_match_item p _ _) _ _;
  on_range_weaken_and_shift
    (seq_seq_match_item p c l)
    (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)))
    (0 - delta)
    i j
    (fun k ->
      if k < Seq.length c && k < Seq.length l
      then begin
        seq_seq_match_item_tail p c l delta (k - delta);
        rewrite
          (seq_seq_match_item p c l k)
          (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (k + (0 - delta)))
      end else begin
        rewrite
          (seq_seq_match_item p c l k)
          (pure (squash False));
        let _ = gen_elim () in
        rewrite
          emp
          (seq_seq_match_item p (Seq.slice c delta (Seq.length c)) (Seq.slice l delta (Seq.length l)) (k + (0 - delta))) // by contradiction
      end
    )
    (i - delta) (j - delta)

let rec seq_seq_match_seq_list_match
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (fun _ -> seq_list_match c l p)
    (Seq.length c == List.Tot.length l)
    (fun _ -> True)
    (decreases l)
= match l with
  | [] ->
    drop (seq_seq_match p _ _ _ _);
    rewrite
      (seq_list_match_nil0 c)
      (seq_list_match c l p)
  | a :: q ->
    Seq.lemma_seq_of_list_induction (a :: q);
    seq_list_match_cons_eq c l p;
    on_range_uncons
      (seq_seq_match_item p _ _)
      _ 1 _;
    rewrite
      (seq_seq_match_item p _ _ _)
      (p (Seq.head c) (List.Tot.hd l));
    let _ = seq_seq_match_tail_intro
      p _ _ 1 _ _
    in
    rewrite
      (seq_seq_match p _ _ _ _)
      (seq_seq_match p (Seq.tail c) (Seq.seq_of_list (List.Tot.tl l)) 0 (List.Tot.length (List.Tot.tl l)));
    seq_seq_match_seq_list_match p _ (List.Tot.tl l);
    rewrite
      (seq_list_match_cons0 c l p seq_list_match)
      (seq_list_match c l p)

let rec seq_list_match_seq_seq_match
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    True
    (fun _ -> Seq.length c == List.Tot.length l)
    (decreases l)
= match l with
  | [] ->
    rewrite
      (seq_list_match c l p)
      (seq_list_match_nil0 c);
    let _ = gen_elim () in
    on_range_empty
      (seq_seq_match_item p c (Seq.seq_of_list l))
      0
      (List.Tot.length l)
  | a :: q ->
    let _l_nonempty : squash (Cons? l) = () in
    Seq.lemma_seq_of_list_induction (a :: q);
    seq_list_match_cons_eq c l p;
    noop ();
    rewrite
      (seq_list_match c l p)
      (seq_list_match_cons0 c l p seq_list_match);
    let _ = gen_elim () in
    let a' = vpattern (fun a' -> p a' _) in
    let c' = vpattern (fun c' -> seq_list_match c' _ _) in
    Seq.lemma_cons_inj (Seq.head c) a' (Seq.tail c) c';
    assert (a' == Seq.head c);
    assert (c' == Seq.tail c);
    noop ();
    seq_list_match_seq_seq_match p _ _;
    rewrite
      (seq_seq_match p _ _ _ _)
      (seq_seq_match p (Seq.slice c 1 (Seq.length c)) (Seq.slice (Seq.seq_of_list l) 1 (Seq.length (Seq.seq_of_list l))) 0 (List.Tot.length (List.Tot.tl l)));
    let _ = seq_seq_match_tail_elim
      p c (Seq.seq_of_list l) 1 0 (List.Tot.length (List.Tot.tl l))
    in
    rewrite
      (seq_seq_match p _ _ _ _)
      (seq_seq_match p c (Seq.seq_of_list l) 1 (List.Tot.length l));
    rewrite
      (p _ _)
      (seq_seq_match_item p c (Seq.seq_of_list l) 0);
    on_range_cons
      (seq_seq_match_item p _ _)
      0 1 (List.Tot.length l)

let seq_seq_match_seq_list_match_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (fun _ -> seq_list_match c l p `star` (seq_list_match c l p `implies_` seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l)))
    (Seq.length c == List.Tot.length l)
    (fun _ -> True)
= seq_seq_match_seq_list_match p c l;
  intro_implies
    (seq_list_match c l p)
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    emp
    (fun _ -> seq_list_match_seq_seq_match p c l)

let seq_list_match_seq_seq_match_with_implies
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) `star` (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l) `implies_` seq_list_match c l p))
    True
    (fun _ -> Seq.length c == List.Tot.length l)
= seq_list_match_seq_seq_match p c l;
  intro_implies
    (seq_seq_match p c (Seq.seq_of_list l) 0 (List.Tot.length l))
    (seq_list_match c l p)
    emp
    (fun _ -> seq_seq_match_seq_list_match p c l)

let seq_list_match_length
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (c: Seq.seq t1)
  (l: list t2)
: STGhost unit opened
    (seq_list_match c l p)
    (fun _ -> seq_list_match c l p)
    True
    (fun _ -> Seq.length c == List.Tot.length l)
= seq_list_match_seq_seq_match_with_implies p c l;
  seq_seq_match_length p _ _ _ _;
  elim_implies
    (seq_seq_match p _ _ _ _)
    (seq_list_match c l p)

let seq_list_match_index
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: list t2)
  (i: nat)
: STGhost (squash (i < Seq.length s1 /\ List.Tot.length s2 == Seq.length s1)) opened
    (seq_list_match s1 s2 p)
    (fun _ ->
      p (Seq.index s1 i) (List.Tot.index s2 i) `star`
      (p (Seq.index s1 i) (List.Tot.index s2 i) `implies_`
        seq_list_match s1 s2 p)
    )
    (i < Seq.length s1 \/ i < List.Tot.length s2)
    (fun _ -> True)
= seq_list_match_seq_seq_match_with_implies p s1 s2;
  let res : squash (i < Seq.length s1 /\ List.Tot.length s2 == Seq.length s1) = () in
  on_range_focus (seq_seq_match_item p s1 (Seq.seq_of_list s2)) 0 i (List.Tot.length s2);
  rewrite_with_implies
    (seq_seq_match_item p _ _ _)
    (p (Seq.index s1 i) (List.Tot.index s2 i));
  implies_trans
    (p (Seq.index s1 i) (List.Tot.index s2 i))
    (seq_seq_match_item p _ _ _)
    (seq_seq_match p s1 (Seq.seq_of_list s2) 0 (List.Tot.length s2));
  implies_trans
    (p (Seq.index s1 i) (List.Tot.index s2 i))
    (seq_seq_match p s1 (Seq.seq_of_list s2) 0 (List.Tot.length s2))
    (seq_list_match s1 s2 p);
  res

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

let seq_seq_match_item_match_option_elim
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: STGhostT unit opened
    (seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
    (fun _ -> seq_seq_match p s1 s2 i j)
= on_range_weaken
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2))
    (seq_seq_match_item p s1 s2)
    i j
    (fun k ->
      rewrite
        (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2) k)
        (seq_seq_match_item p s1 s2 k)
    )

let seq_seq_match_item_match_option_intro
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s1: Seq.seq t1)
  (s2: Seq.seq t2)
  (i j: nat)
: STGhostT unit opened
    (seq_seq_match p s1 s2 i j)
    (fun _ -> seq_seq_match (item_match_option p) s1 (seq_map Some s2) i j)
= on_range_weaken
    (seq_seq_match_item p s1 s2)
    (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2))
    i j
    (fun k ->
      rewrite
        (seq_seq_match_item p s1 s2 k)
        (seq_seq_match_item (item_match_option p) s1 (seq_map Some s2) k)
    )

let rec seq_seq_match_item_match_option_init
  (#opened: _)
  (#t1 #t2: Type)
  (p: t1 -> t2 -> vprop)
  (s: Seq.seq t1)
: STGhostT unit opened
    emp
    (fun _ -> seq_seq_match (item_match_option p) s (Seq.create (Seq.length s) None) 0 (Seq.length s))
    (decreases (Seq.length s))
= if Seq.length s = 0
  then
    on_range_empty (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None)) 0 (Seq.length s)
  else begin
    seq_seq_match_item_match_option_init p (Seq.tail s);
    on_range_weaken_and_shift
      (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None))
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None))
      1
      0
      (Seq.length (Seq.tail s))
      (fun k ->
        rewrite
          (seq_seq_match_item (item_match_option p) (Seq.tail s) (Seq.create (Seq.length (Seq.tail s)) None) k)
          (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None) (k + 1))
      )
      1
      (Seq.length s);
    rewrite
      emp
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None) 0);
    on_range_cons
      (seq_seq_match_item (item_match_option p) s (Seq.create (Seq.length s) None))
      0
      1
      (Seq.length s)
  end

let seq_seq_match_upd
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
: STGhostT (squash (j < Seq.length s1 /\ j < Seq.length s2)) opened
    (seq_seq_match p s1 s2 i k `star` p x1 x2)
    (fun _ -> 
      seq_seq_match p (Seq.upd s1 j x1) (Seq.upd s2 j x2) i k
    )
= seq_seq_match_length p s1 s2 i k;
  on_range_get
    (seq_seq_match_item p s1 s2)
    i j (j + 1) k;
  let res : squash (j < Seq.length s1 /\ j < Seq.length s2) = () in
  drop (seq_seq_match_item p s1 s2 j);
  rewrite
    (p x1 x2)
    (seq_seq_match_item p (Seq.upd s1 j x1) (Seq.upd s2 j x2) j);
  seq_seq_match_weaken
    p p (fun _ _ -> noop ())
    s1 (Seq.upd s1 j x1)
    s2 (Seq.upd s2 j x2)
    i j;
  seq_seq_match_weaken
    p p (fun _ _ -> noop ())
    s1 (Seq.upd s1 j x1)
    s2 (Seq.upd s2 j x2)
    (j + 1) k;
  on_range_put
    (seq_seq_match_item p (Seq.upd s1 j x1) (Seq.upd s2 j x2))
    i j j (j + 1) k;
  res
    
let seq_seq_match_item_match_option_upd
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
: STGhostT (squash (j < Seq.length s1 /\ j < Seq.length s2)) opened
    (seq_seq_match (item_match_option p) s1 s2 i k `star` p x1 x2)
    (fun _ -> 
      seq_seq_match (item_match_option p) (Seq.upd s1 j x1) (Seq.upd s2 j (Some x2)) i k
    )
= rewrite
    (p x1 x2)
    (item_match_option p x1 (Some x2));
  seq_seq_match_upd (item_match_option p) s1 s2 i j k x1 (Some x2)

let seq_seq_match_item_match_option_index
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
: STGhostT (squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j))) opened
    (seq_seq_match (item_match_option p) s1 s2 i k)
    (fun _ -> 
      seq_seq_match (item_match_option p) s1 (Seq.upd s2 j None) i k `star`
      p (Seq.index s1 j) (Some?.v (Seq.index s2 j))
    )
= seq_seq_match_length (item_match_option p) s1 s2 i k;
  on_range_get
    (seq_seq_match_item (item_match_option p) s1 s2)
    i j (j + 1) k;
  let res : squash (j < Seq.length s1 /\ j < Seq.length s2 /\ Some? (Seq.index s2 j)) = () in
  rewrite
    (seq_seq_match_item (item_match_option p) s1 s2 j)
    (p (Seq.index s1 j) (Some?.v (Seq.index s2 j)));
  rewrite
    emp
    (seq_seq_match_item (item_match_option p) s1 (Seq.upd s2 j None) j);
  seq_seq_match_weaken
    (item_match_option p) (item_match_option p) (fun _ _ -> noop ())
    s1 s1
    s2 (Seq.upd s2 j None)
    i j;
  seq_seq_match_weaken
    (item_match_option p) (item_match_option p) (fun _ _ -> noop ())
    s1 s1
    s2 (Seq.upd s2 j None)
    (j + 1) k;
  on_range_put
    (seq_seq_match_item (item_match_option p) s1 (Seq.upd s2 j None))
    i j j (j + 1) k;
  res
