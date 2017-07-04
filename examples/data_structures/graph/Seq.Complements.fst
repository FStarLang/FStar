module Seq.Complements

open FStar.Seq
open FStar.Classical
open FStar.Fin

let _in (s:seq 'a) = k:nat{k < length s}
let ( @^ ) (s:seq 'a) (i:_in s) : 'a = index s i
let snoc (s:seq 'a) (x:'a) = s `append` (create 1 x)


(** Searching the index of an element in a seq **)

let rec index_of_aux (#a:eqtype) (e:a) (s : seq a) (i : _in s)
 : Pure (option (_in s))
  (requires (count e (slice s 0 i) == 0))
  (ensures fun i' -> match i' with | None -> count e s == 0 | Some i0 -> s @^ i0 == e)
  (decreases (length s - i))
= if s @^ i = e
  then Some i
  else begin
    lemma_eq_elim (slice s 0 (i + 1)) (append (slice s 0 i) (slice s i (i + 1)));
    lemma_append_count_aux e (slice s 0 i) (slice s i (i + 1));
    assert(count e (slice s 0 (i+1)) == 0);
    if i = length s - 1 then
      (
        lemma_eq_elim s (slice s 0 (length s));
        assert (slice s 0 (length s) == s) ; None
      )
    else
      index_of_aux e s (i + 1)
  end

let index_of(#a:eqtype) (e:a) (s : seq a)
 : Pure (option (_in s))
  (requires (True))
  (ensures fun i' -> match i' with | None -> count e s == 0 | Some i0 -> s @^ i0 == e)
  = if length s = 0 then None else index_of_aux e s 0

let rec index_of_l_aux (#a:Type) (f:a -> bool) (s:seq a) (i:_in s)
  : Tot (option (_in s)) (decreases (length s - i))
= if f (s @^ i) then Some i else if i = length s - 1 then None else index_of_l_aux #a f s (i+1)

let index_of_l (#a:Type) (f:a -> bool) (s:seq a) : option (_in s) =
  if length s = 0 then None else index_of_l_aux #a f s (0 <: _in s)

let rec index_of_l_aux_spec (#a:Type) (f:a -> bool) (s:seq a) (i:_in s) :
  Lemma (requires (forall (j:_in s{j < i}). not (f (s @^ j))))
    (ensures (let r = index_of_l_aux f s i in
    (forall (i:_in s). (~(Some? r) \/ i < Some?.v r) ==>  not (f (s @^ i))) /\
      (Some? r ==> f (s @^ Some?.v r))))
    (decreases (length s - i))
= if f (s @^ i) then () else if i = length s - 1 then () else index_of_l_aux_spec #a f s (i+1)

let rec index_of_l_spec (#a:Type) (f:a -> bool) (s:seq a) :
    Lemma (let r = index_of_l f s in
    (forall (i:_in s). (None? r \/ i < Some?.v r) ==> not (f (s @^ i))) /\
      (Some? r ==> f (s @^ Some?.v r)))
= if length s = 0 then ()
  else index_of_l_aux_spec f s 0


(** Lemmas on count **)

let rec none_count_zero (#a:eqtype) (e:a) (s:seq a)
  : Lemma (requires (forall (i:_in s). not (e = s @^ i))) (ensures (count e s == 0)) (decreases (length s))
= if length s = 0 then ()
  else
    let s' = tail s in
    assert (not (e = s @^ 0)) ;
    assert (forall (i:_in s'). not (e = s @^ (i+1))) ;
    none_count_zero #a e s'

let rec count_zero_none_aux (#a:eqtype) (e:a) (s:seq a) (i : _in s)
  : Lemma (requires (count e s == 0) /\ (forall (i: k:nat{k< i}) . not (e = s @^ i)))
  (ensures (forall (i:_in s). not (e = s @^ i))) (decreases (length
s - i))
= lemma_count_slice s i;
  if length s - i <= 1 then ()
  else count_zero_none_aux #a e s (i + 1)

let count_zero_none (#a:eqtype) (e:a) (s:seq a)
 : Lemma (requires (count e s == 0)) (ensures (forall (i:_in s). not (e = s @^ i)))
 = if length s = 0 then () else count_zero_none_aux #a e s 0

let index_of_l_count (#a:eqtype) (e:a) (s:seq a)
  : Lemma (match index_of_l (fun x -> x = e) s with | None -> count e s == 0 | Some i0 -> s @^ i0 = e)
= let f x = x = e in
  index_of_l_spec f s ;
  match index_of_l f s with
  | None -> none_count_zero e s
  | Some i0 -> ()


(** Disjointness **)

let disjoint (#a:Type) (s1:seq a) (s2:seq a) = forall (i:_in s1)(j:_in s2). ~(s1 @^ i == s2 @^ j)


let disjoint_implies_count_zero (#a:eqtype) (s1 s2:seq a)
 : Lemma (requires (disjoint s1 s2))
  (ensures (forall (i':_in s1). count (s1 @^ i') s2 == 0))
=
  let disjoint_implies_count_zero_aux (#a:eqtype) (s1 s2:seq a)
    (w:squash(disjoint s1 s2)) (i:_in s1)
    : Lemma (count (s1 @^ i) s2 == 0) =
    FStar.Squash.give_proof w ;
    assert(forall (j:_in s2). ~(s1 @^ i == s2 @^ j));
    none_count_zero (s1 @^ i) s2
  in
  forall_intro (disjoint_implies_count_zero_aux #a s1 s2
    (FStar.Squash.get_proof (disjoint s1 s2)))


let lemma_disjoint_slice (#a:Type) (s1 s2:seq a) (i j : k:nat{k <= length s2})
  : Lemma (requires (i <= j /\ disjoint s1 s2))
    (ensures (i <= j /\ disjoint s1 (slice s2 i j)))
  = let s2' = slice s2 i j in
    assert (forall (i0: _in s2') (k:_in s1). ~(s2 @^ (i+i0) == s1 @^ k))

let disjoint_not_eq_head (#a:Type) (s1: s:seq a{length s >= 1}) (s2:seq a)
 : Lemma (requires (disjoint s1 s2))
   (ensures (forall (j:_in s2). ~(head s1 == s2 @^ j)))
   = assert (forall (j:_in s2). ~(s1 @^ 0 == s2 @^ j))

let lemma_disjoint_append (#a:Type) (s1 s2 s3: seq a)
  : Lemma (requires (disjoint s1 s3) /\ (disjoint s2 s3))
    (ensures (disjoint (append s1 s2) s3))
=
  assert (forall (i:_in (append s1 s2)) (j:_in s3).
    (i < length s1 ==> ~(s1 @^ (i <: nat) == s3 @^ j)) /\
    (i >= length s1 ==> (let i' = i - length s1 in i' < length s2 /\ ~(s2 @^ i' == s3 @^ j)))
    )

(* Mapping *)

abstract
let map (s:seq 'a) (f : 'a -> 'b) : seq 'b = init (length s) (fun i -> f (s @^ i))

let map_lemma (s:seq 'a) (f:'a -> 'b) : Lemma (let s' = map #'a #'b s f in length s' == length s /\ (forall (i:_in s'). s' @^ i == f (s @^ (i <: nat)))) = ()



let injective (p:seq 'a) = forall (i j : _in p) . p @^ i == p @^ j ==> i == j

let injective_map (#a #b:Type) (f: a -> b) (s:seq a)
  : Lemma (requires (injective s /\ (forall (i j:_in s). f (s @^ i) == f (s @^ j) ==> s @^ i == s@^ j)))
    (ensures (injective (map s f)))
= map_lemma s f

let rec injective_length_lemma (#n:nat) (s:seq (fin n))
  : Lemma (requires (injective s)) (ensures (length s <= n)) (decreases n)
= if length s = 0 then ()
  else if n = 1 then
    assert (s @^ 0 == 0 /\ (length s > 1 ==> s @^ 1 == 0))
  else
    let x = head s in
    let xs = tail s in
    assert (forall (i:_in xs). ~(s @^ (i+1) == s @^ 0)) ;
    assert (forall (i:_in xs). ~(xs @^ i == x)) ;
    let f (k:fin n) : fin (n-1) = if k > x then k - 1 else if k < x then (k <: nat) else 0 <: fin (n-1) in
    assert (forall (k1 k2:fin n). k1 <> x /\ k2 <> x /\ f k1 == f k2 ==> k1 == k2) ;
    injective_map f xs ;
    injective_length_lemma #(n-1) (map xs f)
