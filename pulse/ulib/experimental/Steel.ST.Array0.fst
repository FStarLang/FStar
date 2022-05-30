module Steel.ST.Array0

/// Lifting a value of universe 0 to universe 1. We could use
/// FStar.Universe, but that module is not tailored to inlining at
/// extraction.

[@@erasable]
noeq
type dummy_universe1 : Type u#1 = | DummyU1

/// This type definition supports inlining, contrary to the custom
/// type defined in FStar.Universe.fst.
inline_for_extraction
[@@ noextract_to "krml"]
let raise_t (t: Type0) : Type u#1 = (t & dummy_universe1)

inline_for_extraction
[@@noextract_to "krml"]
let raise (#t: Type) (x: t) : Tot (raise_t t) = (x, DummyU1)

inline_for_extraction
[@@noextract_to "krml"]
let lower (#t: Type) (x: raise_t t) : Tot t =
  match x with (x', _) -> x'

/// A map operation on sequences. Here we only need Ghost versions,
/// because such sequences are only used in vprops or with their
/// selectors.

let rec seq_map
  (#t: Type u#a)
  (#t' : Type u#b)
  (f: (t -> GTot t'))
  (s: Seq.seq t)
: Ghost (Seq.seq t')
  (requires True)
  (ensures (fun s' ->
    Seq.length s' == Seq.length s /\
    (forall i . {:pattern (Seq.index s' i)} Seq.index s' i == f (Seq.index s i))
  ))
  (decreases (Seq.length s))
= if Seq.length s = 0
  then Seq.empty
  else Seq.cons (f (Seq.index s 0)) (seq_map f (Seq.slice s 1 (Seq.length s)))

let seq_map_append
  (#t: Type u#a)
  (#t': Type u#b)
  (f: (t -> GTot t'))
  (s1 s2: Seq.seq t)
: Lemma
  (seq_map f (s1 `Seq.append` s2) `Seq.equal` (seq_map f s1 `Seq.append` seq_map f s2))
= ()

let seq_map_raise_inj
  (#elt: Type0)
  (s1 s2: Seq.seq elt)
: Lemma
  (requires (seq_map raise s1 == seq_map raise s2))
  (ensures (s1 == s2))
  [SMTPat (seq_map raise s1); SMTPat (seq_map raise s2)]
= assert (seq_map lower (seq_map raise s1) `Seq.equal` s1);
  assert (seq_map lower (seq_map raise s2) `Seq.equal` s2)

/// Implementation of the interface

/// base, ptr, array, pts_to

module H = Steel.ST.HigherArray0

let base_t elt = H.base_t (raise_t elt)
let base_len b = H.base_len b

let ptr elt = H.ptr (raise_t elt)
let base p = H.base p
let offset p = H.offset p
let ptr_base_offset_inj p1 p2 = H.ptr_base_offset_inj p1 p2

let pts_to a p s = H.pts_to a p (seq_map raise s)

let pts_to_length a p s =
  H.pts_to_length a p _

let pts_to_inj a p1 s1 p2 s2 =
  H.pts_to_inj a p1 (seq_map raise s1) p2 (seq_map raise s2)

/// Non-selector operations.

let malloc x n =
  let res = H.malloc (raise x) n in
  assert (seq_map raise (Seq.create (U32.v n) x) `Seq.equal` Seq.create (U32.v n) (raise x));
  rewrite
    (H.pts_to res _ _)
    (pts_to res _ _);
  return res

let free #_ #s x =
  rewrite
    (pts_to x _ _)
    (H.pts_to x P.full_perm (seq_map raise s));
  H.free x

let share
  #_ #_ #x a p p1 p2
= rewrite
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise x));
  H.share a p p1 p2;
  rewrite
    (H.pts_to a p1 _)
    (pts_to a p1 x);
  rewrite
    (H.pts_to a p2 _)
    (pts_to a p2 x)

let gather
  #_ #_ a #x1 p1 #x2 p2
= rewrite
    (pts_to a p1 _)
    (H.pts_to a p1 (seq_map raise x1));
  rewrite
    (pts_to a p2 _)
    (H.pts_to a p2 (seq_map raise x2));
  H.gather a p1 p2;
  rewrite
    (H.pts_to a _ _)
    (pts_to _ _ _)

let index #_ #p a #s i =
  rewrite
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise s));
  let res = H.index a i in
  rewrite
    (H.pts_to _ _ _)
    (pts_to _ _ _);
  return (lower res)

let upd #_ a #s i v =
  rewrite
    (pts_to a _ _)
    (H.pts_to a P.full_perm (seq_map raise s));
  H.upd a i (raise v);
  assert (seq_map raise (Seq.upd s (U32.v i) v) `Seq.equal` Seq.upd (seq_map raise s) (U32.v i) (raise v));
  rewrite
    (H.pts_to _ _ _)
    (pts_to _ _ _)

let ghost_join
  #_ #_ #x1 #x2 #p a1 a2 h
= rewrite
    (pts_to a1 _ _)
    (H.pts_to a1 p (seq_map raise x1));
  rewrite
    (pts_to a2 _ _)
    (H.pts_to a2 p (seq_map raise x2));
  H.ghost_join a1 a2 h;
  assert (seq_map raise (x1 `Seq.append` x2) `Seq.equal` (seq_map raise x1 `Seq.append` seq_map raise x2));
  rewrite
    (H.pts_to _ _ _)
    (H.pts_to (merge a1 a2) p (seq_map raise (x1 `Seq.append` x2)));
  rewrite
    (H.pts_to _ _ _)
    (pts_to (merge a1 a2) _ _)

let ptr_shift p off = H.ptr_shift p off

let ghost_split
  #_ #_ #x #p a i
=
  rewrite
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise x));
  H.ghost_split a i;
  assert (seq_map raise (Seq.slice x 0 (U32.v i)) `Seq.equal` Seq.slice (seq_map raise x) 0 (U32.v i));
  rewrite
    (H.pts_to (H.split_l a i) _ _)
    (H.pts_to (split_l a i) p (seq_map raise (Seq.slice x 0 (U32.v i))));
  rewrite
    (H.pts_to (split_l a i) _ _)
    (pts_to (split_l a i) _ _);
  assert (seq_map raise (Seq.slice x (U32.v i) (Seq.length x)) `Seq.equal` Seq.slice (seq_map raise x) (U32.v i) (Seq.length (seq_map raise x)));
  Seq.lemma_split x (U32.v i);
  rewrite
    (H.pts_to (H.split_r a i) _ _)
    (H.pts_to (split_r a i) p (seq_map raise (Seq.slice x (U32.v i) (Seq.length x))));
  rewrite
    (H.pts_to (split_r a i) _ _)
    (pts_to (split_r a i) _ _)
