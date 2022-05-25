module Steel.Array0

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

module H = Steel.HigherArray0

let base_t elt = H.base_t (raise_t elt)
let base_len b = H.base_len b

let ptr elt = H.ptr (raise_t elt)
let base p = H.base p
let offset p = H.offset p
let ptr_base_offset_inj p1 p2 = H.ptr_base_offset_inj p1 p2

let pts_to a p s = H.pts_to a p (seq_map raise s)

let pts_to_length a p s =
  H.pts_to_length a p _

/// varrayp and its selector
/// TODO: generalize the following method of defining a selector for an injective pts_to-style vprop

let pts_to'
  (#elt: Type0) (a: array elt)
  (p: P.perm)
  (s: Seq.lseq elt (length a))
: Tot slprop
= hp_of (pts_to a p s)

let varrayp_hp a p =
  Steel.Memory.h_exists (pts_to' a p)

let varrayp_sel' 
  (#elt: Type) (a: array elt) (p: P.perm)
: Tot (selector' (Seq.lseq elt (length a)) (varrayp_hp a p))
= fun m -> id_elim_exists (pts_to' a p) m

let varrayp_sel_depends_only_on
  (#elt: Type)
  (a: array elt)
  (p: P.perm)
  (m0: Steel.Memory.hmem (varrayp_hp a p))
  (m1: mem { disjoint m0 m1 })
: Lemma
  (
    varrayp_sel' a p m0 == varrayp_sel' a p (join m0 m1)
  )
  [SMTPat (varrayp_sel' a p (join m0 m1))]
= H.pts_to_inj a p (seq_map raise (varrayp_sel' a p m0)) p (seq_map raise (varrayp_sel' a p (join m0 m1))) (join m0 m1)

let varrayp_sel_depends_only_on_core
  (#elt: Type)
  (a: array elt)
  (p: P.perm)
  (m0: Steel.Memory.hmem (varrayp_hp a p))
: Lemma
  (
    varrayp_sel' a p m0 == varrayp_sel' a p (core_mem m0)
  )
  [SMTPat (varrayp_sel' a p (core_mem m0))]
= H.pts_to_inj a p (seq_map raise (varrayp_sel' a p m0)) p (seq_map raise (varrayp_sel' a p (core_mem m0))) m0

let varrayp_sel a p = varrayp_sel' a p

let intro_varrayp
  a p s
=
  change_equal_slprop
    (pts_to a p s)
    (H.pts_to a p (seq_map raise s));
  H.pts_to_length a p _;
  change_slprop_rel
    (H.pts_to a p (seq_map raise s))
    (varrayp a p)
    (fun _ s' -> s `Seq.equal` s')
    (fun m ->
      intro_h_exists s (pts_to' a p) m;
      let s' = varrayp_sel' a p m in
      H.pts_to_inj a p (seq_map raise s) p (seq_map raise s') m
    )

let elim_varrayp
  #_ #elt a p
=
  let s0 = gget (varrayp a p) in
  let refinement (s: Seq.lseq elt (length a)) : Tot prop = s == Ghost.reveal s0 in
  let s1 : Ghost.erased (Seq.seq elt) = Ghost.reveal s0 in
  intro_vrefine (varrayp a p) refinement;
  rewrite_slprop
    (varrayp a p `vrefine` refinement)
    (pts_to a p s1)
    (fun m ->
      interp_vrefine_hp (varrayp a p) refinement m
      // injectivity is not needed, because the return value of the
      // selector is exactly the witness of exists_
    );
  s1

/// Non-selector operations. (Their selector versions are defined in the interface)

let alloc_pt x n =
  let res = H.alloc (raise x) n in
  assert (seq_map raise (Seq.create (U32.v n) x) `Seq.equal` Seq.create (U32.v n) (raise x));
  change_equal_slprop
    (H.pts_to res _ _)
    (pts_to res _ _);
  return res

let free_pt #_ #s x =
  change_equal_slprop
    (pts_to x _ _)
    (H.pts_to x P.full_perm (seq_map raise s));
  H.free x

let share_pt
  #_ #_ #x a p p1 p2
= change_equal_slprop
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise x));
  H.share a p p1 p2;
  change_equal_slprop
    (H.pts_to a p1 _)
    (pts_to a p1 x);
  change_equal_slprop
    (H.pts_to a p2 _)
    (pts_to a p2 x)

let gather_pt 
  #_ #_ a #x1 p1 #x2 p2
= change_equal_slprop
    (pts_to a p1 _)
    (H.pts_to a p1 (seq_map raise x1));
  change_equal_slprop
    (pts_to a p2 _)
    (H.pts_to a p2 (seq_map raise x2));
  H.gather a p1 p2;
  change_equal_slprop
    (H.pts_to a _ _)
    (pts_to _ _ _)

let index_pt #_ #p a #s i =
  change_equal_slprop
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise s));
  let res = H.index a i in
  change_equal_slprop
    (H.pts_to _ _ _)
    (pts_to _ _ _);
  return (lower res)

let upd_pt #_ a #s i sq v =
  change_equal_slprop
    (pts_to a _ _)
    (H.pts_to a P.full_perm (seq_map raise s));
  H.upd a i () (raise v);
  assert (seq_map raise (Seq.upd s (U32.v i) v) `Seq.equal` Seq.upd (seq_map raise s) (U32.v i) (raise v));
  change_equal_slprop
    (H.pts_to _ _ _)
    (pts_to _ _ _)

let ghost_join_pt
  #_ #_ #x1 #x2 #p a1 a2 h
= change_equal_slprop
    (pts_to a1 _ _)
    (H.pts_to a1 p (seq_map raise x1));
  change_equal_slprop
    (pts_to a2 _ _)
    (H.pts_to a2 p (seq_map raise x2));
  H.ghost_join a1 a2 h;
  assert (seq_map raise (x1 `Seq.append` x2) `Seq.equal` (seq_map raise x1 `Seq.append` seq_map raise x2));
  change_equal_slprop
    (H.pts_to _ _ _)
    (H.pts_to (merge a1 a2) p (seq_map raise (x1 `Seq.append` x2)));
  change_equal_slprop
    (H.pts_to _ _ _)
    (pts_to (merge a1 a2) _ _)

let ptr_shift p off = H.ptr_shift p off

let ghost_split_pt
  #_ #_ #x #p a i
=
  change_equal_slprop
    (pts_to a _ _)
    (H.pts_to a p (seq_map raise x));
  H.ghost_split a i;
  assert (seq_map raise (Seq.slice x 0 (U32.v i)) `Seq.equal` Seq.slice (seq_map raise x) 0 (U32.v i));
  change_equal_slprop
    (H.pts_to (H.split_l a i) _ _)
    (H.pts_to (split_l a i) p (seq_map raise (Seq.slice x 0 (U32.v i))));
  change_equal_slprop
    (H.pts_to (split_l a i) _ _)
    (pts_to (split_l a i) _ _);
  assert (seq_map raise (Seq.slice x (U32.v i) (Seq.length x)) `Seq.equal` Seq.slice (seq_map raise x) (U32.v i) (Seq.length (seq_map raise x)));
  Seq.lemma_split x (U32.v i);
  change_equal_slprop
    (H.pts_to (H.split_r a i) _ _)
    (H.pts_to (split_r a i) p (seq_map raise (Seq.slice x (U32.v i) (Seq.length x))));
  change_equal_slprop
    (H.pts_to (split_r a i) _ _)
    (pts_to (split_r a i) _ _)
