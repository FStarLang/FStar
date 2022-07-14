module Steel.Array0

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
include Steel.ST.Array0

/// C arrays of universe 0 elements, with selectors.


/// Non-selector style universe 0 arrays are defined in Steel.ST, but
/// we want to transparently reuse the corresponding operations in
/// Steel, so we need to bring in the lift from Steel.ST to Steel,
/// defined in Steel.ST.Coercions.
module STC = Steel.ST.Coercions

module P = Steel.FractionalPermission
module U32 = FStar.UInt32
module A = Steel.ST.Array0

/// A selector version

/// Separation logic predicate indicating the validity of the array in the current memory, p is the fractional permission on the array
val varrayp_hp
  (#elt: Type0) (a: array elt) (p: P.perm)
: Tot (slprop u#1)

/// Selector for Steel arrays. It returns the contents in memory of the array
val varrayp_sel
  (#elt: Type) (a: array elt) (p: P.perm)
: Tot (selector (Seq.lseq elt (length a)) (varrayp_hp a p))

/// Combining the elements above to create an array vprop
[@__steel_reduce__] // for t_of
let varrayp
  (#elt: Type) (a: array elt) (p: P.perm)
: Tot vprop
= VUnit ({
    hp = varrayp_hp a p;
    t = _;
    sel = varrayp_sel a p;
  })

/// A wrapper to access an array selector more easily.
/// Ensuring that the corresponding array vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
[@@ __steel_reduce__]
let aselp (#elt: Type) (#vp: vprop) (a: array elt) (p: P.perm)
  (h: rmem vp { FStar.Tactics.with_tactic selector_tactic (can_be_split vp (varrayp a p) /\ True) })
: GTot (Seq.lseq elt (length a))
= h (varrayp a p)

[@@__steel_reduce__; __reduce__]
let varray
  (#elt: Type) (a: array elt)
: Tot vprop
= varrayp a P.full_perm

[@@ __steel_reduce__]
let asel (#elt: Type) (#vp: vprop) (a: array elt)
  (h: rmem vp { FStar.Tactics.with_tactic selector_tactic (can_be_split vp (varray a) /\ True) })
: GTot (Seq.lseq elt (length a))
= h (varray a)

/// Converting a `pts_to` to a `varrayp`
val intro_varrayp
  (#opened: _) (#elt: Type) (a: array elt) (p: P.perm) (s: Seq.seq elt)
: SteelGhost unit opened
    (pts_to a p s)
    (fun _ -> varrayp a p)
    (fun _ -> True)
    (fun _ _ h' ->
      aselp a p h' == s
    )

let intro_varray
  (#opened: _) (#elt: Type) (a: array elt) (s: Seq.seq elt)
: SteelGhost unit opened
    (pts_to a P.full_perm s)
    (fun _ -> varray a)
    (fun _ -> True)
    (fun _ _ h' ->
      asel a h' == s
    )
= intro_varrayp _ _ _

/// Converting a `varrayp` into a `pts_to`
val elim_varrayp
  (#opened: _) (#elt: Type) (a: array elt) (p: P.perm)
: SteelGhost (Ghost.erased (Seq.seq elt)) opened
    (varrayp a p)
    (fun res -> pts_to a p res)
    (fun _ -> True)
    (fun h res _ ->
      Ghost.reveal res == aselp a p h
    )

let elim_varray
  (#opened: _) (#elt: Type) (a: array elt)
: SteelGhost (Ghost.erased (Seq.seq elt)) opened
    (varray a)
    (fun res -> pts_to a P.full_perm res)
    (fun _ -> True)
    (fun h res _ ->
      Ghost.reveal res == asel a h
    )
= elim_varrayp _ _

/// Allocating a new array of size n, where each cell is initialized
/// with value x. We define the non-selector version of this operation
/// (and others) with a _pt suffix in the name.
inline_for_extraction
[@@noextract_to "krml"]
let malloc
  (#elt: Type)
  (x: elt)
  (n: U32.t)
: Steel (array elt)
    emp
    (fun a -> varray a)
    (fun _ -> True)
    (fun _ a h' ->
      length a == U32.v n /\
      is_full_array a /\
      asel a h' == Seq.create (U32.v n) x
    )
= let res = A.malloc x n in
  intro_varray res _;
  return res

/// Freeing a full array. 
inline_for_extraction
[@@ noextract_to "krml";
    warn_on_use "Steel.Array0.free is currently unsound in the presence of zero-size subarrays, have you collected them all?"]
let free
  (#elt: Type)
  (a: array elt)
: Steel unit
    (varray a)
    (fun _ -> emp)
    (fun _ ->
      is_full_array a
    )
    (fun _ _ _ -> True)
= let _ = elim_varray a in
  A.free a

/// Sharing and gathering permissions on an array. Those only
/// manipulate permissions, so they are nothing more than stateful
/// lemmas.
inline_for_extraction // FIXME: F* bug. This attribute is not necessary here, but if removed, F* complains about duplicate declaration and definition
let share
  (#opened: _)
  (#elt: Type)
  (a: array elt)
  (p p1 p2: P.perm)
: SteelGhost unit opened
    (varrayp a p)
    (fun _ -> varrayp a p1 `star` varrayp a p2)
    (fun _ -> p == p1 `P.sum_perm` p2)
    (fun h _ h' ->
      aselp a p1 h' == aselp a p h /\
      aselp a p2 h' == aselp a p h
    )
= let _ = elim_varrayp a p in
  A.share a p p1 p2;
  intro_varrayp a p1 _;
  intro_varrayp a p2 _

inline_for_extraction // same here
let gather
  (#opened: _)
  (#elt: Type)
  (a: array elt)
  (p1: P.perm)
  (p2: P.perm)
: SteelGhost unit opened
    (varrayp a p1 `star` varrayp a p2)
    (fun _ -> varrayp a (p1 `P.sum_perm` p2))
    (fun _ -> True)
    (fun h _ h' ->
      aselp a (p1 `P.sum_perm` p2) h' == aselp a p1 h /\
      aselp a (p1 `P.sum_perm` p2) h' == aselp a p2 h
    )
= let _ = elim_varrayp a p1 in
  let _ = elim_varrayp a p2 in
  A.gather a p1 p2;
  intro_varrayp a _ _

/// Reading the i-th element of an array a.
/// TODO: we should also provide an atomic version for small types.
inline_for_extraction
[@@noextract_to "krml"]
let index
  (#t: Type) (#p: P.perm)
  (a: array t)
  (i: U32.t)
: Steel t
    (varrayp a p)
    (fun _ -> varrayp a p)
    (fun _ -> U32.v i < length a)
    (fun h res h' ->
      let s = aselp a p h in
      aselp a p h' == s /\
      U32.v i < Seq.length s /\
      res == Seq.index s (U32.v i)
    )
= let _ = elim_varrayp a p in
  let res = A.index a i in
  intro_varrayp a _ _;
  return res

/// Writing the value v at the i-th element of an array a.
/// TODO: we should also provide an atomic version for small types.
inline_for_extraction
[@@noextract_to "krml"]
let upd
  (#t: Type)
  (a: array t)
  (i: U32.t)
  (v: t)
: Steel unit
    (varray a)
    (fun _ -> varray a)
    (fun _ ->  U32.v i < length a)
    (fun h _ h' ->
      U32.v i < length a /\
      asel a h' == Seq.upd (asel a h) (U32.v i) v
    )
= let s = elim_varray a in
  A.pts_to_length a _;
  A.upd a i v;
  intro_varray a _

/// Spatial merging of two arrays, expressed in terms of `merge`.
inline_for_extraction // same as above
let ghost_join
  (#opened: _)
  (#elt: Type)
  (#p: P.perm)
  (a1 a2: array elt)
  (sq: squash (adjacent a1 a2))
: SteelGhost unit opened
    (varrayp a1 p `star` varrayp a2 p)
    (fun res -> varrayp (merge a1 a2) p)
    (fun _ -> True)
    (fun h _ h' ->
      aselp (merge a1 a2) p h' == aselp a1 p h `Seq.append` aselp a2 p h
    )
= let _ = elim_varrayp a1 p in
  let _ = elim_varrayp a2 p in
  A.ghost_join a1 a2 ();
  intro_varrayp _ _ _

/// Spatial merging, combining the use of `merge` and the call to the
/// stateful lemma. Since the only operations are calls to stateful
/// lemmas and pure computations, the overall computation is atomic
/// and unobservable, so can be used anywhere in atomic contexts.  By
/// virtue of the length being ghost, Karamel will extract this to
/// "let res = a1"
inline_for_extraction // this will extract to "let res = a1"
[@@noextract_to "krml"]
let join
  (#opened: _)
  (#elt: Type)
  (#p: P.perm)
  (a1: array elt)
  (a2: Ghost.erased (array elt))
: SteelAtomicBase (array elt) false opened Unobservable
    (varrayp a1 p `star` varrayp a2 p)
    (fun res -> varrayp res p)
    (fun _ -> adjacent a1 a2)
    (fun h res h' ->
      merge_into a1 a2 res /\
      aselp res p h' == aselp a1 p h `Seq.append` aselp a2 p h
    )
= let _ = elim_varrayp a1 _ in
  let _ = elim_varrayp a2 _ in
  let res = A.join a1 a2 in
  intro_varrayp res _ _;
  return res

/// Splitting an array a at offset i, as a stateful lemma expressed in
/// terms of split_l, split_r. In the non-selector case, this stateful
/// lemma returns a proof that offset i is in bounds of the value
/// sequence, which is needed to typecheck the post-resource.
inline_for_extraction // same as above
let ghost_split
  (#opened: _)
  (#elt: Type)
  (#p: P.perm)
  (a: array elt)
  (i: U32.t { U32.v i <= length a })
: SteelGhost unit opened
    (varrayp a p)
    (fun _ -> varrayp (split_l a i) p `star` varrayp (split_r a i) p)
    (fun _ -> True)
    (fun h _ h' ->
      let x = aselp a p h in
      let xl = Seq.slice x 0 (U32.v i) in
      let xr = Seq.slice x (U32.v i) (Seq.length x) in
      aselp (split_l a i) p h' == xl /\
      aselp (split_r a i) p h' == xr /\
      x == Seq.append xl xr
    )
= let _ = elim_varrayp a _ in
  A.ghost_split a i;
  intro_varrayp (split_l a i) _ _;
  intro_varrayp (split_r a i) _ _

/// NOTE: we could implement a SteelAtomicBase Unobservable "split"
/// operation, just like "join", but we don't want it to return a pair
/// of arrays. For now we settle on explicit use of split_l, split_r.


/// Copies the contents of a0 to a1
inline_for_extraction
let memcpy (#t:_) (#p0:P.perm)
           (a0 a1:array t)
           (i:U32.t)
  : Steel unit
    (varrayp a0 p0 `star` varray a1)
    (fun _ -> varrayp a0 p0  `star` varray a1)
    (requires fun _ ->
       U32.v i == length a0 /\ length a0 == length a1)
    (ensures fun h0 _ h1 ->
      length a0 == length a1 /\
      aselp a0 p0 h0 == aselp a0 p0 h1 /\
      asel a1 h1 == aselp a0 p0 h1)
  =
    let _ = elim_varrayp a0 _ in
    let _ = elim_varray a1 in
    A.memcpy a0 a1 i;
    intro_varrayp a0 _ _;
    intro_varray a1 _

/// Decides whether the contents of a0 and a1 are equal
inline_for_extraction
let compare (#t:eqtype) (#p0 #p1:P.perm)
            (a0 a1:array t)
            (l:U32.t { length a0 == length a1 /\ U32.v l == length a0})
  : Steel bool
    (varrayp a0 p0 `star` varrayp a1 p1)
    (fun _ -> varrayp a0 p0 `star` varrayp a1 p1)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      aselp a0 p0 h0 == aselp a0 p0 h1 /\
      aselp a1 p1 h0 == aselp a1 p1 h1 /\
      b = (aselp a0 p0 h1 = aselp a1 p1 h1))
  =
    let _ = elim_varrayp a0 _ in
    let _ = elim_varrayp a1 _ in
    let res = A.compare a0 a1 l in
    intro_varrayp a0 _ _;
    intro_varrayp a1 _ _;
    return res
