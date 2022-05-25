module Steel.Array0

/// C arrays of universe 0 elements, with selectors.

module P = Steel.FractionalPermission
module U32 = FStar.UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

/// NOTE: This module is defined on top of Steel.HigherArray0, so its
/// definitions are all meant to be inlined and benefit from the
/// latter module's primitive extraction. We seal it under an
/// interface to avoid unpleasantly leaking the lifting of values
/// of lower universes into the SMT context. Due to this interface,
/// cross-module inlining must be enabled using F*'s --cmi option.

/// An abstract type to represent a base array (whole allocation
/// unit), exposed for proof purposes only
[@@erasable]
val base_t (elt: Type0) : Tot Type0
val base_len (#elt: Type) (b: base_t elt) : GTot nat

/// An abstract type to represent a C pointer, as a base and an offset
/// into its base
inline_for_extraction
[@@noextract_to "krml"]
val ptr (elt: Type0) : Type0
val base (#elt: Type) (p: ptr elt) : Tot (base_t elt)
val offset (#elt: Type) (p: ptr elt) : Ghost nat (requires True) (ensures (fun offset -> offset <= base_len (base p)))
val ptr_base_offset_inj (#elt: Type) (p1 p2: ptr elt) : Lemma
  (requires (
    base p1 == base p2 /\
    offset p1 == offset p2
  ))
  (ensures (
    p1 == p2
  ))

/// A concrete type to represent a C array, as a C pointer and a ghost
/// array length.  By virtue of the length being ghost, Karamel will
/// extract this type as just ptr, but to inline the definition of
/// this type, we use standard dependent pairs instead of a custom
/// record type.
inline_for_extraction
[@@noextract_to "krml"]
let array (elt: Type0) : Tot Type0 =
  (p: ptr elt & (length: Ghost.erased nat {offset p + length <= base_len (base p)}))

/// This will extract to "let p = a"
inline_for_extraction
[@@noextract_to "krml"]
let ptr_of
  (#elt: Type)
  (a: array elt)
: Tot (ptr elt)
= match a with // dfst is not marked inline_for_extraction, so we need to reimplement it
  | (| p, _ |) -> p

let length (#elt: Type) (a: array elt) : GTot nat =
  dsnd a

/// A Steel separation logic heap predicate to describe that an array
/// a points to some element sequence s with some permission p.
val pts_to
  (#elt: Type0) (a: array elt)
  ([@@@ smt_fallback ] p: P.perm)
  ([@@@ smt_fallback ] s: Seq.seq elt)
: Tot vprop

/// A stateful lemma to relate the size of an array with the size
/// of the element sequence it points to
val pts_to_length
  (#opened: _)
  (#elt: Type0) (a: array elt)
  (p: P.perm)
  (s: Seq.seq elt)
: SteelGhost unit opened
    (pts_to a p s)
    (fun _ -> pts_to a p s)
    (fun _ -> True)
    (fun _ _ _ -> Seq.length s == length a)

/// A selector version
val varrayp_hp
  (#elt: Type0) (a: array elt) (p: P.perm)
: Tot (slprop u#1)

val varrayp_sel
  (#elt: Type) (a: array elt) (p: P.perm)
: Tot (selector (Seq.lseq elt (length a)) (varrayp_hp a p))

[@__steel_reduce__] // for t_of
let varrayp
  (#elt: Type) (a: array elt) (p: P.perm)
: Tot vprop
= VUnit ({
    hp = varrayp_hp a p;
    t = _;
    sel = varrayp_sel a p;
  })

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
val malloc_pt
  (#elt: Type)
  (x: elt)
  (n: U32.t)
: Steel (array elt)
    emp
    (fun a -> pts_to a P.full_perm (Seq.create (U32.v n) x))
    (fun _ -> True)
    (fun _ a _ ->
      length a == U32.v n /\
      base_len (base (ptr_of a)) == U32.v n
    )

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
      base_len (base (ptr_of a)) == U32.v n /\
      asel a h' == Seq.create (U32.v n) x
    )
= let res = malloc_pt x n in
  intro_varray res _;
  return res

/// Freeing a full array. 
inline_for_extraction
[@@ noextract_to "krml";
    warn_on_use "Steel.Array0.free_pt is currently unsound in the presence of zero-size subarrays, have you collected them all?"]
val free_pt
  (#elt: Type)
  (#s: Ghost.erased (Seq.seq elt))
  (a: array elt)
: Steel unit
    (pts_to a P.full_perm s)
    (fun _ -> emp)
    (fun _ ->
      length a == base_len (base (ptr_of a))
    )
    (fun _ _ _ -> True)

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
      length a == base_len (base (ptr_of a))
    )
    (fun _ _ _ -> True)
= let _ = elim_varray a in
  free_pt a

/// Sharing and gathering permissions on an array. Those only
/// manipulate permissions, so they are nothing more than stateful
/// lemmas.
val share_pt
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (a: array elt)
  (p p1 p2: P.perm)
: SteelGhost unit opened
    (pts_to a p x)
    (fun _ -> pts_to a p1 x `star` pts_to a p2 x)
    (fun _ -> p == p1 `P.sum_perm` p2)
    (fun _ _ _ -> True)

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
  share_pt a p p1 p2;
  intro_varrayp a p1 _;
  intro_varrayp a p2 _

val gather_pt
  (#opened: _)
  (#elt: Type)
  (a: array elt)
  (#x1: Seq.seq elt) (p1: P.perm)
  (#x2: Seq.seq elt) (p2: P.perm)
: SteelGhost unit opened
    (pts_to a p1 x1 `star` pts_to a p2 x2)
    (fun _ -> pts_to a (p1 `P.sum_perm` p2) x1)
    (fun _ -> True)
    (fun _ _ _ -> x1 == x2)

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
  gather_pt a p1 p2;
  intro_varrayp a _ _

/// Reading the i-th element of an array a.
/// TODO: we should also provide an atomic version for small types.
inline_for_extraction
[@@noextract_to "krml"]
val index_pt
  (#t: Type) (#p: P.perm)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t)
: Steel t
    (pts_to a p s)
    (fun _ -> pts_to a p s)
    (fun _ -> U32.v i < length a)
    (fun _ res _ -> U32.v i < Seq.length s /\ res == Seq.index s (U32.v i))

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
  let res = index_pt a i in
  intro_varrayp a _ _;
  return res

/// Writing the value v at the i-th element of an array a.
/// TODO: we should also provide an atomic version for small types.
inline_for_extraction
[@@noextract_to "krml"]
val upd_pt
  (#t: Type)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t {U32.v i < Seq.length s})
  (v: t)
: SteelT unit
    (pts_to a P.full_perm s)
    (fun res -> pts_to a P.full_perm (Seq.upd s (U32.v i) v))

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
= let _ = elim_varray a in
  upd_pt a i v;
  intro_varray a _

/// An array a1 is adjacent to an array a2 if and only if they have
/// the same base array and the end of a1 coincides with the beginning
/// of a2
let adjacent (#elt: Type) (a1 a2: array elt) : Tot prop =
  base (ptr_of a1) == base (ptr_of a2) /\
  offset (ptr_of a1) + (length a1) == offset (ptr_of a2)

/// If two arrays are adjacent, then we can compute their merge, with
/// their combined lengths. By virtue of the length being ghost,
/// Karamel will extract it as "let y = a1"
inline_for_extraction
[@@noextract_to "krml"]
let merge (#elt: Type) (a1: array elt) (a2: Ghost.erased (array elt))
: Pure (array elt)
  (requires (adjacent a1 a2))
  (ensures (fun y -> length y == length a1 + length a2))
= (| ptr_of a1, Ghost.hide (length a1 + length a2) |)

/// Adjacency and merging are associative.
let merge_assoc (#elt: Type) (a1 a2 a3: array elt) : Lemma
  (requires (adjacent a1 a2 /\ adjacent a2 a3))
  (ensures (
    adjacent (merge a1 a2) a3 /\ adjacent a1 (merge a2 a3) /\
    merge (merge a1 a2) a3 == merge a1 (merge a2 a3)
  ))
= ()

/// A shortcut to combine adjacency and merging
let merge_into (#elt: Type) (a1 a2 a: array elt) : Tot prop =
  adjacent a1 a2 /\
  merge a1 a2 == a

/// Spatial merging of two arrays, expressed in terms of `merge`.
val ghost_join_pt
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Seq.seq elt)
  (#p: P.perm)
  (a1 a2: array elt)
  (h: squash (adjacent a1 a2))
: SteelGhostT unit opened
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to (merge a1 a2) p (x1 `Seq.append` x2))

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
  ghost_join_pt a1 a2 ();
  intro_varrayp (merge a1 a2) _ _

/// Spatial merging, combining the use of `merge` and the call to the
/// stateful lemma. Since the only operations are calls to stateful
/// lemmas and pure computations, the overall computation is atomic
/// and unobservable, so can be used anywhere in atomic contexts.  By
/// virtue of the length being ghost, Karamel will extract this to
/// "let res = a1"
inline_for_extraction // this will extract to "let res = a1"
[@@noextract_to "krml"]
let join_pt
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Ghost.erased (Seq.seq elt))
  (#p: P.perm)
  (a1: array elt)
  (a2: Ghost.erased (array elt))
: SteelAtomicBase (array elt) false opened Unobservable
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (fun _ -> adjacent a1 a2)
    (fun _ res _ -> merge_into a1 a2 res)
= ghost_join_pt a1 a2 ();
  let res = merge a1 a2 in
  change_equal_slprop
    (pts_to (merge a1 (Ghost.reveal a2)) p (x1 `Seq.append` x2))
    (pts_to res p (x1 `Seq.append` x2));
  return res

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
  let res = join_pt a1 a2 in
  intro_varrayp res _ _;
  return res

/// Computing the left-hand-side part of splitting an array a at
/// offset i.  By virtue of the length being ghost, Karamel will
/// extract this to "let y = a"
inline_for_extraction // this will extract to "let y = a"
[@@noextract_to "krml"]
let split_l (#elt: Type) (a: array elt)
  (i: Ghost.erased U32.t)
: Pure (array elt)
  (requires (U32.v i <= length a))
  (ensures (fun y -> True))
= (| ptr_of a, Ghost.hide (U32.v i) |)

/// C pointer arithmetic to compute (p+off), shifting a pointer p by
/// offset off.  TODO: replace this with a Ghost definition and a
/// SteelAtomicBase Unobservable operation with the corresponding
/// permission.
inline_for_extraction
[@@noextract_to "krml"]
val ptr_shift
  (#elt: Type)
  (p: ptr elt)
  (off: U32.t)
: Pure (ptr elt)
  (requires (offset p + U32.v off <= base_len (base p)))
  (ensures (fun p' ->
    base p' == base p /\
    offset p' == offset p + U32.v off
  ))

/// Computing the right-hand-side part of splitting an array a at
/// offset i.
inline_for_extraction
[@@noextract_to "krml"]
let split_r (#elt: Type) (a: array elt)
  (i: U32.t)
: Pure (array elt)
  (requires (U32.v i <= length a))
  (ensures (fun y -> merge_into (split_l a i) y a))
= (| ptr_shift (ptr_of a) i, Ghost.hide (length a - U32.v i) |)

/// Splitting an array a at offset i, as a stateful lemma expressed in
/// terms of split_l, split_r. In the non-selector case, this stateful
/// lemma returns a proof that offset i is in bounds of the value
/// sequence, which is needed to typecheck the post-resource.
val ghost_split_pt
  (#opened: _)
  (#elt: Type)
  (#x: Seq.seq elt)
  (#p: P.perm)
  (a: array elt)
  (i: U32.t)
: SteelGhost (squash (U32.v i <= length a /\ U32.v i <= Seq.length x)) opened
    (pts_to a p x)
    (fun res ->
      pts_to (split_l a i) p (Seq.slice x 0 (U32.v i)) `star`
      pts_to (split_r a i) p (Seq.slice x (U32.v i) (Seq.length x)))
    (fun _ -> U32.v i <= length a)
    (fun _ res _ ->
      x == Seq.append (Seq.slice x 0 (U32.v i)) (Seq.slice x (U32.v i) (Seq.length x))
    )

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
  ghost_split_pt a i;
  intro_varrayp (split_l a i) _ _;
  intro_varrayp (split_r a i) _ _

/// NOTE: we could implement a SteelAtomicBase Unobservable "split"
/// operation, just like "join", but we don't want it to return a pair
/// of arrays. For now we settle on explicit use of split_l, split_r.
