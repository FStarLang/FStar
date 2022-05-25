module Steel.HigherArray0

/// C arrays of universe 1 elements.
/// 
/// - Due to a limitation on the universe for selectors, no selector
///   version can be defined for universe 1.
/// - Due to F* universes not being cumulative, arrays of universe 0
///   elements need to be defined in a separate module.

module P = Steel.FractionalPermission
module U32 = FStar.UInt32

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

/// NOTE: This module is slated to have primitive Karamel extraction
/// (except for definitions meant to be inlined.)

/// An abstract type to represent a base array (whole allocation
/// unit), exposed for proof purposes only
[@@erasable]
val base_t (elt: Type u#a) : Tot Type0
val base_len (#elt: Type) (b: base_t elt) : GTot nat

/// An abstract type to represent a C pointer, as a base and an offset
/// into its base
[@@noextract_to "krml"] // primitive
val ptr (elt: Type u#a) : Type0
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
let array (elt: Type u#a) : Tot Type0 =
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
/// a points to some element sequence s with some permission p.  vprop
/// limits the universe to at most 1 (because of the universe of the
/// heap.)
val pts_to
  (#elt: Type u#1) (a: array elt)
  ([@@@ smt_fallback ] p: P.perm)
  ([@@@ smt_fallback ] s: Seq.seq elt)
: Tot vprop

/// A stateful lemma to relate the size of an array with the size
/// of the element sequence it points to
val pts_to_length
  (#opened: _)
  (#elt: Type u#1) (a: array elt)
  (p: P.perm)
  (s: Seq.seq elt)
: SteelGhost unit opened
    (pts_to a p s)
    (fun _ -> pts_to a p s)
    (fun _ -> True)
    (fun _ _ _ -> Seq.length s == length a)

/// An injectivity property, needed only to define a selector.  Such a
/// selector can be only defined in universe 0, and universes are not
/// cumulative, so we need to define a separate module for arrays of
/// universe 0 elements with selectors, reusing definitions from this
/// interface, but we do not want to use `friend`.
val pts_to_inj
  (#elt: Type u#1) (a: array elt)
  (p1: P.perm)
  (s1: Seq.seq elt)
  (p2: P.perm)
  (s2: Seq.seq elt)
  (m: mem)
: Lemma
  (requires (
    interp (hp_of (pts_to a p1 s1)) m /\
    interp (hp_of (pts_to a p2 s2)) m
  ))
  (ensures (
    s1 == s2
  ))

/// Allocating a new array of size n, where each cell is initialized
/// with value x
[@@noextract_to "krml"] // primitive
val malloc
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

/// Freeing a full array. 
[@@ noextract_to "krml"; // primitive
    warn_on_use "Steel.HigherArray0.free is currently unsound in the presence of zero-size subarrays, have you collected them all?"]
val free
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

/// Sharing and gathering permissions on an array. Those only
/// manipulate permissions, so they are nothing more than stateful
/// lemmas.
val share
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

val gather
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

/// Reading the i-th element of an array a.
/// TODO: we should also provide an atomic version for small types.
[@@noextract_to "krml"] // primitive
val index
  (#t: Type) (#p: P.perm)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t)
: Steel t
    (pts_to a p s)
    (fun _ -> pts_to a p s)
    (fun _ -> U32.v i < length a)
    (fun _ res _ -> U32.v i < Seq.length s /\ res == Seq.index s (U32.v i))

/// Writing the value v at the i-th element of an array a.
/// TODO: we should also provide an atomic version for small types.
[@@noextract_to "krml"] // primitive
val upd
  (#t: Type)
  (a: array t)
  (#s: Ghost.erased (Seq.seq t))
  (i: U32.t { U32.v i < Seq.length s })
  (v: t)
: SteelT unit
    (pts_to a P.full_perm s)
    (fun res -> pts_to a P.full_perm (Seq.upd s (U32.v i) v))

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
val ghost_join
  (#opened: _)
  (#elt: Type)
  (#x1 #x2: Seq.seq elt)
  (#p: P.perm)
  (a1 a2: array elt)
  (h: squash (adjacent a1 a2))
: SteelGhostT unit opened
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to (merge a1 a2) p (x1 `Seq.append` x2))

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
  (#x1 #x2: Ghost.erased (Seq.seq elt))
  (#p: P.perm)
  (a1: array elt)
  (a2: Ghost.erased (array elt))
: SteelAtomicBase (array elt) false opened Unobservable
    (pts_to a1 p x1 `star` pts_to a2 p x2)
    (fun res -> pts_to res p (x1 `Seq.append` x2))
    (fun _ -> adjacent a1 a2)
    (fun _ res _ -> merge_into a1 a2 res)
= ghost_join a1 a2 ();
  let res = merge a1 a2 in
  change_equal_slprop
    (pts_to (merge a1 (Ghost.reveal a2)) p (x1 `Seq.append` x2))
    (pts_to res p (x1 `Seq.append` x2));
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
[@@noextract_to "krml"] // primitive
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
/// terms of split_l, split_r. This stateful lemma returns a proof
/// that offset i is in bounds of the value sequence, which is needed to
/// typecheck the post-resource.
val ghost_split
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

/// NOTE: we could implement a SteelAtomicBase Unobservable "split"
/// operation, just like "join", but we don't want it to return a pair
/// of arrays. For now we settle on explicit use of split_l, split_r.
