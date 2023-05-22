module Steel.ArrayArith

open Steel.FractionalPermission
open Steel.Effect.Atomic
open Steel.Effect
open Steel.ST.Array
open Steel.Array

(* This module provides a very restricted way of doing pointer arithmetic comparison on Steel arrays.
   Primitives in this module are considered builtins by karamel, and have handwritten C implementations.
   Clients using this module should extract with the krml options
   `-static-header Steel.ArrayArith -no-prefix Steel.ArrayArith`
*)

/// The main predicate of this module. `within_bounds` captures that [p] is part of the same
/// allocation unit as [arr1] and [arr2], and situated in between. It is an abstract predicate,
/// that can only be introduced by the `within_bounds_intro` function below.
val within_bounds (#a: Type) (arr1 p arr2: array a) : prop

/// An abbreviation capturing that [arr1] and [arr2] belong to the same array,
/// and hence to the same allocation unit according to the Steel memory model
unfold
let same_base_array (#a:Type) (arr1 arr2: array a) : prop
 = base (ptr_of arr1) == base (ptr_of arr2)

/// The only way to introduce the `within_bounds` predicate.
/// To fit inside the C standard, we require all three arrays to be live.
/// Furthermore, pointer comparison when pointers belong to different
/// allocation units is undefined according to the C standard, see section 6.5.8
/// of https://www.open-std.org/jtc1/sc22/wg14/www/docs/n2912.pdf. Instead, this
/// function will be primitively extracted to C as a comparison on uintptr_t,
/// i.e. (uintptr_t) arr1 <= (uintptr_t) p && (uintptr_t) p <= (uintptr_t) arr2
val within_bounds_ptr (#a :Type) (#p1 #p2 #pp:perm) (arr1 p arr2: ptr a)
  (len1: Ghost.erased nat { offset arr1 + len1 <= base_len (base arr1) })
  (len2: Ghost.erased nat { offset arr2 + len2 <= base_len (base arr2) })
  (lenp: Ghost.erased nat { offset p + lenp <= base_len (base p) })
  (s1 s2 sp: Ghost.erased (Seq.seq a))
  : Steel bool
  (pts_to (| arr1, len1 |) p1 s1 `star` pts_to (| arr2, len2 |) p2 s2 `star` pts_to (| p, lenp |) pp sp)
  (fun _ -> pts_to (| arr1, len1 |) p1 s1 `star` pts_to (| arr2, len2 |) p2 s2 `star` pts_to (| p, lenp |) pp sp)
  (requires fun _ -> base arr1 == base arr2)
  (ensures fun _ r _ -> if r then within_bounds (| arr1, len1 |) (| p, lenp |) (| arr2, len2 |) else True)

inline_for_extraction
[@@noextract_to "krml"]
let within_bounds_intro (#a: Type)
  (#p1 #pp #p2: perm)
  (arr1 p arr2: array a)
  : Steel bool
  (varrayp arr1 p1 `star` varrayp p pp `star` varrayp arr2 p2)
  (fun _ -> varrayp arr1 p1 `star` varrayp p pp `star` varrayp arr2 p2)
  (requires fun h0 -> same_base_array arr1 arr2)
  (ensures fun h0 r h1 ->
    (if r then within_bounds arr1 p arr2 else True) /\
    aselp arr1 p1 h1 == aselp arr1 p1 h0 /\
    aselp p pp h1 ==  aselp p pp h0 /\
    aselp arr2 p2 h1 == aselp arr2 p2 h0
  )
  = let s1 = elim_varrayp arr1 p1 in
    let s2 = elim_varrayp arr2 p2 in
    let sp = elim_varrayp p pp in
    change_equal_slprop (pts_to arr1 p1 _) (pts_to (| ptr_of arr1, Ghost.hide (length arr1) |) p1 _);
    change_equal_slprop (pts_to p pp _) (pts_to (| ptr_of p, Ghost.hide (length p) |) pp _);
    change_equal_slprop (pts_to arr2 _ _) (pts_to (| ptr_of arr2, Ghost.hide (length arr2) |) p2 _);
    let b = within_bounds_ptr (ptr_of arr1) (ptr_of p) (ptr_of arr2) (length arr1) (length arr2) (length p) s1 s2 sp in
    change_equal_slprop (pts_to (| ptr_of arr1, Ghost.hide (length arr1) |) _ _) (pts_to arr1 _ _) ;
    change_equal_slprop (pts_to (| ptr_of p, Ghost.hide (length p) |) _ _) (pts_to p _ _);
    change_equal_slprop (pts_to (| ptr_of arr2, Ghost.hide (length arr2) |) _ _) (pts_to arr2 _ _);
    intro_varrayp arr1 p1 s1;
    intro_varrayp arr2 p2 s2;
    intro_varrayp p pp sp;
    return b

/// An elimination lemma for `within_bounds`. If [p] is within bounds of
/// [arr1] and [arr2], then they are all part of the same allocation unit,
/// and it is located between the two pointers.
val within_bounds_elim (#a: Type)
  (arr1 arr2 p: array a)
  : Lemma
  (requires
    same_base_array arr1 arr2 /\
    within_bounds arr1 p arr2)
  (ensures
    same_base_array arr1 p /\
    same_base_array arr2 p /\
    offset (ptr_of p) - offset (ptr_of arr1) >= 0 /\
    offset (ptr_of arr2) - offset (ptr_of p) >= 0
  )
