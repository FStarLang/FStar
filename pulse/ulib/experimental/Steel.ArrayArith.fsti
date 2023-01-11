module Steel.ArrayArith

open Steel.Effect.Atomic
open Steel.Effect
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
val within_bounds_intro (#a: Type)
  (arr1 p arr2: array a)
  : Steel bool
  (varray arr1 `star` varray p `star` varray arr2)
  (fun _ -> varray arr1 `star` varray p `star` varray arr2)
  (requires fun h0 -> same_base_array arr1 arr2)
  (ensures fun h0 r h1 ->
    if r then within_bounds arr1 p arr2 else True /\
    asel arr1 h1 == asel arr1 h0 /\
    asel p h1 ==  asel p h0 /\
    asel arr2 h1 == asel arr2 h0
  )

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
