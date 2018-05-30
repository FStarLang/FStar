module Test.Integers
open FStar.Integers

/// Without the --integer_overloading option
/// working with integer constants requires an explicit
/// type annotation to infer implicit arguments
[@fail]
let x_fail = 0ul + 1ul

let x : uint_32 = 0ul + 1ul

/// Or, one can explicitly use the non-overloaded operators
let x_explicit = FStar.UInt32.(0ul +^ 1ul)

#set-options "--integer_overloading true"
/// With the option turned on, this is no longer necessary
/// Note the inferred type: z: int_t (Unsigned W32)
let ex1 = 0ul + 1ul

/// Overloading covers both machine integers as well as
/// mathematical integers
/// Note the inferred type: z: int_t (Signed Winfinite)
let ex2 = 0 + 1

/// `FStar.Integers.nat`, `FStar.Integers.pos` etc.
///  are just refinements of `FStar.Integers.int`
///  So, operations that mix these with are supported
let ex3_const_nat (x:nat) : nat = 0 + x
let ex4_nat_int_pos (x:nat) (y:int) (z:pos) = x + y + z

/// There's nothing special about the refinements in FStar.Integers
/// You can define your own
let ex5_nat_custom_int_pos (x:nat) (y:int{y > x}) (z:pos) : nat = x + y + z

/// You can still use these with the integer operations in prims
/// But, it's a bit ugly
let ex6_prims_again (x:nat) (y:int{y > x}) (z:pos) : nat = Prims.(x `op_Addition` y `op_Addition` z)

/// Expressing bounds checks on machine integers should be
/// significantly easier, using the `ok` combinator
let ex7 (x:uint_32) (y:uint_32{ok ( * ) y y /\ ok (+) x (y * y)}) = x + y * y

/// Despite the overloading, one can still use the explicit operations
/// if desired, in mixture with the types that support overloading
let ex8 (x:uint_32) (y:uint_32{ok ( + ) x y }) = FStar.UInt32.(x +^ y)

/// Unfortunately, we still have trouble parsing `( - )` as an operator
/// So, you have to write it as `op_Subtraction`
let ex9 (x:int_32{ok op_Subtraction 0l x}) = 0l - x

/// Though, it's arguably still a bit cleaner than before
let ex10 (x:FStar.Int32.t{FStar.Int.size (Prims.op_Minus (FStar.Int32.v x)) 32}) = FStar.Int32.(0l -^ x)

/// We also now have unary minus on machine integers
let ex11 =
  let abs (x:int) = if x > 0 then x else - x in
  let min_int32 = -0x7fffffffl - 1l in
  let abs_int32 (x:int_32{x <> min_int32}) : y:int_32{v y = abs (v x)} =
      if x < 0l then -x else x
  in
  ()

/// We also have a generic bounds-respecting cast operator among the integer types
/// This one does an an addition in uint_32, with checks on both the cast and the addition
let cast_ok #from to (x:int_t from) = within_bounds to (v x)
let ex12 (x:int_32{cast_ok (Unsigned W32) x}) (y:uint_32{ok (+) (cast x) y}) = cast x + y

/// But casts to wider types of the same signedness are always ok
let ex13 (x:uint_16) (y:uint_32{ok (+) (cast x) y}) = cast x + y
