module Test.Integers
open FStar.Integers

(**
 This file demonstrates the overloading support for integers and
 machine integers provided by the FStar.Integers library and by a
 compiler option `--integer_overloading` for typing machine integer
 constants w.r.t this library
 **)

/// `FStar.Integers.nat`, `FStar.Integers.pos` etc.
///  are just refinements of `FStar.Integers.int`
///  So, operations that mix these with are supported
let ex1_const_nat (x:nat) : nat = 0 + x
let ex2_nat_int_pos (x:nat) (y:int) (z:pos) = x + y + z

/// There's nothing special about the refinements in FStar.Integers
/// You can define your own
let ex3_nat_custom_int_pos (x:nat) (y:int{y > x}) (z:pos) : nat = x + y + z

/// You can still use these with the integer operations in prims But,
/// it's a bit ugly.  In particular, the operators in prims are
/// (poorly) named `op_Addition, ...` etc. rather than `(+), ...`
/// etc. We should fix this.
let ex4_prims_again (x:nat) (y:int{y > x}) (z:pos) : nat =
  Prims.(x `op_Addition` y `op_Addition` z)

/// The same operations can also be used on machine integers, although
/// they come with bounds checks, as should be expected.
///
/// Note the inferred type: `int_t (Unsigned W32)`
let ex4_uint32_plus (x:uint_32) (y:uint_32{FStar.UInt.size (FStar.UInt32.(v x `Prims.op_Addition` v y)) 32}) =
  x + y

/// But, rather than the clumsy bounds check above, we can write it
/// more succinctly using the `ok` combinator
///
/// Note the inferred type: `int_t (Unsigned W32)`
let ex5_uint32_ok (x:uint_32) (y:uint_32{ok ( * ) y y /\ ok (+) x (y * y)}) = x + y * y

/// Despite the overloading, one can still use the explicit operations
/// if desired, in mixture with the types that support overloading
let ex6 (x:uint_32) (y:uint_32{ok ( + ) x y }) = FStar.UInt32.(x +^ y)

/// Unfortunately, we still have trouble parsing `( - )` as an operator
/// So, you have to write it as `op_Subtraction`
let ex9 (x:int_32{ok op_Subtraction 0l x}) = 0l - x

/// Though, it's arguably still a bit cleaner than before
let ex10 (x:FStar.Int32.t{FStar.Int.size (Prims.op_Minus (FStar.Int32.v x)) 32}) = FStar.Int32.(0l -^ x)

/// We also have a generic bounds-respecting cast operator among the integer types
/// This one does an an addition in uint_32, with checks on both the cast and the addition
let ex12 (x:int_32{cast_ok (Unsigned W32) x}) (y:uint_32{ok (+) (cast x) y}) = cast x + y

/// But casts to wider types of the same signedness are always ok
let ex13 (x:uint_16) (y:uint_32{ok (+) (cast x) y}) = cast x + y

////////////////////////////////////////////////////////////////////////////////
// Constants:
//  By default constants like 0ul are types as FStar.UInt32.t
//  rather than FStar.Integers.uint_32
////////////////////////////////////////////////////////////////////////////////

/// Without the --integer_overloading option
/// working with integer constants requires an explicit
/// type annotation to infer implicit arguments
///
/// This next one is expected to fail since `0ul` and `1ul` are typed
/// as FStar.UInt32.t, whereas the `+` is from FStar.Integers
/// and its implicit arguments cannot be inferred
[@fail]
let ex_fail1 = 0ul + 1ul

/// But, with a type annotation it succeeds
let ex14 : uint_32 = 0ul + 1ul

/// Or, one can explicitly use the non-overloaded operators
let ex15 = FStar.UInt32.(0ul +^ 1ul)

/// But, recall that this is just a problem where there are no
/// FStar.Integer.int_t types around to help guide inference
///
/// As above, this still works: an annotation on one of the operands
/// will do
let ex16 (bound:uint_32) (x:uint_32{x < bound}) = x + 1ul

/// One can also annotate the constants with their types
let ex17 = (0ul <: uint_32) + (1ul <: uint_32)

/// The following compiler option automates this type ascription
/// adding the appropriate ascription to all integer constants
#set-options "--integer_overloading true"

/// With the option turned on, this is no longer necessary
let ex18 = 0ul + 1ul

/// Overloading covers both machine integers as well as
/// mathematical integers
/// Note the inferred type: z: int_t (Signed Winfinite)
let ex19 = 0 + 1

/// With constants typed this way, and with unary minus on machine integers
/// some code is easier to write than before
let ex20 =
  let abs (x:int) = if x > 0 then x else - x in
  let min_int32 = -0x7fffffffl - 1l in
  let abs_int32 (x:int_32{x <> min_int32}) : y:int_32{v y = abs (v x)} =
      if x < 0l then -x else x
  in
  ()

////////////////////////////////////////////////////////////////////////////////
//But, some problems remain. Notably, compatibility with modules that
//have not been written with FStar.Integers in mind
////////////////////////////////////////////////////////////////////////////////

/// If you have code annotated with types like Prims.int or FStar.UInt32.t etc.
/// then using these with FStar.Integers requires explicit casts

[@fail] //this will fail to infer implicits
let ex_fail2 (x:Prims.int) (y:Prims.int) = x + y

/// But not if you annotate with FStar.Integers.int
let ex21 (x:int) (y:int) = x + y

/// This may not seem like much of a problem, except that many
/// libraries do not use yet use these FStar.Integer types
[@fail] //fails for the same reason as ex_fail2; Seq.length returns a Prims.nat
let ex_fail3 (a:Type0) (s:Seq.seq a) (t:Seq.seq a) = Seq.length s < Seq.length t

/// It requires an explicit ascription to FStar.Integers.nat to succeed
let ex22 (a:Type0) (s:Seq.seq a) (t:Seq.seq a) = (Seq.length s <: nat) < Seq.length t

/// So, unless we
///
/// 1. rewrite our libraries to use FStar.Integers.* more
///    systematically
///
/// Or,
///
/// 2. add compiler support to special case types like Prims.int,
///    Prims.nat, FStar.UInt[N].t, etc, allowing them to be implicitly
///    converted to their counterparts in `FStar.Integers.int_t _`
///
/// this overloading support will continue to have such kinks.
