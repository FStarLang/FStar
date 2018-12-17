(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
///  So, operations that mix these are supported
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
// Mixing code that has been annotated or inferred with types like Prims.int
// with code that uses FStar.Integers.int, etc. just works
// This required an extension of the unification algorithm
////////////////////////////////////////////////////////////////////////////////

/// Constants like `0ul` are still typed as `FStar.UInt32.t`
/// But, they can still be used with the overloaded operators
/// Since `FStar.UInt32.t` can be unified with `FStar.Integers.int_t (Unsigned W32)
/// Note the inferred type is still `FStar.Integers.int_t (Unsigned W32)
let ex14 = 0ul + 1ul

/// Of course, you can also annotate it
let ex15 : uint_32 = 0ul + 1ul

/// Or, one can still explicitly use the non-overloaded operators
let ex16 = FStar.UInt32.(0ul +^ 1ul)

/// Types from FStar.Integers can also be mixed with
/// the machine integer types
let ex17 (bound:uint_32) (x:uint_32{x < bound}) = x + 1ul

/// Of course, this works for mathematical integers too
let ex19 = 0 + 1

/// We now also have a unary minus on all integers making some code
/// easier to write than before, esp. when mixed with machine integer
/// constants
let ex20 =
  let abs (x:int) = if x > 0 then x else - x in
  let min_int32 = -0x7fffffffl - 1l in
  let abs_int32 (x:int_32{x <> min_int32}) : y:int_32{v y = abs (v x)} =
      if x < 0l then -x else x
  in
  ()

/// If you have code annotated with types like Prims.int or
/// FStar.UInt32.t etc.  then these can be freely mixed with
/// FStar.Integers
let ex_21 (x:Prims.int) (y:Prims.int) = x + y

/// This is especially important for reuse of exsiting libraries
let ex_22 (a:Type0) (s:Seq.seq a) (t:Seq.seq a) = Seq.length s < Seq.length t
let ex_23 (a:Type0) (s:Seq.seq a) (t:Seq.seq a) = Seq.length s + Seq.length t + 1

////////////////////////////////////////////////////////////////////////////////
// A heuristic for unifying matches is key to making this work
// In particular, we can unify
//  `match ?u with | P1 -> t1 ... | Pn -> tn` with `s`
// by setting `?u := Pi`,
// whenever the head symbol of `ti` matches the head of `s`
// If no such branch exists, we try the branches in sequence
// trying to solve `ti ~ s` backtracking when it fails to try the next branch.
//
// This works well for in many simple cases, and also allows for
// several layers of overloading to be defined compositionally
////////////////////////////////////////////////////////////////////////////////

/// This is a small example mimicing the essence of how FStar.Integers works
let t0 (b:bool) =
  match b with
  | true -> int
  | false -> string
let f0 #b (x:t0 b) = ()
let g0 = f0 0
let h0 = f0 "hello"

/// And you can layer these indexed types, as usual
let t1 (x:option bool) =
  match x with
  | Some b -> t0 b
  | None -> unit
let f1 #i (x:t1 i) = ()
/// And the inference heuristic succeeds here, finding a branch that
/// matches the head symbol easily
let g1 (a: t0 true) = f1 a
let g2 (a: t0 false) = f1 a

/// But even when that's not the case, the backtracking search
/// succeeds in finding the needed instantiation

/// Unification picks the first branch of t1 and the head-matching
/// heuristic picks the first branch of t0
let g3 = f1 0

/// Unification picks the first branch of t1 and the head-matching
/// heuristic picks the second branch of t0
let g4 = f1 "hello"

/// The head-matching heuristic picks the 2nd branch of t1
let g5 = f1 ()

/// Without the head-matching heuristic, unification would pick the
/// first branch of t1, then the first branch of t0 & fail;
/// backtracks to the 2nd branch of t0 & fail; backtracks to the
/// the second branch of t1 and succeed.
///
/// Note, as with other uses of backtracking in the unification
/// algorithm, the search is local; if we find a solution a particular
/// problem instance, we commit to it immediately even if the chosen
/// solution is incompatible with other problems that may be in scope;
/// global backtracking is too expensive and unpredictable.
