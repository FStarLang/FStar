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
module FStar.BV

/// This module provides a type of bit-vectors, some instantiations of
/// which are mapped to Z3's bit-vector type in SMT proofs.
///
/// The main type is `bv_t (n:nat)`. This type is modeled internally
/// as a sequence of `n` booleans (using FStar.BitVector). However, it
/// is presented in this interface as an abstract type with operations
/// like `bvand`, `bvor` etc.
///
/// Most importantly, all constant instantiations of `bv_t`, e.g.,
/// `bv_t 16` are given special treatment of F*'s SMT encoding by
/// being mapped to the sort `bv 16`, Z3's type of bitvectors of
/// length 16. This enables using Z3's theory of bitvectors to
/// automate many proofs for that type. As such, proofs such as the
/// one below are fully automated, whereas when using
/// `FStar.BitVector` (which has no primitive Z3 support) explicit
/// lemmas must be provided.
///
/// ```
///  let test (x y z : bv_t 16) =
///    assert (bvand (bvand x y) z ==
///            bvand x (bvand y z))
/// ```
///
/// As a rule of thumb, one can expect good automation for identities
/// on `bv_t n` (for constant `n`) when using bitwise boolean
/// operators `bvand, bvor, bvxor, bvnot` etc. However, bitwise
/// arithmetic operators are more expensive and the extent of proof
/// automation to expect is less predictable.
///
/// This module also provides lemmas that relate the bitwise operators
/// to their underlying "sequence of bools" model. These lemmas are
/// useful when reasoning with the SMT bitvector theory alone is
/// insufficient, e.g., for certain arithmetic proofs or for
/// non-constant instantiations of `bv_t` (which do not receive
/// special treatment in the SMT encoding)

module U = FStar.UInt
 
val bv_t: (n : nat) -> t:Type0{hasEq t}

(* Redefining basic type from UInt to avoid importing UInt *)
(* Reduces verification time by 50% in small examples *)
// let max_int (n:nat) : Tot int = pow2 n - 1
// let min_int (n:nat) : Tot int = 0
// let fits (x:int) (n:nat) : Tot bool = min_int n <= x && x <= max_int n
// let size (x:int) (n:nat) : Tot Type0 = b2t(fits x n)
// type uint_t' (n:nat) = x:int{size x n}

/// Promoting to a larger bitvector type by setting the first `m` bits to zero
val bv_uext: #n:pos -> #m:pos -> a:bv_t n -> Tot (normalize (bv_t (m+n)))

/// bitwise conjunction
val bvand: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

/// bitwise exclusive or
val bvxor: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

/// bitwise disjunction
val bvor: #n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

/// bitwise negation
val bvnot: #n:pos -> a:bv_t n -> Tot (bv_t n)

/// shift left
val bvshl: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)

/// shift right
val bvshr: #n:pos -> a:bv_t n -> s:nat -> Tot (bv_t n)

/// coercing an integer to a bitvector of size `n`
///     - Requires the integer to be representable in `n` bits, i.e., no overflow
/// 
///     - This is mapped to `int2bv` in Z3, which is essentially an
///       uinterpreted function there though
/// 
/// See https://z3prover.github.io/api/html/ml/Z3.BitVector.html
val int2bv: #n:pos -> num:U.uint_t n -> Tot (bv_t n)

/// coercing a bitvector to an integer
///     - This is proven to be the inverses of int2bv
///     - And is mapped to `bv2int` in Z3
/// See `inverse_vec_lemma` and `inverse_num_lemma`
val bv2int: #n:pos -> vec:bv_t n -> Tot (U.uint_t n)

/// `list2bv` and `bv2list` are another pair of mutually inverse coercions.
/// However, these receive to special SMT encoding
val list2bv: #n:pos -> l:list bool{List.length l = n} -> Tot (bv_t n)
val bv2list: #n:pos -> bv_t n -> Tot (l:list bool{List.length l = n})

unfold
let bv_zero #n = int2bv #n 0

/// unsigned bitvector less-than
val bvult: #n:pos -> a: bv_t n -> b: bv_t n -> Tot (bool)

/// This lemma looks redundant: it is just a congruence
val int2bv_lemma_1: #n:pos -> a:U.uint_t n -> b:U.uint_t n ->
  Lemma (requires a = b) (ensures (int2bv #n a = int2bv #n b))

/// This lemma proves that `int2bv` is injective
val int2bv_lemma_2: #n:pos -> a:U.uint_t n -> b:U.uint_t n ->
  Lemma (requires (int2bv a = int2bv b)) (ensures a = b)

/// `bv2list` is the inverse of `list2bv`
val list2bv_bij: #n:pos -> a:list bool{List.length a = n} ->
  Lemma (ensures (bv2list (list2bv #n a) = a))

/// `list2bv` is the inverse of `bv2list`
val bv2list_bij: #n:pos -> a:bv_t n ->
  Lemma (ensures (list2bv (bv2list #n a) = a))

/// bitwise addition
val bvadd :#n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

/// bitwise subtraction
val bvsub :#n:pos -> a:bv_t n -> b:bv_t n -> Tot (bv_t n)

/// bitwise unsigned division: `bvudiv` in Z3
val bvdiv :#n:pos -> a:bv_t n -> b:U.uint_t n{b <> 0} -> Tot (bv_t n)

/// bitwise unsigned remained: `bvurem` in Z3
val bvmod :#n:pos -> a:bv_t n -> b:U.uint_t n{b <> 0} -> Tot (bv_t n)

/// bitwise multiplication: `bvmul` in Z3
val bvmul :#n:pos -> a:bv_t n -> b:U.uint_t n -> Tot (bv_t n)

/// `int2bv` is the inverse of `bv2int`
val inverse_vec_lemma: #n:pos -> vec:bv_t n ->
  Lemma (ensures vec = (int2bv (bv2int vec)))
        [SMTPat (int2bv (bv2int vec))]

/// `bv2int` is the inverse of `int2bv`
val inverse_num_lemma: #n:pos -> num:U.uint_t n ->
  Lemma (ensures num = bv2int #n (int2bv #n num))
        [SMTPat (bv2int #n (int2bv #n num))]

(* Lemmas revealing the underlying model of bv_t as a sequence of booleans *)

/// relating `bvult` to `<`
val int2bv_lemma_ult_1: #n:pos -> a:U.uint_t n -> b:U.uint_t n ->
  Lemma (requires a < b) (ensures (bvult #n (int2bv #n a) (int2bv #n b)))
val int2bv_lemma_ult_2: #n:pos -> a:U.uint_t n -> b:U.uint_t n ->
  Lemma (requires (bvult #n (int2bv #n a) (int2bv #n b))) (ensures a < b)

/// relating `bvand` to `logand`
val int2bv_logand (#n:pos) (#x:U.uint_t n) (#y:U.uint_t n) (#z:bv_t n)
                  (_:squash (bvand #n (int2bv #n x) (int2bv #n y) == z))
  : Lemma (int2bv #n (U.logand #n x y) == z)

/// relating `bvxor` to `logxor`
val int2bv_logxor : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
		     squash (bvxor #n (int2bv #n x) (int2bv #n y) == z) ->
		     Lemma (int2bv #n (U.logxor #n x y) == z)

/// relating `bvor` to `logor`
val int2bv_logor : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
		     squash (bvor #n (int2bv #n x) (int2bv #n y) == z) ->
		     Lemma (int2bv #n (U.logor #n x y) == z)

/// relating `bvshl` to `shift_left`
val int2bv_shl : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
			    squash (bvshl #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (U.shift_left #n x y) == z)

/// relating `bvshr` to `shift_right`
val int2bv_shr : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
			    squash (bvshr #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (U.shift_right #n x y) == z)

/// relating `bvadd` to `add_mod`, addition modulo
val int2bv_add : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
			    squash (bvadd #n (int2bv #n x) (int2bv #n y) == z) ->
			    Lemma (int2bv #n (U.add_mod #n x y) == z)

/// relating `bvsub` to `sub_mod`, subtraction modulo
val int2bv_sub : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
			    squash (bvsub #n (int2bv #n x) (int2bv #n y) == z) ->
			    Lemma (int2bv #n (U.sub_mod #n x y) == z)

/// relating `bvdiv` to `udiv`, unsigned division modulo
val int2bv_div : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n{y <> 0}) -> (#z:bv_t n) ->
			    squash (bvdiv #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (U.udiv #n x y) == z)

/// relating `bvmod` to `mod`, unsigned modulo
val int2bv_mod : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n{y <> 0}) -> (#z:bv_t n) ->
			    squash (bvmod #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (U.mod #n x y) == z)
			    
/// relating `bvmul` to `mul_mod`, multiplication modulo
val int2bv_mul : #n:pos -> (#x:U.uint_t n) -> (#y:U.uint_t n) -> (#z:bv_t n) ->
			    squash (bvmul #n (int2bv #n x) y == z) ->
			    Lemma (int2bv #n (U.mul_mod #n x y) == z)


/// Some tests to illustrate proof automation via Z3's bitvector theory
irreducible
let __test (x y z : bv_t 16) =
   assert (bvand (bvand x y) z ==
           bvand x (bvand y z))
