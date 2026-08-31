(*
   Copyright 2008-2026 Microsoft Research

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
module FStar.Real.Dedekind

/// The real numbers, constructed as Dedekind cuts of [FStar.Rational.rat].
///
/// Unlike [FStar.Real], which is a logical model of Z3's theory of reals and is
/// therefore entirely axiomatized, everything in this module is *constructed*:
/// [real] is a concrete type, the operations are concrete definitions, and
/// every law below is proved.  The only assumptions used are the two standard
/// logical axioms already present in F*'s library --- functional and
/// propositional extensionality --- which are what make "equality of cuts" be
/// F*'s propositional equality [==]. No property of the reals is assumed.
///
/// The representation is sealed by this interface: a real is *characterized* by
/// the ordered-field laws plus completeness ([lub]) below, which is exactly what
/// a client needs.

module Q = FStar.Rational

[@@erasable]
val real : Type0

(**** The rational numbers sit inside the reals *)

val of_rat : Q.rat -> real

let of_int (n:int) : real = of_rat (Q.of_int n)

let zero : real = of_int 0
let one  : real = of_int 1
let two  : real = of_int 2

(**** Order *)

val lt : real -> real -> prop

let le (x y:real) : prop = lt x y \/ x == y
let gt (x y:real) : prop = lt y x
let ge (x y:real) : prop = le y x

(**** Field operations *)

val add : real -> real -> real
val opp : real -> real
val mul : real -> real -> real

/// Total inverse, with [inv zero == zero].
val inv : real -> real

let sub (x y:real) : real = add x (opp y)
let div (x y:real) : real = mul x (inv y)

(**** Abelian group under addition *)

val add_comm  (x y:real)   : Lemma (add x y == add y x)
val add_assoc (x y z:real) : Lemma (add (add x y) z == add x (add y z))
val add_zero  (x:real)     : Lemma (add x zero == x)
val add_opp   (x:real)     : Lemma (add x (opp x) == zero)

(**** Commutative monoid under multiplication, and a field *)

val mul_comm  (x y:real)   : Lemma (mul x y == mul y x)
val mul_assoc (x y z:real) : Lemma (mul (mul x y) z == mul x (mul y z))
val mul_one   (x:real)     : Lemma (mul x one == x)
val mul_zero  (x:real)     : Lemma (mul x zero == zero)

val distrib (x y z:real)
  : Lemma (mul x (add y z) == add (mul x y) (mul x z))

val mul_inv (x:real)
  : Lemma (requires x =!= zero) (ensures mul x (inv x) == one)

(**** Total order, compatible with the field structure *)

val lt_irrefl (x:real)   : Lemma (~(lt x x))
val lt_trans  (x y z:real) : Lemma (requires lt x y /\ lt y z) (ensures lt x z)
val lt_total  (x y:real) : Lemma (lt x y \/ x == y \/ lt y x)

val lt_add_r (x y z:real)
  : Lemma (lt (add x z) (add y z) <==> lt x y)

val lt_mul_pos (x y z:real)
  : Lemma (requires lt zero z) (ensures lt (mul x z) (mul y z) <==> lt x y)

(**** The embedding is a morphism of ordered fields *)

val of_rat_add (p q:Q.rat) : Lemma (of_rat (Q.add p q) == add (of_rat p) (of_rat q))
val of_rat_mul (p q:Q.rat) : Lemma (of_rat (Q.mul p q) == mul (of_rat p) (of_rat q))
val of_rat_opp (p:Q.rat)   : Lemma (of_rat (Q.neg p) == opp (of_rat p))
val of_rat_lt  (p q:Q.rat) : Lemma (lt (of_rat p) (of_rat q) <==> Q.lt p q)
val of_rat_inj (p q:Q.rat) : Lemma (of_rat p == of_rat q <==> p == q)

(**** Archimedes *)

/// Every real is dominated by a natural number. Equivalently, the rationals
/// are dense in the reals.
val archimedean (x:real) : Lemma (exists (n:nat). lt x (of_int n))

(**** Completeness: the whole point of the construction *)

/// Sets of reals, as predicates.
let rset = real -> prop

let is_upper_bound (s:rset) (b:real) : prop = forall (x:real). s x ==> le x b
let is_bounded_above (s:rset) : prop = exists (b:real). is_upper_bound s b
let is_nonempty (s:rset) : prop = exists (x:real). s x
let is_lub (s:rset) (b:real) : prop =
  is_upper_bound s b /\ (forall (c:real). is_upper_bound s c ==> le b c)

/// The least upper bound of a nonempty, bounded-above set of reals.
/// This is the property that distinguishes the reals from the rationals, and
/// it is the one that makes an axiom-free square root possible.
val lub (s:rset)
  : Ghost real
      (requires is_nonempty s /\ is_bounded_above s)
      (ensures  fun b -> is_lub s b)
