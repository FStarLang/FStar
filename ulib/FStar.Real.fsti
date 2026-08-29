(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Real
(*
  This module provides a signature for real arithmetic.

  Real number constants can be specific in floating point format with
  an 'R' suffix, e.g., 1.0R

  All these operations are mapped to the corresponding primitives
  in Z3's theory of real arithmetic.

  This is only a logical model of the reals. There is no extraction
  for them, as they are an erasable type. Any operation that can observe
  a real (comparisons, etc) must be Ghost or a proposition.

  Unlike most SMT-mapped theories in F*, this one is not merely assumed:
  [FStar.Real.fst] *implements* everything declared here in terms of
  [FStar.Real.Dedekind], the reals built from scratch as Dedekind cuts of
  [FStar.Rational]. So [real] is a concrete type, the field operations are
  concrete definitions.

  This is exactly the arrangement [FStar.BV] has with [FStar.BitVector]: the
  symbols below are still given Z3's native interpretation by the SMT
  encoding --- that is what makes real-arithmetic goals discharge
  automatically, and it does mean that the *identification* of this type with
  Z3's [Real] sort remains an assumption of the encoding --- but there is now
  a construction underneath witnessing that the assumed theory has a model.

  Having a construction underneath also lets this interface state things Z3
  cannot prove. Z3's reals form an ordered *field*; what makes the reals *the*
  reals is completeness, and [lub] below exposes it as a theorem of the
  Dedekind construction. [FStar.Math.Sqrt] uses nothing but [lub] to define an
  axiom-free square root, discharging the axiom it used to assume.

  Note that the [FStar.Real.Dedekind] hierarchy is deliberately *not* visible
  in this interface: [FStar.Real] is a dependency of the reflection stubs, and
  hence of essentially all of F*, so its interface is kept as light as it has
  always been. The construction is a dependency of [FStar.Real.fst] only.
*)

[@@erasable]
val real : Type0

val of_int : int -> Tot real

val ( +. ) : real -> real -> Tot real
val ( -. ) : real -> real -> Tot real
val ( *. ) : real -> real -> Tot real
val ( /. ) : real -> d:real{d =!= 0.0R} -> Tot real

val ( >.  ) : real -> real -> prop
val ( >=. ) : real -> real -> prop

val ( <.  ) : real -> real -> prop
val ( <=. ) : real -> real -> prop

let zero : real = of_int 0
let one  : real = of_int 1
let two  : real = of_int 2

(**** Completeness *)

/// Z3's theory of reals is a theory of ordered *fields*: it says nothing at
/// all about completeness, so nothing below can be discharged by SMT. It is
/// instead *proved* in [FStar.Real.fst], where [real] is the type of Dedekind
/// cuts of [FStar.Rational] and the least upper bound is a construction.
///
/// This is what makes [real] the reals rather than some arbitrary ordered
/// field, and it is what [FStar.Math.Sqrt] uses to define a square root
/// without assuming one.

/// Sets of reals, as predicates.
let rset = real -> prop

let is_upper_bound (s:rset) (b:real) : prop = forall (x:real). s x ==> x <=. b
let is_bounded_above (s:rset) : prop = exists (b:real). is_upper_bound s b
let is_nonempty (s:rset) : prop = exists (x:real). s x
let is_lub (s:rset) (b:real) : prop =
  is_upper_bound s b /\ (forall (c:real). is_upper_bound s c ==> b <=. c)

/// The least upper bound of a nonempty, bounded-above set of reals.
val lub (s:rset)
  : Ghost real
      (requires is_nonempty s /\ is_bounded_above s)
      (ensures  fun b -> is_lub s b)

/// Every real is dominated by a natural number.
val archimedean (x:real) : Lemma (exists (n:nat). x <. of_int n)
