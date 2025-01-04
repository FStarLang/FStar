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

module FStar.BigOps

/// This library provides propositional connectives over finite sets
/// expressed as lists, aka "big operators", in analogy with LaTeX
/// usage for \bigand, \bigor, etc.
///
/// The library is designed with a dual usage in mind:
///
///     1. Normalization: When applied to a list literal, we want
///        {[big_and f [a;b;c]]} to implicilty reduce to [f a /\ f b /\ f c]
///
///     2. Symbolic manipulation: We provide lemmas of the form
///
///        [big_and f l <==> forall x. L.memP x l ==> f x]
///
/// In this latter form, partially computing [big_and] as a fold over
/// a list is cumbersome for proof. So, we provide variants [big_and']
/// etc., that do not reduce implicitly.

module L = FStar.List.Tot.Base

(** We control reduction using the [delta_attr] feature of the
    normalizer. See FStar.Pervasives for how that works. Every term
    that is to be reduced is with the [__reduce__] attribute *)
let __reduce__ = ()

(** We wrap [norm] with a module-specific custom usage, triggering
    specific reduction steps *)

[@@ __reduce__]
unfold
let normal (#a: Type) (x: a) : a =
  FStar.Pervasives.norm [
      iota;
      zeta;
      delta_only [`%L.fold_right_gtot; `%L.map_gtot];
      delta_attr [`%__reduce__];
      primops;
      simplify
    ]
    x

(** A useful lemma to relate terms to their implicilty reducing variants *)
val normal_eq (#a: Type) (f: a) : Lemma (f == normal f)

(**** Map and fold *)

(** A utility that combines map and fold: [map_op' op f l z] maps each
    element of [l] by [f] and then combines them using [op] *)
[@@ __reduce__]
let map_op' #a #b #c (op: (b -> c -> GTot c)) (f: (a -> GTot b)) (l: list a) (z: c) : GTot c =
  L.fold_right_gtot #a #c l (fun x acc -> (f x) `op` acc) z

(** Equations for [map_op'] showing how it folds over the empty list *)
val map_op'_nil (#a #b #c: Type) (op: (b -> c -> GTot c)) (f: (a -> GTot b)) (z: c)
    : Lemma (map_op' op f [] z == z)

(** Equations for [map_op'] showing how it folds over a cons cell *)
val map_op'_cons
      (#a #b #c: Type)
      (op: (b -> c -> GTot c))
      (f: (a -> GTot b))
      (hd: a)
      (tl: list a)
      (z: c)
    : Lemma (map_op' op f (hd :: tl) z == (f hd) `op` (map_op' op f tl z))

(**** Conjunction *)

(** [big_and' f l] = [/\_{x in l} f x] *)
[@@ __reduce__]
let big_and' #a (f: (a -> Type)) (l: list a) : Type = map_op' l_and f l True

(** Equations for [big_and'] showing it to be trivial over the empty list *)
val big_and'_nil (#a: Type) (f: (a -> Type)) : Lemma (big_and' f [] == True)

(** Equations for [big_and'] showing it to be a fold over a list with [/\] *)
val big_and'_cons (#a: Type) (f: (a -> Type)) (hd: a) (tl: list a)
    : Lemma (big_and' f (hd :: tl) == (f hd /\ big_and' f tl))

(** [big_and' f l] is a [prop], i.e., it is proof irrelevant.

   Note: defining `big_and'` to intrinsically be in `prop`
   is also possible, but it's much more tedious in proofs.

   This is in part because the [/\] is not defined in prop,
   though one can prove that [a /\ b] is a prop.

   The discrepancy means that I preferred to prove these
   operators in [prop] extrinsically.
*)
val big_and'_prop (#a: Type) (f: (a -> Type)) (l: list a) : Lemma ((big_and' f l) `subtype_of` unit)

(** Interpreting the finite conjunction [big_and f l]
    as an infinite conjunction [forall] *)
val big_and'_forall (#a: Type) (f: (a -> Type)) (l: list a)
    : Lemma (big_and' f l <==> (forall x. L.memP x l ==> f x))

(** [big_and f l] is an implicitly reducing variant of [big_and']
    It is defined in [prop] *)

[@@ __reduce__]
unfold
let big_and #a (f: (a -> Type)) (l: list a) : prop =
  big_and'_prop f l;
  normal (big_and' f l)

(**** Disjunction *)

(** [big_or f l] = [\/_{x in l} f x] *)
[@@ __reduce__]
let big_or' #a (f: (a -> Type)) (l: list a) : Type = map_op' l_or f l False

(** Equations for [big_or] showing it to be [False] on the empty list *)
val big_or'_nil (#a: Type) (f: (a -> Type)) : Lemma (big_or' f [] == False)

(** Equations for [big_or] showing it to fold over a list *)
val big_or'_cons (#a: Type) (f: (a -> Type)) (hd: a) (tl: list a)
    : Lemma (big_or' f (hd :: tl) == (f hd \/ big_or' f tl))

(** [big_or f l] is a `prop`
     See the remark above on the style of proof for prop *)
val big_or'_prop (#a: Type) (f: (a -> Type)) (l: list a) : Lemma ((big_or' f l) `subtype_of` unit)

(** Interpreting the finite disjunction [big_or f l]
    as an infinite disjunction [exists] *)
val big_or'_exists (#a: Type) (f: (a -> Type)) (l: list a)
    : Lemma (big_or' f l <==> (exists x. L.memP x l /\ f x))

(** [big_or f l] is an implicitly reducing variant of [big_or']
     It is defined in [prop] *)

[@@ __reduce__]
unfold
let big_or #a (f: (a -> Type)) (l: list a) : prop =
  big_or'_prop f l;
  normal (big_or' f l)

(**** Pairwise operators *)

/// We provide functions to apply a reflexive, symmetric binary
/// operator to elements in a list [l] pairwise, in a triangle of
/// elements in the square matrix of [l X l]. To illustrate, for a
/// list of [n] elements, we fold the operator over the pairwise
/// elements of the list in top-down, left-to-right order of the
/// diagram below
///
///
///  {[
///     0 1 2 3 ... n
///   0
///   1 x
///   2 x x
///   3 x x x
///   . x x x x
///   n x x x x  ]}

(** Mapping pairs of elements of [l] using [f] and combining them with
    [op]. *)
[@@ __reduce__]
let rec pairwise_op' #a #b (op: (b -> b -> GTot b)) (f: (a -> a -> b)) (l: list a) (z: b) : GTot b =
  match l with
  | [] -> z
  | hd :: tl -> (map_op' op (f hd) tl z) `op` (pairwise_op' op f tl z)

(** [f] is a symmetric relation *)
let symmetric (#a: Type) (f: (a -> a -> Type)) = forall x y. f x y <==> f y x

(** [f] is a reflexive relation *)
let reflexive (#a: Type) (f: (a -> a -> Type)) = forall x. f x x

(** [f] is a anti-reflexive relation *)
let anti_reflexive (#a: Type) (f: (a -> a -> Type)) = forall x. ~(f x x)

(**** Pairwise conjunction *)

(** [pairwise_and f l] conjoins [f] on all pairs excluding the diagonal
    i.e.,

      {[ pairwise_and f [a; b; c] = f a b /\ f a c /\ f b c ]} *)
[@@ __reduce__]
let pairwise_and' #a (f: (a -> a -> Type)) (l: list a) : Type = pairwise_op' l_and f l True

(** Equations for [pairwise_and] showing it to be a fold with [big_and] *)
val pairwise_and'_nil (#a: Type) (f: (a -> a -> Type0)) : Lemma (pairwise_and' f [] == True)

(** Equations for [pairwise_and] showing it to be a fold with [big_and] *)
val pairwise_and'_cons (#a: Type) (f: (a -> a -> Type0)) (hd: a) (tl: list a)
    : Lemma (pairwise_and' f (hd :: tl) == (big_and' (f hd) tl /\ pairwise_and' f tl))

(** [pairwise_and' f l] is a prop
    See the remark above on the style of proof for prop *)
val pairwise_and'_prop (#a: Type) (f: (a -> a -> Type)) (l: list a)
    : Lemma ((pairwise_and' f l) `subtype_of` unit)

(** [pairwise_and' f l] for symmetric reflexive relations [f]
    is interpreted as universal quantification over pairs of list elements **)
val pairwise_and'_forall (#a: Type) (f: (a -> a -> Type)) (l: list a)
    : Lemma (requires symmetric f /\ reflexive f)
      (ensures (pairwise_and' f l <==> (forall x y. L.memP x l /\ L.memP y l ==> f x y)))

(** [pairwise_and' f l] for symmetric relations [f] interpreted as
    universal quantification over pairs of list of unique elements *)
val pairwise_and'_forall_no_repeats (#a: Type) (f: (a -> a -> Type)) (l: list a)
    : Lemma (requires symmetric f /\ L.no_repeats_p l)
      (ensures (pairwise_and' f l <==> (forall x y. L.memP x l /\ L.memP y l /\ x =!= y ==> f x y)))

(** [pairwise_and f l] is an implicitly reducing variant of [pairwise_and']
    It is defined in [prop] *)

[@@ __reduce__]
unfold
let pairwise_and #a (f: (a -> a -> Type)) (l: list a) : prop =
  pairwise_and'_prop f l;
  normal (pairwise_and' f l)

(**** Pairwise disjunction *)

(** [pairwise_or f l] disjoins [f] on all pairs excluding the diagonal
    i.e., [pairwise_or f [a; b; c] = f a b \/ f a c \/ f b c] *)
[@@ __reduce__]
let pairwise_or' #a (f: (a -> a -> Type)) (l: list a) : Type = pairwise_op' l_or f l False

(** Equations for [pairwise_or'] showing it to be a fold with [big_or'] *)
val pairwise_or'_nil (#a: Type) (f: (a -> a -> Type0)) : Lemma (pairwise_or' f [] == False)

(** Equations for [pairwise_or'] showing it to be a fold with [big_or'] *)
val pairwise_or'_cons (#a: Type) (f: (a -> a -> Type0)) (hd: a) (tl: list a)
    : Lemma (pairwise_or' f (hd :: tl) == (big_or' (f hd) tl \/ pairwise_or' f tl))

(** [pairwise_or' f l] is a prop
    See the remark above on the style of proof for prop *)
val pairwise_or'_prop (#a: Type) (f: (a -> a -> Type)) (l: list a)
    : Lemma ((pairwise_or' f l) `subtype_of` unit)

(** [pairwise_or' f l] for symmetric, anti-reflexive relations [f]
    interpreted as existential quantification over
    pairs of list elements *)
val pairwise_or'_exists (#a: Type) (f: (a -> a -> Type)) (l: list a)
    : Lemma (requires symmetric f /\ anti_reflexive f)
      (ensures (pairwise_or' f l <==> (exists x y. L.memP x l /\ L.memP y l /\ f x y)))

(** [pairwise_or' f l] for symmetric, anti-reflexive relations [f]
    interpreted as existential quantification over
    pairs of list elements *)
val pairwise_or'_exists_no_repeats (#a: Type) (f: (a -> a -> Type)) (l: list a)
    : Lemma (requires symmetric f /\ L.no_repeats_p l)
      (ensures (pairwise_or' f l <==> (exists x y. L.memP x l /\ L.memP y l /\ x =!= y /\ f x y)))

(** [pairwise_or f l] is an implicitly reducing variant of [pairwise_or']
    It is defined in [prop] *)

[@@ __reduce__]
unfold
let pairwise_or #a (f: (a -> a -> Type)) (l: list a) : prop =
  pairwise_or'_prop f l;
  normal (pairwise_or' f l)

