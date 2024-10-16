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

module FStar.IFC

/// FStar.IFC provides a simple, generic abstraction for monadic
/// information-flow control based on a user-defined (semi-)lattice of
/// information flow labels.
///
/// The main idea is to provide an abstract type [protected a l],
/// encapsulating values of type [a] carrying information at
/// confidentiality level [l]. Operations that compute on the
/// underlying [a] are instrumented to reflect the sensitivity of
/// their arguments on their results.
///
/// Several papers develop this idea, ranging from
///
/// Fable: A language for enforcing user-defined security policies
/// http://www.cs.umd.edu/~nswamy/papers/fable-tr.pdf
///
/// To more modern variants like
/// https://hackage.haskell.org/package/lio

(**** Basic definitions for a join semilattice *)

(** The [lub] is associative *)
let associative #a (f: (a -> a -> a)) = forall x y z. f (f x y) z == f x (f y z)

(** The [lub] is commutative *)
let commutative #a (f: (a -> a -> a)) = forall x y. f x y == f y x

(** The [lub] is idempotent *)
let idempotent #a (f: (a -> a -> a)) = forall x. f x x == x

(** A semilattice has a top element and a
    associative-commutative-idempotent least upper bound operator.
    This is effectively the typeclass of a semilattice, however, we
    program explicitly with semilattice, rather than use typeclass
    instantiation.  *)
noeq
type semilattice : Type u#(c + 1) =
  | SemiLattice : 
      #carrier: Type u#c ->
      top: carrier ->
      lub: (f: (carrier -> carrier -> carrier){associative f /\ commutative f /\ idempotent f})
    -> semilattice

(** For most of the rest of this development, we'll use an erased
    counterpart of a semilattice *)
let sl:Type u#(c + 1) = FStar.Ghost.erased semilattice

(** A lattice element is just an element of the carrier type *)
let lattice_element (sl: sl) = Ghost.erased (SemiLattice?.carrier (Ghost.reveal sl))

(** A convenience for joining elements in the lattice *)
unfold
let lub #sl (x: lattice_element sl) (y: lattice_element sl) : Tot (lattice_element sl) =
  Ghost.hide (SemiLattice?.lub (Ghost.reveal sl) (Ghost.reveal x) (Ghost.reveal y))

(** The main type provided by this module is [protected l b] i.e,, a
    [b]-typed value protected at IFC level [l].

    [protected b l] is in a bijection with [b], as shown by [reveal]
    and [hide] below *)
val protected (#sl: sl u#c) (l: lattice_element sl) (b: Type u#b) : Type u#b

(** [reveal] projects a [b] from a [protected b l], but incurs a ghost effect *)
val reveal (#sl: _) (#l: lattice_element sl) (#b: _) (x: protected l b) : GTot b

(** [hide] injects a [b] into a [protected b l].

    Note, any [b] can be promoted to a [protected l b] i.e.,
    [protected l b] is only meant to enforce confidentiality *)
val hide (#sl: _) (#l: lattice_element sl) (#b: _) (x: b) : Tot (protected l b)

(** The next pair of lemmas show that reveal/hide are inverses *)
val reveal_hide (#l #t #b: _) (x: b) : Lemma (reveal (hide #l #t x) == x) [SMTPat (hide #l #t x)]

val hide_reveal (#sl: _) (#l: lattice_element sl) (#b: _) (x: protected l b)
    : Lemma (hide (reveal x) == x) [SMTPat (reveal x)]

/// [protected l b] is a form of parameterized monad
///  It provides:
///    -- [return] (via [hide])
///    -- [map]    (i.e., it's a functor)
///    -- [join]   (so it's also a monad)
///  Which we package up as a [bind]

unfold
let return #sl #a (l: lattice_element sl) (x: a) : protected l a = hide x

(** This is just a map of [f] over [x] But, notice the order of
    arguments is flipped We write [map x f] instead of [map f x] so
    that [f]'s type can depend on [x] *)
val map (#a #b #sl: _) (#l: lattice_element sl) (x: protected l a) (f: (y: a{y == reveal x} -> b))
    : Tot (y: protected l b {reveal y == f (reveal x)})

(** This is almost a regular monadic [join]
    Except notice that the label of the result is the [lub]
    of the both the labels in the argument *)
val join (#sl: _) (#l1 #l2: lattice_element sl) (#a: _) (x: protected l1 (protected l2 a))
    : Tot (y: protected (l1 `lub` l2) a {reveal y == reveal (reveal x)})

(** This is almost like a regular bind, except like [map] the type of
    the continuation's argument depends on the argument [x]; and, like
    [join], the indexes on the result are at least as high as the
    indexes of the argument

    As such, any computation that observes the protected value held in
    [x] has a secrecy level at least as secret as [x] itself *)
unfold
let (let>>)
      #sl
      (#l1: lattice_element sl)
      #a
      (x: protected l1 a)
      (#l2: lattice_element sl)
      #b
      (f: (y: a{y == reveal x} -> protected l2 b))
    : Tot (protected (l1 `lub` l2) b) = join (map x f)

