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

module FStar.Squash

/// The module provides an interface to work with [squash] types, F*'s
/// representation for proof-irrelevant propositions.
///
/// The type [squash p] is defined in [Prims] as [_:unit{p}]. As such,
/// the [squash] type captures the classical logic used in F*'s
/// refinement types, although the interface in this module isn't
/// specifically classical. The module [FStar.Classical] provides
/// further derived forms to manipulate [squash] types.
///
/// This is inspired in part by: Quotient Types: A Modular
/// Approach. Aleksey Nogin, TPHOLs 2002.
/// http://www.nuprl.org/documents/Nogin/QuotientTypes_02.pdf
///
/// Broadly, [squash] is a monad, support the usual [return] and
/// [bind] operations.
///
/// Additionally, it supports a [push_squash] operation that relates
/// arrow types and [squash].

(** A proof of [a] can be forgotten to create a squashed proof of [a]
    *)
val return_squash (#a: Type) (x: a) : Tot (squash a)

(** Sequential composition of squashed proofs *)
val bind_squash (#a #b: Type) (x: squash a) (f: (a -> GTot (squash b))) : Tot (squash b)

(** The [push] operation, together with [bind_squash], allow deriving
    some of the other operations, notably [squash_double_arrow]. We
    rarely use the [push_squash] operation directly.

    One reading of [push f] is that for a function [f] that builds a
    proof-irrelevant prooof of [b x] for all [x:a], there exists a
    proof-irrelevant proof of [forall (x:a). b x].

    Note: since [f] is not itself squashed, [push_squash f] is not
    equal to [f].  *)
val push_squash (#a: Type) (#b: (a -> Type)) (f: (x: a -> Tot (squash (b x))))
    : Tot (squash (x: a -> GTot (b x)))

/// The pre- and postconditions of of [Pure] are equivalent to
/// squashed arguments and results.

(** [get_proof p], in a context requiring [p] is equivalent to a proof
    of [squash p] *)
val get_proof (p: Type) : Pure (squash p) (requires p) (ensures (fun _ -> True))

(** [give_proof x], for [x:squash p] is a equivalent to ensuring
    [p]. *)
val give_proof (#p: Type) (x: squash p) : Pure unit (requires True) (ensures (fun _ -> p))

(** All proofs of [squash p] are equal  *)
val proof_irrelevance (p: Type) (x y: squash p) : Tot (squash (x == y))

(** Squashing the proof of the co-domain of squashed universal
    quantifier is redundant---[squash_double_arrow] allows removing
    it. *)
val squash_double_arrow (#a: Type) (#p: (a -> Type)) ($f: (squash (x: a -> GTot (squash (p x)))))
    : GTot (squash (x: a -> GTot (p x)))

(** The analog of [push_squash] for sums (existential quantification *)
val push_sum (#a: Type) (#b: (a -> Type)) ($p: (dtuple2 a (fun (x: a) -> squash (b x))))
    : Tot (squash (dtuple2 a b))

(** The analog of [squash_double_arrow] for sums (existential quantification) *)
val squash_double_sum
      (#a: Type)
      (#b: (a -> Type))
      ($p: (squash (dtuple2 a (fun (x: a) -> squash (b x)))))
    : Tot (squash (dtuple2 a b))

(** [squash] is functorial; a ghost function can be mapped over a squash *)
val map_squash (#a #b: Type) (x: squash a) (f: (a -> GTot b)) : Tot (squash b)

(** [squash] is a monad: double squashing is redundant and can be removed. *)
val join_squash (#a: Type) (x: squash (squash a)) : Tot (squash a)

