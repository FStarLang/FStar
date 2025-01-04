(*
   Copyright 2008-2014 Microsoft Research

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

module FStar.Ghost

/// This module provides an erased type to abstract computationally
/// irrelevant values.
///
/// It relies on the GHOST effect defined in Prims.
///
/// [erased a] is decorated with the erasable attribute. As such,
///
///    1. The type is considered non-informative.
///
///       So, [Ghost (erased a)] can be subsumed to [Pure (erased a)]
///
///    2. The compiler extracts [erased a] to [unit]
///
///       The type is [erased a] is in a bijection with [a], as
///       witnessed by the [hide] and [reveal] function.
///
/// Importantly, computationally relevant code cannot use [reveal]
/// (it's marked [GTot])
///
/// Just like Coq's prop, it is okay to use erased types
/// freely as long as we produce an erased type.
///
/// [reveal] and [hide] are coercions: the typechecker will
/// automatically insert them when required. That is, if the type of
/// an expression is [erased X], and the expected type is NOT an
/// [erased Y], it will insert [reveal], and vice versa for [hide].

(** [erased t] is the computationally irrelevant counterpart of [t] *)
[@@ erasable]
new
val erased ([@@@strictly_positive] a: Type u#a) : Type u#a

(** [erased t] is in a bijection with [t], as witnessed by [reveal]
    and [hide] *)
val reveal: #a: Type u#a -> erased a -> GTot a

val hide: #a: Type u#a -> a -> Tot (erased a)

val hide_reveal (#a: Type) (x: erased a)
    : Lemma (ensures (hide (reveal x) == x)) [SMTPat (reveal x)]

val reveal_hide (#a: Type) (x: a) : Lemma (ensures (reveal (hide x) == x)) [SMTPat (hide x)]


/// The rest of this module includes several well-defined defined
/// notions. They are not trusted.

(** [Tot] is a sub-effect of [GTot] F* will usually subsume [Tot]
    computations to [GTot] computations, though, occasionally, it may
    be useful to apply this coercion explicitly. *)
let tot_to_gtot (f: ('a -> Tot 'b)) (x: 'a) : GTot 'b = f x

(** [erased]: Injecting a value into [erased]; just an alias of [hide] *)
let return (#a: Type) (x: a) : erased a = hide x

(** Sequential composition of erased *)
let bind (#a #b: Type) (x: erased a) (f: (a -> Tot (erased b))) : Tot (erased b) =
  let y = reveal x in
  f y

unfold
let (let@) (x:erased 'a) (f:('a -> Tot (erased 'b))) : Tot (erased 'b) = bind x f

(** Unary map *)
irreducible
let elift1 (#a #b: Type) (f: (a -> GTot b)) (x: erased a)
    : Tot (y: erased b {reveal y == f (reveal x)}) =
  let@ xx = x in return (f xx)

(** Binary map *)
irreducible
let elift2 (#a #b #c: Type) (f: (a -> b -> GTot c)) (x: erased a) (y: erased b)
    : Tot (z: erased c {reveal z == f (reveal x) (reveal y)}) =
  let@ xx = x in
  let@ yy = y in
  return (f xx yy)

(** Ternary map *)
irreducible
let elift3
      (#a #b #c #d: Type)
      (f: (a -> b -> c -> GTot d))
      (ga: erased a)
      (gb: erased b)
      (gc: erased c)
    : Tot (gd: erased d {reveal gd == f (reveal ga) (reveal gb) (reveal gc)}) =
  let@ a = ga in
  let@ b = gb in
  let@ c = gc in
  return (f a b c)

(** Pushing a refinement type under the [erased] constructor *)
let push_refinement #a (#p: (a -> Type0)) (r: erased a {p (reveal r)})
    : erased (x: a{p x /\ x == reveal r}) =
  let x:(x: a{p x}) = reveal r in
  return x

(** Mapping a function with a refined domain over a refined erased value *)
irreducible
let elift1_p
      (#a #b: Type)
      (#p: (a -> Type))
      ($f: (x: a{p x} -> GTot b))
      (r: erased a {p (reveal r)})
    : Tot (z: erased b {reveal z == f (reveal r)}) =
  let x:(x: a{p x}) = reveal r in
  return (f x)

(** Mapping a binary function with a refined domain over a pair of
    refined erased values *)
irreducible
let elift2_p
      (#a #b #c: Type)
      (#p: (a -> b -> Type))
      ($f: (xa: a -> xb: b{p xa xb} -> GTot c))
      (ra: erased a)
      (rb: erased b {p (reveal ra) (reveal rb)})
    : Tot (rc: erased c {reveal rc == f (reveal ra) (reveal rb)}) =
  let x = reveal ra in
  let y:(y: b{p x y}) = reveal rb in
  return (f x y)

(** Mapping a function with a refined domain and co-domain over a
    refined erased value producing a refined erased value *)
irreducible
let elift1_pq
      (#a #b: Type)
      (#p: (a -> Type))
      (#q: (x: a{p x} -> b -> Type))
      ($f: (x: a{p x} -> GTot (y: b{q x y})))
      (r: erased a {p (reveal r)})
    : Tot (z: erased b {reveal z == f (reveal r)}) =
  let x:(x: a{p x}) = reveal r in
  return (f x)

(** Mapping a binary function with a refined domain and co-domain over
    a pair of refined erased values producing a refined erased value
    *)
irreducible
let elift2_pq
      (#a #b #c: Type)
      (#p: (a -> b -> Type))
      (#q: (x: a -> y: b{p x y} -> c -> Type))
      ($f: (x: a -> y: b{p x y} -> GTot (z: c{q x y z})))
      (ra: erased a)
      (rb: erased b {p (reveal ra) (reveal rb)})
    : Tot (z: erased c {reveal z == f (reveal ra) (reveal rb)}) =
  let x = reveal ra in
  let y:(y: b{p x y}) = reveal rb in
  return (f x y)

