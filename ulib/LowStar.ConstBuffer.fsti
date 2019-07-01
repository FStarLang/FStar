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
module LowStar.ConstBuffer

(* This module provides a model of const pointers in C.

   A well-typed client guarantees that it will not mutate memory
   through a const pointer. But it cannot rely on the context not
   mutating the same memory.

   As such, we model const pointers as a finite disjunction of
   {mutable, immutable}-pointers, forcing code to guarantee the
   strongest condition of the two (immutability) and to rely only on
   the weakest (i.e., mutability).

   The main type of this module is `const_buffer t`. It is extracted
   by KreMLin to  `const t*`.
*)

module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
open FStar.HyperStack.ST

module I = LowStar.ImmutableBuffer
module B = LowStar.Buffer

(*** A model for const pointers **)

/// We start by defining the finite disjunction of mutable and
/// immutable buffers.
///
/// NB: THIS IS FOR SPECIFICATIONAL PURPOSES ONLY
/// The concrete type `const_buffer` is defined later

/// `qual`: mutability qualifier
type qual =
  | MUTABLE
  | IMMUTABLE

/// `qbuf_cases q a`: disjunction of mutable and immutable pointers
let qbuf_cases (q:qual) (a:Type) =
  match q with
  | MUTABLE -> B.buffer a
  | IMMUTABLE -> I.ibuffer a

/// `q_preorder q a`: As we'll see shortly, it is convenient to also
/// define a disjunction of the preorder indices on a qualified
/// buffer
let q_preorder (q:qual) (a:Type) =
  match q with
  | MUTABLE -> B.trivial_preorder a
  | IMMUTABLE -> I.immutable_preorder a

/// `qbuf a`: This type is used for specificational purposes only. It
///  is buffer whose mutability qualifier is existentially bound, via
///  a dependent pair
let qbuf a = (q:qual & qbuf_cases q a)

/// `qbuf_qual c`: projecting the mutability qualifier of a `qbuf`
let qbuf_qual (c:qbuf 'a) : qual = dfst c

/// `qbuf_pre c`: case-dependent preorders for a qbuf
let qbuf_pre (c:qbuf 'a)  = q_preorder (qbuf_qual c) 'a

/// `qbuf_mbuf c`: turning a qbuf into a regular monotonic buffer
let qbuf_mbuf (c:qbuf 'a) : B.mbuffer 'a (qbuf_pre c) (qbuf_pre c) = dsnd c

(*** CONCRETE CONST POINTERS **)

/// `const_buffer`:
///  An abstract type of a read-only pointer to an array of `a`
val const_buffer (a:Type u#0) : Type u#0


/// `as_qbuf`: For specificational purposes, a const_buffer can be
/// seen as an existentially quantified qbuf
val as_qbuf (c:const_buffer 'a) : GTot (qbuf 'a)

/// `as_mbuf`: A convenience function to turn a const_buffer into a
/// regular mbuffer, for spec purposes
let as_mbuf (c:const_buffer 'a) : GTot _ = qbuf_mbuf (as_qbuf c)

/// We now give several convenience functions that lift common
/// notions on buffers to const_buffer, via the `as_mbuf` coercion
let live (h:HS.mem) (c:const_buffer 'a)   = B.live h (as_mbuf c)
let length (c:const_buffer 'a)            = B.length (as_mbuf c)
let loc_buffer (c:const_buffer 'a)        = B.loc_buffer (as_mbuf c)
let as_seq (h:HS.mem) (c:const_buffer 'a) = B.as_seq h (as_mbuf c)

(*** CONSTRUCTORS **)

/// `of_buffer`: A constructors for const buffers from mutable and
/// immutable buffers. It is fully specified in terms of the
/// `qbuf/mbuf` model
val of_buffer (b:B.buffer 'a)
  : Pure (const_buffer 'a)
    (requires True)
    (ensures fun c ->
      let c = as_qbuf c in
      qbuf_qual c == MUTABLE /\
      qbuf_mbuf c == b)

/// `of_ibuffer`: A constructors for const buffers from mutable and
/// immutable buffers. It is fully specified in terms of the
/// `qbuf/mbuf` model
val of_ibuffer (b:I.ibuffer 'a)
  : Pure (const_buffer 'a)
    (requires True)
    (ensures fun c ->
      let c = as_qbuf c in
      qbuf_qual c == IMMUTABLE /\
      qbuf_mbuf c == b)

(*** OPERATIONS ON CONST POINTERS **)

/// `index c i`: Very similar to the spec for `Buffer.index`
val index (c:const_buffer 'a) (i:U32.t)
  : Stack 'a
    (requires fun h ->
      live h c /\
      U32.v i < length c)
    (ensures fun h0 y h1 ->
      h0 == h1 /\
      y == Seq.index (as_seq h0 c) (U32.v i))

/// `sub`: A sub-buffer of a const buffer points to a given
/// within-bounds offset of its head
val sub (c:const_buffer 'a) (i len:U32.t)
  : Stack (const_buffer 'a)
    (requires fun h ->
      live h c /\
      U32.v i + U32.v len <= length c)
    (ensures fun h0 c' h1 ->
      let qc = as_qbuf c in
      let qc' = as_qbuf c' in
      h0 == h1 /\
      qbuf_qual qc == qbuf_qual qc' /\
      qbuf_mbuf qc' == B.mgsub (qbuf_pre qc) (qbuf_mbuf qc) i len)

/// `cast`: It is possible to cast away the const qualifier recovering
///  a mutable or immutable pointer, in case the context can prove
///  that `qbuf_qual c` is MUTABLE or IMMUTABLE, respectively
val cast (c:const_buffer 'a)
  : Pure (B.mbuffer 'a (qbuf_pre (as_qbuf c)) (qbuf_pre (as_qbuf c)))
    (requires True)
    (ensures fun x ->
      x == as_mbuf c)

val to_buffer (c:const_buffer 'a)
  : Pure (B.buffer 'a)
    (requires (
      let c = as_qbuf c in
      qbuf_qual c == MUTABLE))
    (ensures fun x ->
      x == as_mbuf c)

val to_ibuffer (c:const_buffer 'a)
  : Pure (I.ibuffer 'a)
    (requires (
      let c = as_qbuf c in
      qbuf_qual c == IMMUTABLE))
    (ensures fun x ->
      x == as_mbuf c)

////////////////////////////////////////////////////////////////////////////////
let test (x:B.buffer U32.t) (y:I.ibuffer U32.t)
  : Stack U32.t
    (requires fun h ->
      B.live h x /\
      B.live h y /\
      B.length x > 0 /\
      B.length y > 2 /\
      B.get h y 0 == 1ul /\
      B.get h y 1 == 2ul /\
      B.disjoint x y)
    (ensures fun h0 a h1 ->
      B.modifies (B.loc_buffer x) h0 h1 /\
      a == 4ul)
  = let c1 = of_buffer x in
    let c2 = of_ibuffer y in
    B.upd x 0ul 1ul;
    let a = index c1 0ul in
    assert (a == 1ul);
    let a' = index c2 0ul in
    assert (a' == 1ul);
    let c3 = sub c2 1ul 1ul in
    let a'' = index c3 0ul in
    assert (a'' == 2ul);
    U32.(a +^ a' +^ a'')
