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
   by KaRaMeL to  `const t*`.
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
[@@erasable]
noeq
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
inline_for_extraction
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
val as_qbuf (c:const_buffer 'a) : Tot (qbuf 'a)

/// `qual_of`:
let qual_of (#a:_) (c:const_buffer a)
  : Tot qual
  = dfst (as_qbuf c)

/// `as_mbuf`: A convenience function to turn a const_buffer into a
/// regular mbuffer, for spec purposes
let as_mbuf (c:const_buffer 'a) : GTot _ = qbuf_mbuf (as_qbuf c)

/// We now give several convenience functions that lift common
/// notions on buffers to const_buffer, via the `as_mbuf` coercion
let live (h:HS.mem) (c:const_buffer 'a)    = B.live h (as_mbuf c)
let length (c:const_buffer 'a)             = B.length (as_mbuf c)
let loc_buffer (c:const_buffer 'a)         = B.loc_buffer (as_mbuf c)
let loc_addr_of_buffer (c:const_buffer 'a) = B.loc_addr_of_buffer (as_mbuf c)
let as_seq (h:HS.mem) (c:const_buffer 'a)  = B.as_seq h (as_mbuf c)
let g_is_null (c:const_buffer 'a)          = B.g_is_null (as_mbuf c)

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


/// `of_qbuf`: A constructors for const buffers from either mutable and
/// immutable buffers. It is fully specified in terms of the
/// `qbuf/mbuf` model
val of_qbuf (#q:qual) (b:B.mbuffer 'a (q_preorder q 'a) (q_preorder q 'a))
  : Pure (const_buffer 'a)
    (requires True)
    (ensures fun c ->
      let c = as_qbuf c in
      qbuf_qual c == q /\
      qbuf_mbuf c == b)

/// null constant buffer
let null 'a : const_buffer 'a = of_buffer B.null

(*** OPERATIONS ON CONST POINTERS **)

/// Is the buffer the null pointer?
val is_null (c:const_buffer 'a)
  : Stack bool (requires (fun h -> live h c))
               (ensures  (fun h y h' -> h == h' /\ y == g_is_null c))


/// `index c i`: Very similar to the spec for `Buffer.index`
val index (c:const_buffer 'a) (i:U32.t)
  : Stack 'a
    (requires fun h ->
      live h c /\
      U32.v i < length c)
    (ensures fun h0 y h1 ->
      h0 == h1 /\
      y == Seq.index (as_seq h0 c) (U32.v i))


/// Specification of sub
let gsub (c:const_buffer 'a) (i:U32.t) (len:U32.t{U32.v i + U32.v len <= length c})
  : GTot (const_buffer 'a)
  = let qc = as_qbuf c in
    of_qbuf (B.mgsub (qbuf_pre qc) (qbuf_mbuf qc) i len)

/// Relational specification of sub
let const_sub_buffer (i:U32.t) (len:U32.t) (csub c:const_buffer 'a) =
  let qc = as_qbuf c in
  let qcsub = as_qbuf csub in
  U32.v i + U32.v len <= length c /\
  csub == gsub c i len

/// `sub`: A sub-buffer of a const buffer points to a given
/// within-bounds offset of its head
val sub (#a:_) (c:const_buffer a) (i:U32.t) (len:Ghost.erased (U32.t))
  : Stack (const_buffer a)
    (requires fun h ->
      live h c /\
      U32.v i + U32.v len <= length c)
    (ensures fun h0 c' h1 ->
      let qc = as_qbuf c in
      let qc' = as_qbuf c' in
      h0 == h1 /\
      c' `const_sub_buffer i len` c)

/// Discussion between NS and JP (20191119)
///
/// Why is it safe to generate C code that casts away the const qualifier with the
/// cast operations below? Looking at the C11 standard, 6.7.3 alinea 6:
///
/// > If an attempt is made to modify an object defined with a const-qualified type
/// > through useof an lvalue with non-const-qualified type, the behavior is
/// > undefined.
///
/// So, dangerous things happen in situations where the original object is *created*
/// with a const qualifier (the object's _identity_ is const).
///
/// ```
/// #include <stdio.h>
/// #include <stdlib.h>
///
/// extern void f(const int *x);
///
/// int main() {
///   const int x = 0;
///   f(&x); // f promises not to modify x
///   printf("%d\n", x); // prints 0 at -O3 but 1 at -O0
///   return 0;
/// }
/// ```
///
/// with:
///
/// ```
/// void f(const int *x) {
///   int *y = (int *)x;
///   *y = 1;
/// }
/// ```
///
/// In Low*, however, we never create objects that are marked const from the start.
/// This is for historical reasons; in particular, immutable buffers are not marked
/// const (they certainly could be).
///
/// So, the casts seem to be safe? Also, the difference in behavior noted above
/// does not happen if x is defined as
///
/// ```
///   const int *x = calloc(1, sizeof *x);
/// ```
///
/// Finally, the compiler, if the const qualifier is stripped from x, could still
/// potentially rely on an argument of freshness (pointer provenance?) to deduce
/// that &x is the sole pointer to x and that therefore the value of x should remain
/// the same. This does not seem to be happening.

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
