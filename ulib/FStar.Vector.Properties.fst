 (*
      Copyright 2008-2017 Microsoft Research

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

module FStar.Vector.Properties
open FStar.Vector.Base
module S = FStar.Seq
module U32 = FStar.UInt32

/// This coercion seems to be necessary in some places
///
/// For example,  when trying to treat a    `raw a (l1 +^ l2)`
///                                    as a `raw a (m1 +^ m2)`
/// F* type inference tries matches on the head symbol of the index
/// and tries to prove `l1 = m1 /\ l2 = m2`
/// which is often too strong.
/// This coercion is a workaround for in such cases
unfold
let coerce
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (m:len_t{l == m})
  : Tot (raw a m)
  = v

/// An abbreviation that states that some binary arithmetic
/// operation on len_t's respects bouns
unfold
let ok
    (op:int -> int -> int)
    (l1:len_t)
    (l2:len_t)
  : Type
  = UInt.size U32.(op (v l1) (v l2)) U32.n

/// Most lemmas from FStar.Seq.Properties can just be lifted
/// to vectors, although the lengths have to be bounds checked
let append_inj
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (#m1:len_t)
    (#m2:len_t)
    (u1:raw a l1)
    (u2:raw a l2{ok (+) l1 l2})
    (v1:raw a m1)
    (v2:raw a m2{ok (+) m1 m2})
  : Lemma
    (requires (let open U32 in
               m1 +^ m2 = l1 +^ l2 /\
               equal (u1@|u2) (coerce (v1@|v2) (l1 +^ l2)) /\
               (l1 == m1 \/ l2 == m2)))
    (ensures (l1 = m1 /\
              l2 = m2 /\
              equal u1 v1 /\
              equal u2 v2))
  = FStar.Seq.lemma_append_inj (reveal u1) (reveal u2) (reveal v1) (reveal v2)

let head (#a:Type) (#l:len_t{l <> 0ul}) (v:raw a l)
  : Tot a
  = v.[0ul]

let tail (#a:Type) (#l:len_t{l <> 0ul}) (v:raw a l)
  : Tot (raw a U32.(l -^ 1ul))
  = sub v 1ul l

let head_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 <> 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (head (v1@|v2) == head v1))
  = ()

let tail_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 <> 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (tail (v1@|v2) == tail v1@|v2))
  = Seq.lemma_tail_append (reveal v1) (reveal v2)

/// and so on ...
