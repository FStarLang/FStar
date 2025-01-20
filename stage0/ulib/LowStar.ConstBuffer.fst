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

module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
open FStar.HyperStack.ST

module I = LowStar.ImmutableBuffer
module B = LowStar.Buffer

let const_buffer a = qbuf a

let as_qbuf c = c

let of_buffer b = (| MUTABLE, b |)

let of_ibuffer b = (| IMMUTABLE, b |)

let of_qbuf #_ #q b = (| q, b |)

let is_null #a c =
  let x = qbuf_mbuf c in
  B.is_null x

let index c i =
  let x = qbuf_mbuf c in
  B.index x i

let sub #a c i len =
  let (| q, x |) = c in
  let x : B.mbuffer a (q_preorder q a) (q_preorder q a) = x in
  let y = B.msub (q_preorder q a) x i len in
  (| q, y |)

let cast c = qbuf_mbuf c
let to_buffer c = qbuf_mbuf c
let to_ibuffer c = qbuf_mbuf c
