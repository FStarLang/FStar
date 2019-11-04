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
module FStar.Pointer.Derived2
include FStar.Pointer.Base
include FStar.Pointer.Derived1

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let copy_buffer_contents_precond
  (#t: typ)
  (a: buffer t) (* source *)
  (idx_a: UInt32.t)
  (b: buffer t) (* destination *)
  (idx_b: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: GTot Type0
= UInt32.v idx_a + UInt32.v len <= UInt32.v (buffer_length a) /\
  UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
  buffer_live h (gsub_buffer b idx_b len) /\
  buffer_readable h (gsub_buffer a idx_a len) /\
  loc_disjoint (loc_buffer (gsub_buffer a idx_a len)) (loc_buffer (gsub_buffer b idx_b len))

let copy_buffer_contents_postcond
  (#t: typ)
  (a: buffer t) (* source *)
  (idx_a: UInt32.t)
  (b: buffer t) (* destination *)
  (idx_b: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
  (h' : HS.mem)
: GTot Type0
= copy_buffer_contents_precond a idx_a b idx_b len h /\
  modifies (loc_buffer (gsub_buffer b idx_b len)) h h' /\
  buffer_readable h' (gsub_buffer b idx_b len) /\
  buffer_as_seq h' (gsub_buffer b idx_b len) == buffer_as_seq h (gsub_buffer a idx_a len)

val copy_buffer_contents
  (#t: typ)
  (a: buffer t) (* source *)
  (idx_a: UInt32.t)
  (b: buffer t) (* destination *)
  (idx_b: UInt32.t)
  (len: UInt32.t)
: HST.Stack unit
  (requires (fun h ->
    copy_buffer_contents_precond a idx_a b idx_b len h
  ))
  (ensures (fun h0 _ h1 ->
    copy_buffer_contents_postcond a idx_a b idx_b len h0 h1
  ))
