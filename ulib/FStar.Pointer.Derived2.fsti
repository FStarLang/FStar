module FStar.Pointer.Derived2
include FStar.Pointer.Base
include FStar.Pointer.Derived1

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let copy_buffer_contents_precond
  (#t: typ) (a: buffer t) (idx_a: UInt32.t) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t)
  (h: HS.mem)
  : GTot Type0 =
  (* source *)
  (* destination *)
  UInt32.v idx_a + UInt32.v len <= UInt32.v (buffer_length a) /\
  UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
  buffer_live h (gsub_buffer b idx_b len) /\ buffer_readable h (gsub_buffer a idx_a len) /\
  loc_disjoint (loc_buffer (gsub_buffer a idx_a len)) (loc_buffer (gsub_buffer b idx_b len))

let copy_buffer_contents_postcond
  (#t: typ) (a: buffer t) (idx_a: UInt32.t) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t)
  (h: HS.mem) (h': HS.mem)
  : GTot Type0 =
  (* source *)
  (* destination *)
  copy_buffer_contents_precond a idx_a b idx_b len h /\
  modifies (loc_buffer (gsub_buffer b idx_b len)) h h' /\
  buffer_readable h' (gsub_buffer b idx_b len) /\
  buffer_as_seq h' (gsub_buffer b idx_b len) == buffer_as_seq h (gsub_buffer a idx_a len)

val copy_buffer_contents: 
  #t: typ ->
  a:
  (* source *)
  buffer t ->
  idx_a: UInt32.t ->
  b:
  (* destination *)
  buffer t ->
  idx_b: UInt32.t ->
  len: UInt32.t ->
  HST.Stack unit
    (requires (fun h -> copy_buffer_contents_precond a idx_a b idx_b len h))
    (ensures (fun h0 _ h1 -> copy_buffer_contents_postcond a idx_a b idx_b len h0 h1))

