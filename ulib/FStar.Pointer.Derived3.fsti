module FStar.Pointer.Derived3
include FStar.Pointer.Base
include FStar.Pointer.Derived1
// include FStar.Pointer.Derived2 // useless here

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let fill_buffer_precond (#t: typ) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t) (h: HS.mem)
  : GTot Type0 =
  (* destination *)
  UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
  buffer_live h (gsub_buffer b idx_b len)

let fill_buffer_postcond
  (#t: typ) (b: buffer t) (idx_b: UInt32.t) (len: UInt32.t) (v: type_of_typ t) (h: HS.mem)
  (h': HS.mem)
  : GTot Type0 =
  (* destination *)
  fill_buffer_precond b idx_b len h /\ modifies (loc_buffer (gsub_buffer b idx_b len)) h h' /\
  buffer_readable h' (gsub_buffer b idx_b len) /\
  buffer_as_seq h' (gsub_buffer b idx_b len) == Seq.create (UInt32.v len) v

val fill_buffer: 
  #t: typ ->
  b:
  (* destination *)
  buffer t ->
  idx_b: UInt32.t ->
  len: UInt32.t ->
  v: type_of_typ t ->
  HST.Stack unit
    (requires (fun h -> fill_buffer_precond b idx_b len h))
    (ensures (fun h0 _ h1 -> fill_buffer_postcond b idx_b len v h0 h1))

