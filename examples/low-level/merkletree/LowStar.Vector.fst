module LowStar.Vector

open FStar.All
open FStar.Integers
open LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

type uint32_t = UInt32.t

val max_uint32: uint32_t
let max_uint32 = UInt32.uint_to_t (UInt.max_int UInt32.n)

let root = Monotonic.HyperHeap.root

/// Abstract vector type

noeq type vector_str a =
| Vec: sz:uint32_t{sz > 0ul} ->
       cap:uint32_t{cap >= sz} ->
       vs:B.buffer a{B.len vs = cap} -> 
       vector_str a

val vector (a: Type0): Tot Type0
let vector a = vector_str a

/// Construction

val create: 
  #a:Type -> len:uint32_t{len > 0ul} -> a -> 
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 -> modifies loc_none h0 h1))
let create #a n v =
  Vec n n (B.malloc root v n)

/// Heap conditions

val live: #a:Type -> HS.mem -> vector a -> GTot Type0
let live #a h vec =
  B.live h (Vec?.vs vec)

/// Capacity

val size_of: #a:Type -> vec:vector a -> Tot uint32_t
let size_of #a vec = 
  Vec?.sz vec

val capacity_of: #a:Type -> vec:vector a -> Tot uint32_t
let capacity_of #a vec =
  Vec?.cap vec

val is_empty: #a:Type -> vec:vector a -> Tot bool
let is_empty #a vec =
  size_of vec = 0ul

val is_full: #a:Type -> vstr:vector_str a -> GTot bool
let is_full #a vstr =
  Vec?.sz vstr >= max_uint32

/// Element access

val index: 
  #a:Type -> vec:vector a -> i:uint32_t -> 
  HST.ST a
    (requires (fun h0 -> live h0 vec /\ i < Vec?.sz vec))
    (ensures (fun h0 _ h1 -> h0 == h1))
let index #a vec i =
  B.index (Vec?.vs vec) i

val assign:
  #a:Type -> vec:vector a -> 
  i:uint32_t -> v:a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ i < Vec?.sz vec))
    (ensures (fun h0 _ h1 -> modifies (loc_buffer (Vec?.vs vec)) h0 h1))
let assign #a vec i v =
  B.upd (Vec?.vs vec) i v

/// Operations

private val resize_ratio: uint32_t
private let resize_ratio = 2ul

private val new_capacity: uint32_t -> Tot uint32_t
private let new_capacity cap =
  if cap >= max_uint32 / resize_ratio then max_uint32
  else cap * resize_ratio

val insert: 
  #a:Type -> vec:vector a -> v:a -> 
  HST.ST (vector a)
    (requires (fun h0 ->
      live h0 vec /\ not (is_full vec)))
    (ensures (fun h0 nvec h1 ->
      modifies (loc_union (loc_buffer (Vec?.vs vec)) 
			  (loc_buffer (Vec?.vs nvec))) h0 h1 /\
      Vec?.sz nvec = Vec?.sz vec + 1ul /\
      B.as_seq h1 (B.gsub (Vec?.vs nvec) 0ul (Vec?.sz vec)) ==
      B.as_seq h0 (B.gsub (Vec?.vs vec) 0ul (Vec?.sz vec)) /\
      B.get h1 (Vec?.vs nvec) (UInt32.v (Vec?.sz vec)) == v))
let insert #a vec v =
  let sz = Vec?.sz vec in
  let cap = Vec?.cap vec in
  let vs = Vec?.vs vec in
  if sz = cap then
    (let ncap = new_capacity cap in
    let nvs = B.malloc root v ncap in
    B.blit vs 0ul nvs 0ul sz;
    B.upd nvs sz v;
    Vec (sz + 1ul) ncap nvs)
  else
    (B.upd vs sz v;
    Vec (sz + 1ul) cap vs)

