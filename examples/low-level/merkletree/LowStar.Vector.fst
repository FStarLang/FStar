module LowStar.Vector

open FStar.All
open FStar.Integers
open LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

type uint32_t = UInt32.t

val max_uint32: uint32_t
let max_uint32 = UInt32.uint_to_t (UInt.max_int UInt32.n)

module U32 = FStar.UInt32

/// Abstract vector type

noeq type vector_str a =
| Vec: sz:uint32_t ->
       cap:uint32_t{cap > 0ul && cap >= sz} ->
       vs:B.buffer a{B.len vs = cap} -> 
       vector_str a

val vector (a: Type0): Tot Type0
let vector a = vector_str a

/// Specification

val as_seq: HS.mem -> #a:Type -> vec:vector a -> GTot (S.seq a)
let as_seq h #a vec =
  B.as_seq h (B.gsub (Vec?.vs vec) 0ul (Vec?.sz vec))

/// Memory-related

unfold val live: #a:Type -> HS.mem -> vector a -> GTot Type0
unfold let live #a h vec =
  B.live h (Vec?.vs vec)

unfold val freeable: #a:Type -> vector a -> GTot Type0
unfold let freeable #a vec =
  B.freeable (Vec?.vs vec)

unfold val loc_vector: #a:Type -> vector a -> GTot loc
unfold let loc_vector #a vec =
  B.loc_buffer (Vec?.vs vec)

unfold val loc_addr_of_vector: #a:Type -> vector a -> GTot loc
unfold let loc_addr_of_vector #a vec =
  B.loc_addr_of_buffer (Vec?.vs vec)

unfold val frameOf: #a:Type -> vector a -> GTot Monotonic.HyperHeap.rid
unfold let frameOf #a vec =
  B.frameOf (Vec?.vs vec)

/// Capacity

unfold val size_of: #a:Type -> vec:vector a -> Tot uint32_t
unfold let size_of #a vec = 
  Vec?.sz vec

unfold val capacity_of: #a:Type -> vec:vector a -> Tot uint32_t
unfold let capacity_of #a vec =
  Vec?.cap vec

unfold val is_empty: #a:Type -> vec:vector a -> Tot bool
unfold let is_empty #a vec =
  size_of vec = 0ul

unfold val is_full: #a:Type -> vstr:vector_str a -> GTot bool
unfold let is_full #a vstr =
  Vec?.sz vstr >= max_uint32

/// Construction

val create_rid:
  #a:Type -> len:uint32_t{len > 0ul} -> v:a ->
  rid:Monotonic.HyperHeap.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = rid /\ 
	   live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (S.create (U32.v len) v)))
let create_rid #a len v rid =
  Vec len len (B.malloc rid v len)

val create: 
  #a:Type -> len:uint32_t{len > 0ul} -> v:a -> 
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = Monotonic.HyperHeap.root /\
	   live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (S.create (U32.v len) v)))
let create #a len v =
  create_rid len v Monotonic.HyperHeap.root

val create_reserve:
  #a:Type -> len:uint32_t{len > 0ul} -> ia:a ->
  rid:Monotonic.HyperHeap.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
	 (requires (fun h0 -> true))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = rid /\ live h1 vec /\ freeable vec /\
	   modifies loc_none h0 h1 /\
	   size_of vec = 0ul /\
	   S.equal (as_seq h1 vec) S.empty))
let create_reserve #a len ia rid =
  Vec 0ul len (B.malloc rid ia len)

val create_by_buffer:
  #a:Type -> len:uint32_t{len > 0ul} ->
  buf:B.buffer a{B.len buf = len} ->
  HST.ST (vector a)
	 (requires (fun h0 -> B.live h0 buf))
	 (ensures (fun h0 vec h1 -> 
	   frameOf vec = B.frameOf buf /\ loc_vector vec == B.loc_buffer buf /\
	   live h1 vec /\ h0 == h1 /\
	   size_of vec = len /\
	   S.equal (as_seq h1 vec) (B.as_seq h0 buf)))
let create_by_buffer #a len buf =
  Vec len len buf

/// Destruction

val free:
  #a:Type -> vec:vector a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ freeable vec))
    (ensures (fun h0 _ h1 -> modifies (loc_addr_of_vector vec) h0 h1))
let free #a vec =
  B.free (Vec?.vs vec)

/// Element access

val index: 
  #a:Type -> vec:vector a -> i:uint32_t -> 
  HST.ST a
    (requires (fun h0 -> live h0 vec /\ i < Vec?.sz vec))
    (ensures (fun h0 v h1 -> 
      h0 == h1 /\
      S.index (as_seq h1 vec) (U32.v i) == v))
let index #a vec i =
  B.index (Vec?.vs vec) i

val assign:
  #a:Type -> vec:vector a -> 
  i:uint32_t -> v:a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ i < Vec?.sz vec))
    (ensures (fun h0 _ h1 -> 
      modifies (loc_buffer (Vec?.vs vec)) h0 h1 /\
      S.equal (as_seq h1 vec) (S.upd (as_seq h0 vec) (U32.v i) v)))
let assign #a vec i v =
  B.upd (Vec?.vs vec) i v

/// Operations

private val resize_ratio: uint32_t
private let resize_ratio = 2ul

private val new_capacity: cap:uint32_t{cap > 0ul} -> Tot uint32_t
private let new_capacity cap =
  if cap >= max_uint32 / resize_ratio then max_uint32
  else cap * resize_ratio

val insert: 
  #a:Type -> vec:vector a -> v:a -> 
  HST.ST (vector a)
    (requires (fun h0 -> live h0 vec /\ not (is_full vec)))
    (ensures (fun h0 nvec h1 ->
      live h1 vec /\
      modifies (loc_union (loc_buffer (Vec?.vs vec)) 
			  (loc_buffer (Vec?.vs nvec))) h0 h1 /\
      S.equal (as_seq h1 nvec) (S.snoc (as_seq h0 vec) v)))
let insert #a vec v =
  let sz = Vec?.sz vec in
  let cap = Vec?.cap vec in
  let vs = Vec?.vs vec in
  if sz = cap 
  then (let ncap = new_capacity cap in
       // let nvs = B.malloc (B.frameOf vs) v ncap in
       let nvs = B.malloc Monotonic.HyperHeap.root v ncap in
       B.blit vs 0ul nvs 0ul sz;
       B.upd nvs sz v;
       // B.free vs; // TODO!
       Vec (sz + 1ul) ncap nvs)
  else
    (B.upd vs sz v;
    Vec (sz + 1ul) cap vs)

/// Iteration

val fold_left_seq:
  #a:Type -> #b:Type0 -> seq:S.seq a ->
  f:(b -> a -> Tot b) -> ib:b -> 
  GTot b (decreases (S.length seq))
let rec fold_left_seq #a #b seq f ib =
  if S.length seq = 0 then ib
  else fold_left_seq (S.tail seq) f (f ib (S.head seq))

val fold_left_buffer:
  #a:Type -> #b:Type0 -> len:uint32_t ->
  buf:B.buffer a{B.len buf = len} ->
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> B.live h0 buf))
    (ensures (fun h0 v h1 -> 
      h0 == h1 /\
      v == fold_left_seq (B.as_seq h0 buf) f ib))
    (decreases (B.length buf))
let rec fold_left_buffer #a #b len buf f ib =
  if len = 0ul then ib
  else (fold_left_buffer (len - 1ul) (B.sub buf 1ul (len - 1ul)) 
			 f (f ib (B.index buf 0ul)))

val fold_left:
  #a:Type -> #b:Type0 -> vec:vector a -> 
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\
      v == fold_left_seq (as_seq h0 vec) f ib))
let fold_left #a #b vec f ib =
  fold_left_buffer (Vec?.sz vec) (B.sub (Vec?.vs vec) 0ul (Vec?.sz vec)) f ib

val forall_prop_seq:
  #a:Type -> seq:S.seq a -> p:(a -> GTot Type0) -> GTot Type0
let forall_prop_seq #a seq p =
  forall (i:nat{i < S.length seq}). p (S.index seq i)

val forall_prop_buffer:
  #a:Type -> h:HS.mem -> buf:B.buffer a ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_prop_buffer #a h buf p =
  forall_prop_seq (B.as_seq h buf) p

val forall_prop: 
  #a:Type -> h:HS.mem -> vec:vector a -> 
  p:(a -> Tot Type0) -> GTot Type0
let forall_prop #a h vec p =
  forall_prop_seq (as_seq h vec) p

val forall_two_prop_seq:
  #a:Type -> seq:S.seq a -> p:(a -> a -> GTot Type0) -> GTot Type0
let forall_two_prop_seq #a seq p =
  forall (i:nat{i < S.length seq}) (j:nat{j < S.length seq && i <> j}).
    p (S.index seq i) (S.index seq j)

val forall_two_prop_buffer:
  #a:Type -> h:HS.mem -> buf:B.buffer a ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall_two_prop_buffer #a h buf p =
  forall_two_prop_seq (B.as_seq h buf) p

val forall_two_prop:
  #a:Type -> h:HS.mem -> vec:vector a -> 
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall_two_prop #a h vec p =
  forall_two_prop_seq (as_seq h vec) p


(*! Facts *)

val forall_prop_0:
  #a:Type -> h:HS.mem -> vec:vector a{size_of vec = 0ul} ->
  p:(a -> Tot Type0) ->
  Lemma (forall_prop h vec p)
let forall_prop_0 #a h vec p = ()

val forall_prop_1:
  #a:Type -> h:HS.mem -> vec:vector a{size_of vec = 1ul} ->
  p:(a -> Tot Type0) ->
  Lemma (forall_prop h vec p <==> p (S.index (as_seq h vec) 0))
let forall_prop_1 #a h vec p = ()

val forall_two_prop_0:
  #a:Type -> h:HS.mem -> vec:vector a{size_of vec = 0ul} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (forall_two_prop h vec p)
let forall_two_prop_0 #a h vec p = ()

val forall_two_prop_1:
  #a:Type -> h:HS.mem -> vec:vector a{size_of vec = 1ul} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (forall_two_prop h vec p)
let forall_two_prop_1 #a h vec p = ()

// val forall_prop_buffer_consistent:
//   #a:Type -> h:HS.mem -> len:uint32_t{len > 0ul} ->
//   buf:B.buffer a{B.len buf = len} ->
//   vec:vector a ->
//   p:(a -> Tot Type0) ->
//   Lemma (requires (S.equal (as_seq h vec) (B.as_seq h buf) /\
// 		  forall_prop_buffer h buf p))
// 	(ensures (forall_prop h vec p))
// let forall_prop_buffer_consistent #a h len buf vec p = ()

// val forall_two_prop_buffer_consistent:
//   #a:Type -> h:HS.mem -> len:uint32_t{len > 0ul} ->
//   buf:B.buffer a{B.len buf = len} ->
//   vec:vector a ->
//   p:(a -> a -> Tot Type0) ->
//   Lemma (requires (S.equal (as_seq h vec) (B.as_seq h buf) /\
// 		  forall_two_prop_buffer h buf p))
// 	(ensures (forall_two_prop h vec p))
// let forall_two_prop_buffer_consistent #a h len buf vec p = ()

