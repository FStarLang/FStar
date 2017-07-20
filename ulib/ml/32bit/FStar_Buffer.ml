
let disjoint_only_lemma t b t' b' = ()
let eq_lemma h0 h1 size a mods = ()
let modifies_transitivity_lemma mods h0 h1 h2 = ()
let modifies_subset_lemma mods submods h0 h1 = ()
let modifies_empty_lemma h = ()
let modifies_fresh_lemma h0 h1 mods size b = ()

type ('a, 'b, 'c, 'd) disjoint = unit
type ('a, 'b, 'c) live = unit

type abuffer = | Buff of (unit * unit)

type uint32 = FStar_UInt32.t
let zero = FStar_UInt32.zero

type 'a buffer = {
    content:'a array;
    idx: uint32;
    length: int;
  }

type uint8s = FStar_UInt8.uint8 buffer
type uint32s = FStar_UInt32.uint32 buffer
type uint64s = FStar_UInt64.uint64 buffer
type uint128s = FStar_UInt128.uint128 buffer

type u9 = FStar_UInt8.t
type u32 = FStar_UInt32.t
type u64 = FStar_UInt64.t
type u128 = FStar_UInt128.t

let create init len = {content = Array.make (Int64.to_int len) init; idx = zero; length = Int64.to_int len}
let createL l = {content = Array.of_list l; idx = zero; length = List.length l}
let rcreate r init len = create init len

let index b n =
  let idx = Int64.to_int (Int64.add n b.idx) in
   Array.get b.content idx

let upd (b:'a buffer) (n:uint32) (v:'a) =
  let idx = Int64.to_int (Int64.add n b.idx) in
  Array.set b.content idx v

let sub b i len = {content = b.content; idx = Int64.add b.idx i; length = Int64.to_int len}
let offset b i  = {content = b.content; idx = Int64.add b.idx i; length = b.length - (Int64.to_int i)}

let blit a idx_a b idx_b len =
  let ida = Int64.to_int (Int64.add idx_a b.idx) in
  let idb = Int64.to_int (Int64.add idx_b b.idx) in
  Array.blit a.content ida b.content idb (Int64.to_int len)

let fill a z len = Array.fill a.content 0 (Int64.to_int len) z
let split a i =
  let al = Int64.of_int a.length in
  (sub a zero i, sub a i (Int64.sub al i))
let of_seq s l = ()
let copy b l =
  {content = Array.sub b.content (Int64.to_int b.idx) (Int64.to_int l); idx = zero; length = Int64.to_int l}

let eqb b1 b2 len =
  Array.sub b1.content (Int64.to_int b1.idx) (Int64.to_int len) 
  = Array.sub b2.content (Int64.to_int b2.idx) (Int64.to_int len)

type ('a, 'b, 'c, 'd) modifies_buf = ()
let op_Plus_Plus a b = BatSet.empty
let only a = BatSet.empty

let op_Array_Access b n = index b n
let op_Array_Assignment b n v = upd b n v

let recall = fun b -> ()

let to_seq_full b = Obj.magic ()
