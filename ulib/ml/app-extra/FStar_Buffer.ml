
let disjoint_only_lemma t b t' b' = ()
let eq_lemma h0 h1 size a mods = ()
let modifies_transitivity_lemma mods h0 h1 h2 = ()
let modifies_subset_lemma mods submods h0 h1 = ()
let modifies_empty_lemma h = ()
let modifies_fresh_lemma h0 h1 mods size b = ()

type ('a, 'b, 'c, 'd) disjoint = unit
type ('a, 'b, 'c) live = unit

type abuffer = | Buff of (unit * unit)

type 'a buffer = {
    content:'a array;
    idx:int;
    length:int;
  }

type u8   = FStar_UInt8.t
type u32  = FStar_UInt32.t
type u64  = FStar_UInt64.t
type u128 = FStar_UInt128.t

type uint8s   = u8 buffer
type uint32s  = u32 buffer
type uint64s  = u64 buffer
type uint128s = u128 buffer

let create init len = {content = Array.make len init; idx = 0; length = len}
let createL l = {content = Array.of_list l; idx = 0; length = List.length l}
let rcreate r init len = create init len
let index b n = Array.get b.content (n+b.idx)
let upd (b:'a buffer) (n:u32) (v:'a) = Array.set b.content (FStar_UInt32.to_native_int n + b.idx) v
let sub b i len = {content = b.content; idx = b.idx+i; length = len}
let offset b i  = {content = b.content; idx = b.idx+i; length = b.length-i}
let blit a idx_a b idx_b len =
    let idx_a = FStar_UInt32.to_native_int idx_a in
    let idx_b = FStar_UInt32.to_native_int idx_b in
    let len   = FStar_UInt32.to_native_int len   in
    Array.blit a.content (idx_a+a.idx) b.content (idx_b+b.idx) len

let fill a z len = Array.fill a.content a.idx (FStar_UInt32.to_native_int len) z
let split a i = (sub a 0 i, sub a i (a.length - i))
let of_seq s l = ()
let copy b l = {content = Array.sub b.content b.idx l; idx = 0; length = l}

let eqb b1 b2 (len:u32) =
  Array.sub b1.content b1.idx (FStar_UInt32.to_native_int len) = Array.sub b2.content b2.idx (FStar_UInt32.to_native_int len)

type ('a, 'b, 'c, 'd) modifies_buf = unit
let op_Plus_Plus a b = BatSet.empty
let only a = BatSet.empty

let op_Array_Access b n = index b n
let op_Array_Assignment b n v = upd b n v

let recall = fun b -> ()

let of_ocaml_array a = {
   content = a;
   idx = 0;
   length = Array.length a
}

(* AR: revisit. This is used in the idealization code of AEAD encrypt *)
let to_seq_full b = Obj.magic ()

