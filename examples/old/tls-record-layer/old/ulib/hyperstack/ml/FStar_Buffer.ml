
type ('a, 'b, 'c, 'd) disjoint = unit
type ('a, 'b, 'c) live = unit

type abuffer = unit
                           
type uint32 = FStar_UInt32.uint32

type 'a buffer = {
    content:'a array;
    idx:uint32;
    length:uint32;
  }                   

(* type suint8s = SInt_UInt8.uint8 buffer *)
                
let create init len = {content = Array.make len init; idx = 0; length = len}
let index b n = Array.get b.content (n+b.idx)
let upd b n v = Array.set b.content (n+b.idx) v
let sub b i len = {content = b.content; idx = b.idx+i; length = len}
let offset b i  = {content = b.content; idx = b.idx+i; length = b.length-i}
let blit a idx_a b idx_b len = Array.blit a.content (idx_a+a.idx) b.content (idx_b+b.idx) len
let split a i = (sub a 0 i, sub a i (a.length - i))
let of_seq s l = ()
let copy b l = {content = Array.sub b.content b.idx l; idx = 0; length = l} 
                
