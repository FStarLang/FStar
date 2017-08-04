
module Test 

open FStar.List.Tot.Base
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.BaseTypes
open FStar.Buffer
open Manifest
open FStar.UInt32
open FStar.Int.Cast
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let buf_size = 0xffff
let bitmap_size = 0xff
type memory = (sgxmem:(buffer uint8){length sgxmem == buf_size})


assume val in_u_component: (l:umemlayout)->(ptr:uint32) -> Pure bool
(requires  true)
(ensures (fun _ -> ptr <=^ 65535ul))  

(* Ensures that all return addresses in the bitmap are set to zero 
*  QUESTION: How do we know top of the stack? From manifest, we only know stack start and end!!
*)
assume val wellformed: (m:memory) -> (l:umemlayout)-> (h:mem) -> GTot bool
(* Checks if a bit is set in bitmap *)
assume val bitmap_is_set: (m:memory)->(ptr:uint32)->GTot bool
assume val set_bitmap: (m:memory)->(ptr:uint32)->GTot bool
assume val unset_bitmap:(m:memory)->(ptr:uint32)->GTot bool


effect Sgx (a:Type) (pre:st_pre) (post: (mem -> Tot (st_post a))) = 
	     STATE a
              (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1 /\ equal_stack_domains h h1) ==> p a h1)) (* WP *)


(* copy srcidx + size bytes into dstidx + size. Requires that
 *  1. Bitmap is well-formed i.e., return addresses of U are marked as zero
 *  2. Bits corresponding to (dstidx, dst+size) are set in the bitmap
 *  3. Bitmap is not modified
 *  4. Bitmap is well-formed (follows from (3)) after the memcpy
 *)
val memcpy: (l:umemlayout)-> (m:memory)-> (srcidx:uint32) -> (dstidx: uint32) -> (size: uint8)->Sgx unit
 (requires (fun h -> (if (in_u_component l srcidx) && (in_u_component l dstidx) then (forall (i:uint8{UInt8.lte i size}). bitmap_is_set m (dstidx +^ (uint8_to_uint32 i))) 
           else true) /\ (wellformed m l h) 
	   ))
 (ensures (fun h0 r h1 -> wellformed m l h1)) 


(* allocate in U's heap 
* 1. Requires that bitmap is well-formed
* 2. Bitmap is modified only for U's heap regions
* 3. Bitmap is well-formed after malloc
*)
val umalloc: (l:umemlayout)-> (m:memory)->(size: uint8)->Sgx unit
 (requires (fun h -> (wellformed m l h) 
	   ))
 (ensures (fun h0 r h1 -> wellformed m l h1 /\
                      modifies_1 m h0 h1 /\ 
		      (* In Progress: compare only bitmaps; compare only bits corresponding to stack *)
		      slice (as_seq h1 m) stackstart stackend == Seq.upd (as_seq h0 m) 0 (UInt32.v 1ul)
	  )) 

val ufree: (l:umemlayout)-> (m:memory)->(ptr: uint32)->Sgx unit
 (requires (fun h -> (wellformed m l h) 
	   ))
 (ensures (fun h0 r h1 -> wellformed m l h1 /\
                      modifies_1 m h0 h1 /\ 
		      (* In Progress: compare only bitmaps; compare only bits corresponding to stack *)
		      as_seq h1 m == Seq.upd (as_seq h0 m) 0 (UInt32.v 0ul)
	  )) 


