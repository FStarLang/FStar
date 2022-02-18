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
module Demo.Deps
open LowStar.Buffer
open FStar.UInt32
module B = LowStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
open FStar.HyperStack.ST
effect St (a:Type)  = FStar.HyperStack.ST.St a

let buffer = B.buffer

let uint32 = U32.t
let uint8 = U8.t

unfold
let length (#a:Type) (b:buffer a) : GTot U32.t =
    U32.uint_to_t (B.length b)

unfold
let modifies (b:B.buffer 'a) h0 h1 = modifies (loc_buffer b) h0 h1

unfold
let live h (b:buffer 'a) = B.live h b

unfold
let ( .() ) (b:buffer 'a) (i:U32.t)
  : ST 'a (requires fun h -> live h b /\ i <^ length b)
         (ensures  (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))
  = B.index b i

unfold
let ( .()<- ) (b:buffer 'a) (i:U32.t) (v:'a)
  : ST unit 
    (requires (fun h -> 
      live h b /\
      i <^ length b))
    (ensures (fun h _ h' -> 
      modifies b h h' /\
      live h' b /\
      as_seq h' b == Seq.upd (as_seq h b) (U32.v i) v))
  = B.upd b i v

unfold
let suffix (#a:Type) 
           (b:buffer a)
           (from:U32.t) 
           (len:U32.t{len <=^ length b /\ from <=^ len})
  : ST (buffer a)
       (requires (fun h -> 
         U32.v from + U32.v len <= U32.v (length b) /\
         live h b))
       (ensures  (fun h y h' -> h == h' /\ y == mgsub _ b from (len -^ from)))
  = B.sub b from (len -^ from)

unfold
let disjoint (b0 b1:B.buffer 'a) = B.disjoint b0 b1

let lbuffer (len:U32.t) (a:Type) = b:B.buffer a{len <=^ length b}

let prefix_equal (#l:uint32) (#a:Type) 
                 (h:HS.mem)
                 (b1 b2: lbuffer l a)
                 (i:uint32{i <=^ l})
  : prop 
  = forall (j:uint32). j <^ i ==>
                  B.get h b1 (U32.v j) == B.get h b2 (U32.v j)

  


unfold
let ( <= ) x y = U32.(x <=^ y)

unfold
let ( < ) x y = U32.(x <^ y)

let ( + ) (x:U32.t) (y:U32.t{FStar.UInt.size (v x + v y) U32.n}) = U32.(x +^ y)

let op_Subtraction (x:U32.t) 
                   (y:U32.t{FStar.UInt.size (v x - v y) U32.n})
                   = U32.(x -^ y)

let malloc (init:'a) (len:U32.t)
  : ST (lbuffer len 'a)
       (requires fun h -> malloc_pre HS.root len)
       (ensures fun h0 b h1 ->
         alloc_post_mem_common b h0 h1 (Seq.create (U32.v len) init) /\
         freeable b)
  = B.malloc HS.root init len

let free (#a:Type0) (b:buffer a)
  : ST unit
       (requires fun h0 ->
         live h0 b /\
         freeable b)
       (ensures  (fun h0 _ h1 -> 
         Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
         (HS.get_tip h1) == (HS.get_tip h0) /\
         B.modifies (loc_addr_of_buffer b) h0 h1 /\
         HS.live_region h1 (frameOf b)))
 = B.free b

let get (h:HS.mem) (b:buffer 'a{ live h b }) (i:U32.t{ i < length b}) = 
  B.get h b (U32.v i)
