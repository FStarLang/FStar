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
open FStar.Buffer
open FStar.UInt32
module B = FStar.Buffer
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module HS = FStar.HyperStack
effect ST (a:Type) (pre:HS.mem -> Type0) (post:HS.mem -> a -> HS.mem -> Type0) = FStar.HyperStack.ST.ST a pre post
effect St (a:Type)  = FStar.HyperStack.ST.St a

let buffer = FStar.Buffer.buffer

let uint32 = U32.t
let uint8 = U8.t
unfold
let length (#a:Type) (b:buffer a) : GTot U32.t =
    U32.uint_to_t (B.length b)

unfold
let modifies1 = modifies_1

unfold
let live = B.live

unfold
let ( .() ) = Buffer.index

unfold
let ( .()<- ) = Buffer.upd

unfold
let ( <= ) x y = U32.(x <=^ y)

unfold
let ( < ) x y = U32.(x <^ y)

unfold
let op_Subtraction (x:U32.t) (y:U32.t{FStar.UInt.size (v x - v y) U32.n})
 = U32.(x -^ y)

unfold
let ( + ) (x:U32.t) (y:U32.t{FStar.UInt.size (v x + v y) U32.n}) = U32.(x +^ y)

unfold
let suffix (#a:Type) (b:buffer a) (from:U32.t) (len:U32.t{len <= length b /\ from <= len}) =
    B.sub b from (len - from)

unfold
let disjoint = Buffer.disjoint

let lbuffer (len:U32.t) (a:Type) = b:buffer a{len <= length b}

let prefix_equal (#l:uint32) (#a:Type) (h:HS.mem) (b1 b2: lbuffer l a) (i:uint32{i <= l}) =
  forall (j:uint32). j < i ==> Buffer.get h b1 (U32.v j) == Buffer.get h b2 (U32.v j)

  


