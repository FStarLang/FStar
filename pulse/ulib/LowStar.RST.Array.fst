(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.RST.Array

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps

abstract
let array_view (#a:Type) (ptr:B.buffer a) : view (Seq.seq a) =
  reveal_view ();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr) in 
  let inv h = B.live h ptr /\ B.freeable ptr in
  let sel h = B.as_seq h ptr in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let array_resource (#a:Type) (ptr:B.buffer a) = 
  as_resource (array_view ptr)

let reveal_array ()
  : Lemma ((forall a (ptr:B.buffer a) .{:pattern as_loc (fp (array_resource ptr))} 
             as_loc (fp (array_resource ptr)) == B.loc_addr_of_buffer ptr) /\
           (forall a (ptr:B.buffer a) h .{:pattern inv (array_resource ptr) h} 
             inv (array_resource ptr) h <==> B.live h ptr /\ B.freeable ptr) /\
           (forall a (ptr:B.buffer a) h .{:pattern sel (array_view ptr) h} 
             sel (array_view ptr) h == B.as_seq h ptr)) = 
  ()

let index (#a:Type) (ptr:B.buffer a) (i:UInt32.t)
  : RST a (array_resource ptr)
          (fun _ -> array_resource ptr)
          (fun _ -> UInt32.v i < B.length ptr)
          (fun h0 x h1 ->
             UInt32.v i < B.length ptr /\
             Seq.index (sel (array_view ptr) h0) (UInt32.v i) == x /\
                     sel (array_view ptr) h0 == sel (array_view ptr) h1)
  = B.index ptr i

let upd (#a:Type) (ptr:B.buffer a) (i:UInt32.t) (v:a)
  : RST unit (array_resource ptr)
             (fun _ -> array_resource ptr)
             (fun _ -> UInt32.v i < B.length ptr)
             (fun h0 _ h1 -> UInt32.v i < B.length ptr /\
               sel (array_view ptr) h1 == 
                 Seq.upd (sel (array_view ptr) h0) (UInt32.v i) v)
  =
  reveal_rst_inv();
  reveal_modifies();
  B.upd ptr i v

let malloc (#a:Type) (init:a) (len:UInt32.t)
  : RST (B.buffer a) (empty_resource)
                     (fun ptr -> array_resource ptr)
                     (fun _ -> UInt32.v len > 0)
                     (fun _ ptr h1 -> sel (array_view ptr) h1 == Seq.create (UInt32.v len) init)
  = 
  reveal_rst_inv();
  reveal_modifies();
  B.malloc HS.root init len

let free (#a:Type) (ptr:B.buffer a)
  : RST unit (array_resource ptr)
             (fun _ -> empty_resource)
             (fun _ -> True)
             (fun _ _ _ -> True)
   =
   reveal_empty_resource();
   reveal_rst_inv();
   reveal_modifies();
   B.free ptr
