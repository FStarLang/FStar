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
module LowStar.RST.Pointer

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps

abstract
let ptr_view (#a:Type) (ptr:B.pointer a) : view a = 
  reveal_view ();
  let fp = Ghost.hide (B.loc_buffer ptr) in 
  let inv h = B.live h ptr in
  let sel h = Seq.index (B.as_seq h ptr) 0 in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let ptr_resource (#a:Type) (ptr:B.pointer a) = 
  as_resource (ptr_view ptr)

let reveal_ptr ()
  : Lemma ((forall a (ptr:B.pointer a) .{:pattern as_loc (fp (ptr_resource ptr))} 
             as_loc (fp (ptr_resource ptr)) == B.loc_buffer ptr) /\
           (forall a (ptr:B.pointer a) h .{:pattern inv (ptr_resource ptr) h} 
             inv (ptr_resource ptr) h <==> B.live h ptr) /\
           (forall a (ptr:B.pointer a) h .{:pattern sel (ptr_view ptr) h} 
             sel (ptr_view ptr) h == Seq.index (B.as_seq h ptr) 0)) = 
  ()

let ptr_read (#a:Type)
             (ptr:B.pointer a)
             (_:unit)
           : RST a (ptr_resource ptr) 
                   (fun _ -> True)
                   (fun h0 x h1 -> 
                      sel (ptr_view ptr) h0 == x /\ 
                      x == sel (ptr_view ptr) h1) =
  reveal_rst_inv ();
  !* ptr

let ptr_write (#a:Type)
              (ptr:B.pointer a)
              (x:a)
              (_:unit)
            : RST unit (ptr_resource ptr)
                       (fun _ -> True)
                       (fun _ _ h1 -> 
                          sel (ptr_view ptr) h1 == x) =
  reveal_rst_inv ();
  reveal_modifies ();
  ptr *= x

//let with_new_ptr_pre (res:resource)

(*
let with_new_ptr (#res:resource)
                 (#a:Type)
                 (init:a)
                 (#b:Type)
                 (#pre:r_pre res)
                 (#post:r_post res b)
                 (f:(ptr:B.pointer a -> RST b (res <*> (ptr_resource ptr)) pre post)) 
               : RST b res pre post = 
  reveal_rst_inv ();
  reveal_view ();
  reveal_star ();
  reveal_ptr ();
  HST.push_frame ();
  
  let ptr = B.alloca init 1ul in
  let h0 = get () in
  
  assert (inv res h0);
  assert (inv (ptr_resource ptr) h0);

  assert (r_disjoint res (ptr_resource ptr));
  
  assert (inv (res <*> (ptr_resource ptr)) h0);

  assert (pre h0);
  admit ();
  let (x:b) = f ptr in
  HST.pop_frame ();
  admit ()
*)
