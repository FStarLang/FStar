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

(* Pointer view and resource *)

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

(* Reading and writing using a pointer resource *)

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

(* Scoped allocation of pointer resources *)

(* Another (currently assumed) lemmas about loc_not_unused_in *)
assume val lemma_loc_not_unused_in_fresh_frame (l:B.loc) (h0 h1:HS.mem) 
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l /\ HS.fresh_frame h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l)) 

assume val lemma_loc_not_unused_in_popped (l:B.loc) (h0 h1:HS.mem) 
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l /\ HS.popped h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l)) 

unfold
let with_new_ptr_pre (res:resource) =
  pre:r_pre res{(forall h0 h1.{:pattern pre h0; HS.fresh_frame h0 h1} 
                   pre h0 /\ HS.fresh_frame h0 h1 ==> pre h1) /\
                (forall h0 h1.{:pattern pre h0; B.modifies B.loc_none h0 h1} 
                   pre h0 /\ B.modifies B.loc_none h0 h1 ==> pre h1)}

unfold
let with_new_ptr_post (res:resource) (a:Type) =
  post:r_post res a{(forall h0 h1 x h2.{:pattern B.modifies B.loc_none h0 h1; post h1 x h2} 
                       B.modifies B.loc_none h0 h1 /\ post h1 x h2 ==> post h0 x h2) /\
                    (forall h0 h1 x h2.{:pattern HS.fresh_frame h0 h1; post h1 x h2}
                       rst_inv res h0 /\ HS.fresh_frame h0 h1 /\ post h1 x h2 ==> post h0 x h2) /\ 
                    (forall h0 x h1 h2.{:pattern post h0 x h1; HS.popped h1 h2}
                       post h0 x h1 /\ HS.popped h1 h2 /\ rst_inv res h2 ==> post h0 x h2)}

let with_new_ptr (#res:resource)
                 (#a:Type)
                 (init:a)
                 (#b:Type)
                 (#pre:with_new_ptr_pre res)
                 (#post:with_new_ptr_post res b)
                 (f:(ptr:B.pointer a -> RST b (res <*> (ptr_resource ptr)) pre post)) 
               : RST b res pre post = 
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_view ();
  reveal_star ();
  reveal_ptr ();
  let h0 = get () in
  HST.push_frame ();
  let h1 = get () in
  lemma_loc_not_unused_in_fresh_frame (as_loc (fp res)) h0 h1;
  let ptr = B.alloca init 1ul in
  let h2 = get () in
  lemma_loc_not_unused_in_modifies (as_loc (fp res)) h1 h2;
  let x = f ptr in
  let h3 = get () in
  HST.pop_frame ();
  let h4 = get () in
  B.modifies_fresh_frame_popped h0 h1 (as_loc (fp (res <*> (ptr_resource ptr)))) h3 h4;
  lemma_loc_not_unused_in_popped (as_loc (fp res)) h3 h4;
  x
