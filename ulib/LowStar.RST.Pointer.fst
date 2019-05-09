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

open LowStar.RST
open LowStar.BufferOps

abstract
let r_ptr (#a:Type) (ptr:B.pointer a) : res:resource{res.view.t == a} = 
  let fp = Ghost.hide (B.loc_buffer ptr) in 
  let inv h = B.live h ptr in
  let view = (
    let sel (h:imem inv) = Seq.index (B.as_seq h ptr) 0 in 
    {
      t = a;
      sel = sel
    }) in 
  {
    fp = fp;
    inv = inv;
    view = view
  }

let reveal_ptr ()
  : Lemma ((forall a (ptr:B.pointer a) . as_loc (fp (r_ptr ptr)) == B.loc_buffer ptr) /\
           (forall a (ptr:B.pointer a) h . inv (r_ptr ptr) h <==> B.live h ptr) /\
           (forall a (ptr:B.pointer a) h . sel (r_ptr ptr) h == Seq.index (B.as_seq h ptr) 0)) =
  reveal ()

abstract
let r_ptr_read (#a:Type)
               (#ptr:B.pointer a)
               (_:unit)
             : RST a (r_ptr ptr) 
                     (fun _ -> True)
                     (fun h0 x h1 -> 
                        sel (r_ptr ptr) h0 == x /\ 
                        x == sel (r_ptr ptr) h1) =
  reveal ();
  !* ptr

abstract
let r_ptr_write (#a:Type)
                (#ptr:B.pointer a)
                (x:a)
              : RST unit (r_ptr ptr)
                         (fun _ -> True)
                         (fun _ _ h1 -> sel (r_ptr ptr) h1 == x) =
  reveal ();
  ptr *= x
