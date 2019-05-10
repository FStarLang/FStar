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
module LowStar.RST

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Resource

(* State effect indexed by a resource *)

let r_pre (res:resource) = imem (inv res) -> Type0
let r_post (res:resource) (a:Type) = imem (inv res) -> a -> imem (inv res) -> Type0

effect RST (a:Type)
           (res:resource)
           (pre:r_pre res)
           (post:r_post res a) = 
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               inv res h0 /\               //Require the resource invariant
               pre h0 /\                   //Require the pre-condition
               (forall (x:a) (h1:HS.mem).
                 inv res h1 /\                          //Ensure the resource invariant
                 modifies res h0 h1 /\                  //Ensure that only resource's footprint is modified
                 post h0 x h1 ==>                       //Ensure the post-condition
                 k x h1))                               //prove the continuation under this hypothesis

(* Left and right framing operations for RST computations *)

unfold
let frame_left_pre (#fp:resource)
                   (#frame:resource)
                   (pre:r_pre fp)
                   (h:imem (inv (fp <*> frame))) = 
  pre h

unfold
let frame_left_post (#fp:resource)
                    (#frame:resource)
                    (#a:Type)
                    (post:r_post fp a)
                    (h0:imem (inv (fp <*> frame)))
                    (x:a)
                    (h1:imem (inv (fp <*> frame))) =
  post h0 x h1 /\
  sel (view_of frame) h0 == sel (view_of frame) h1

let frame_left (#frame:resource)
               (#a:Type)
               (#fp:resource)
               (#pre:r_pre fp)
               (#post:r_post fp a)
               ($f:unit -> RST a fp pre post)
             : RST a (fp <*> frame)
                     (frame_left_pre pre) 
                     (frame_left_post post) =
  reveal_view ();
  reveal_star ();
  reveal_modifies ();
  f ()

unfold
let frame_right_pre (#frame:resource)
                    (#fp:resource)
                    (pre:r_pre fp)
                    (h:imem (inv (frame <*> fp))) = 
  pre h

unfold
let frame_right_post (#frame:resource)
                     (#fp:resource)
                     (#a:Type)
                     (post:r_post fp a)
                     (h0:imem (inv (frame <*> fp)))
                     (x:a)
                     (h1:imem (inv (frame <*> fp))) =
  post h0 x h1 /\
  sel (view_of frame) h0 == sel (view_of frame) h1

let frame_right (#frame:resource)
                (#a:Type)           
                (#fp:resource)
                (#pre:r_pre fp)
                (#post:r_post fp a)
                ($f:unit -> RST a fp pre post)
              : RST a (frame <*> fp) 
                      (frame_right_pre pre) 
                      (frame_right_post post) =
  reveal_view ();
  reveal_star ();
  reveal_modifies ();
  f ()

(* Generic frame operation for RST computations (through resource inclusion) *)

unfold
let frame_pre (#outer:resource)
              (#inner:resource)
              (delta:r_includes outer inner)
              (pre:r_pre inner)
              (h:imem (inv outer)) =
  pre h

unfold
let frame_post (#outer:resource)
               (#inner:resource)
               (delta:r_includes outer inner)
               (#a:Type)
               (post:r_post inner a)
               (h0:imem (inv outer))
               (x:a)
               (h1:imem (inv outer)) = 
  post h0 x h1 /\
  sel (view_of delta) h0 == sel (view_of delta) h1
  
let frame (#a:Type)
          (#outer:resource)
          (#inner:resource)
          (delta:r_includes outer inner)  // eventually we will want to infer this argument through metaprogramming
          (#pre:r_pre inner)
          (#post:r_post inner a)
          ($f:unit -> RST a inner pre post)
        : RST a outer (frame_pre delta pre) 
                      (frame_post delta post) =
  reveal_view ();
  reveal_modifies ();
  f ()

(* Weaker form of framing, a bit similar to snapshot restoration in monotonic state, 
   in that the additional condition required of the inner postcondition (inner_post) 
   ensures that we can restore the outer invariant at the end, whilst it might have 
   been violated during the execution of the individual steps of the computation. *)

unfold
let weak_frame_pre (#outer:resource)
                   (#inner:resource)
                   (delta:r_weakly_includes outer inner)
                   (pre:r_pre inner)
                   (h:imem (inv outer)) =
  pre h

// The postcondition of the inner computation has to allow us to restore the outer invariant
let inner_post inner outer a = 
  post:r_post inner a{forall h0 x h1 . inv outer h0 /\ post h0 x h1 ==> inv outer h1}

unfold
let weak_frame_post (#outer:resource)
                    (#inner:resource)
                    (delta:r_weakly_includes outer inner)
                    (#a:Type)
                    (post:r_post inner a)
                    (h0:imem (inv outer))
                    (x:a)
                    (h1:imem (inv outer)) = 
  post h0 x h1 /\
  sel (view_of delta) h0 == sel (view_of delta) h1
  
let weak_frame (#a:Type)
               (#outer:resource)
               (#inner:resource)
               (delta:r_weakly_includes outer inner)  // eventually we will want to infer this argument through metaprogramming
               (#pre:r_pre inner)
               (#post:inner_post inner outer a)
               ($f:unit -> RST a inner pre post)
             : RST a outer (weak_frame_pre delta pre) 
                           (weak_frame_post delta post) =
  reveal_view ();
  reveal_modifies ();
  f ()
