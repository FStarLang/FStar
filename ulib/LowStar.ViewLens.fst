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
module LowStar.ViewLens

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let view_t a b = a -> GTot b

let imem inv = m:HS.mem{inv m}

let eloc = Ghost.erased B.loc

let as_loc (x:eloc) : GTot B.loc = Ghost.reveal x

let view_reads_loc #b #inv (el:eloc) (view:view_t (imem inv) b) =
  forall (h0 h1:imem inv) loc. {:pattern  (B.modifies loc h0 h1); (view h1)}
    B.loc_disjoint (as_loc el) loc /\
    B.modifies loc h0 h1 ==>
    view h0 == view h1

let invariant_reads_loc inv (el:eloc) =
  forall h0 h1 loc.{:pattern (B.modifies loc h0 h1); (inv h1)}
    inv h0 /\
    B.loc_disjoint (as_loc el) loc /\
    B.modifies loc h0 h1 ==>
    inv h1

let imem_view_lens inv b loc =
  l:view_t (imem inv) b {
    view_reads_loc loc l /\
    invariant_reads_loc inv loc
  }

noeq
type hs_view_lens a b = {
  fp: eloc;                             //footprint of get, put, inv
  inv: a -> HS.mem -> Type0;            //invariant, typically liveness
  roots:a;                              //root of the hyperstack fragment
  view:imem_view_lens (inv roots) b fp  //the imem_view_lens itself
}

let inv #roots #view (l:hs_view_lens roots view) (h:HS.mem) =
  l.inv l.roots h

let fp #roots #view (l:hs_view_lens roots view) = 
  l.fp

let view #roots #view (l:hs_view_lens roots view) (h:imem (inv l)) =
  l.view h

let ( <*> ) #roots1 #view1 #roots2 #view2 
            (l1:hs_view_lens roots1 view1)
            (l2:hs_view_lens roots2 view2{B.loc_disjoint (as_loc l1.fp) (as_loc l2.fp)}) 
  : GTot (hs_view_lens (roots1 & roots2) (view1 * view2)) = 
  let fp = Ghost.hide (B.loc_union (as_loc l1.fp) (as_loc l2.fp)) in
  let inv (x,y) h = l1.inv x h /\ l2.inv y h in
  let roots = (l1.roots,l2.roots) in
  let view h = (l1.view h,l2.view h) in
  {
    fp = fp;
    inv = inv;
    roots = roots;
    view = view
  }

noeq
type lens_includes_aux #roots1 #roots2 #view1 #view2
                       (l1:hs_view_lens roots1 view1)
                       (l2:hs_view_lens roots2 view2) =
  {
    i_roots: roots1 -> roots2;
    i_views: view1 -> view2
  }

let lens_includes #roots1 #roots2 #view1 #view2
                  (l1:hs_view_lens roots1 view1)
                  (l2:hs_view_lens roots2 view2) = 
  i:lens_includes_aux l1 l2 {
    (i.i_roots l1.roots == l2.roots) /\ 
    (forall h . i.i_views (l1.view h) == l2.view h) /\
    (B.loc_includes (as_loc l1.fp) (as_loc l2.fp)) /\ 
    (forall h . l1.inv l1.roots h ==> l2.inv l2.roots h)
  }
