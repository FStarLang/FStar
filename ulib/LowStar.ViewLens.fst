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

unfold
let lens_disjoint #roots1 #view1 #roots2 #view2 
                  (l1:hs_view_lens roots1 view1)
                  (l2:hs_view_lens roots2 view2) =
  B.loc_disjoint (as_loc l1.fp) (as_loc l2.fp)

let ( <*> ) #roots1 #view1 #roots2 #view2 
            (l1:hs_view_lens roots1 view1)
            (l2:hs_view_lens roots2 view2{lens_disjoint l1 l2}) 
  : hs_view_lens (roots1 & roots2) (view1 * view2) = 
  // Footprint is the union of footprints
  let fp = Ghost.hide (B.loc_union (as_loc l1.fp) (as_loc l2.fp)) in
  // Invariant is the pointwise conjunction
  let inv (x,y) h = l1.inv x h /\ l2.inv y h in
  // Roots are a pair of roots
  let roots = (l1.roots,l2.roots) in
  // Views are pairs of views 
  let view h = (l1.view h,l2.view h) in
  {
    fp = fp;
    inv = inv;
    roots = roots;
    view = view
  }

noeq
type lens_includes_aux #roots1 #view1 #roots2 #view2
                       (l1:hs_view_lens roots1 view1)
                       (l2:hs_view_lens roots2 view2) =
  {
    inc_roots: roots1 -> roots2;    // Mapping of lens source elements
    inc_views: view1 -> view2;      // Mapping of lens target elements
    delta_fp: eloc                  // Explicit footprints difference
  }

let lens_includes #roots1 #view1 #roots2 #view2
                  (l1:hs_view_lens roots1 view1)
                  (l2:hs_view_lens roots2 view2) = 
  inc:lens_includes_aux l1 l2 {
    // Roots are mapped to roots
    (inc.inc_roots l1.roots == l2.roots) /\ 
    // Views are mapped to views
    (forall h .{:pattern (inc.inc_views (l1.view h))} 
               inc.inc_views (l1.view h) == l2.view h) /\
    // Difference in footprints is exactly inc.i_fp
    (B.loc_disjoint (as_loc inc.delta_fp) (as_loc l2.fp)) /\ 
    (as_loc l1.fp == B.loc_union (as_loc inc.delta_fp) (as_loc l2.fp)) /\ 
    // Larger lens's invariant implies the smaller lens's one (e.g., liveness)
    (forall h .{:pattern (inv l1 h); (inv l2 h)} inv l1 h ==> inv l2 h) /\ 
    // Larger lens's invariant can be framed across modifications by the smaller lens
    (forall h0 h1 .{:pattern (inv l1 h1); (B.modifies (as_loc l2.fp) h0 h1)} 
                   inv l1 h0 /\ B.modifies (as_loc l2.fp) h0 h1 /\ inv l2 h1 ==> inv l1 h1)
  }

let star_includes_left #roots1 #view1 #roots2 #view2
                       (l1:hs_view_lens roots1 view1)
                       (l2:hs_view_lens roots2 view2{lens_disjoint l1 l2})
                     : lens_includes (l1 <*> l2) l1 =
  {
    inc_roots = fst;
    inc_views = fst;
    delta_fp = l2.fp
  }

let star_includes_right #roots1 #view1 #roots2 #view2
                       (l1:hs_view_lens roots1 view1)
                       (l2:hs_view_lens roots2 view2{lens_disjoint l1 l2})
                     : lens_includes (l1 <*> l2) l2 =
  {
    inc_roots = snd;
    inc_views = snd;
    delta_fp = l1.fp
  }
