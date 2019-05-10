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
module Point

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.RST
open LowStar.RST.Pointer
open LowStar.BufferOps

abstract
noeq
type point_t = {
    x: B.pointer int;
    y: B.pointer int
  }

let point =
  p:point_t

type point_view_t = {
    x_view: int;
    y_view: y_view:int{x_view = y_view}
  }

abstract
let point_view (p:point) : view point_view_t = 
  let fp = Ghost.hide (B.loc_union (B.loc_buffer p.x) (B.loc_buffer p.y)) in
  let inv h = B.live h p.x /\ B.live h p.y /\ 
              Seq.index (B.as_seq h p.x) 0 == Seq.index (B.as_seq h p.y) 0 in
  let sel (h:imem inv) = 
    { 
      x_view = Seq.index (B.as_seq h p.x) 0; 
      y_view = Seq.index (B.as_seq h p.y) 0
    } in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let mk_point (x:B.pointer int) (y:B.pointer int) 
  : point = 
  {
    x = x;
    y = y
  }

// [DA: TODO: this definition cannot be completed in its current form 
//      as (inv res1 h <==> inv res2 h /\ inv delta h) doesn't hold]
private
let point_inclusion (p:point) 
  : r_includes (as_resource (point_view p)) 
               (ptr_resource p.x <*> ptr_resource p.y) = 
  reveal_star ();
  let inc (xy:(as_resource (point_view p)).t) 
    : GTot ((ptr_resource p.x).t & (ptr_resource p.y).t) = 
    (xy.x_view,xy.y_view) in 
  let delta = {
      t = unit;
      view = {
        fp = Ghost.hide B.loc_none;
        inv = (fun h -> True);
        sel = (fun _ -> ())
      }
    } in 
  reveal ();
  reveal_ptr ();
  // assume (forall (h:imem (fun h -> inv (as_resource (point_view p)) h /\ inv (ptr_resource p.x <*> ptr_resource p.y) h)) . 
  //           inc (sel (view_of (as_resource (point_view p))) h) == sel (view_of (ptr_resource p.x <*> ptr_resource p.y)) h);
  // assert (r_disjoint delta (ptr_resource p.x <*> ptr_resource p.y));
  // assert (as_loc (fp (as_resource (point_view p))) == B.loc_union (as_loc (fp delta)) (as_loc (fp (ptr_resource p.x <*> ptr_resource p.y))));
  // assume (forall h . inv (as_resource (point_view p)) h <==> inv (ptr_resource p.x <*> ptr_resource p.y) h /\ inv delta h);
  admit ();
  {
    inc = inc;
    delta = delta
  }

private
let move_up_aux (x:B.pointer int) (y:B.pointer int)
  : RST unit (ptr_resource x <*> ptr_resource y)
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel (ptr_view x) h1 = sel (ptr_view x) h0 + 1 /\
                sel (ptr_view y) h1 = sel (ptr_view y) h0 + 1) = 
  let x' = frame (star_includes_left (ptr_resource y)) (ptr_read x) in 
  let y' = frame (star_includes_right (ptr_resource x)) (ptr_read y) in
  frame (star_includes_left (ptr_resource y)) (ptr_write x (x'+1));
  frame (star_includes_right (ptr_resource x)) (ptr_write y (y'+1))

let move_up (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> (sel (point_view p) h1).x_view = (sel (point_view p) h0).x_view+1 /\
                             (sel (point_view p) h1).y_view = (sel (point_view p) h0).y_view+1) = 
  reveal ();
  frame (point_inclusion p) (fun _ -> move_up_aux p.x p.y)
