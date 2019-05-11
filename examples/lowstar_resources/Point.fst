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

open LowStar.Resource
open LowStar.RST
open LowStar.RST.Pointer

open LowStar.BufferOps

abstract
noeq
type point = {
    x: B.pointer int;
    y: B.pointer int
  }

type point_view_t = {
    x_view: int;
    y_view: y_view:int
  }

abstract
let point_view (p:point) : view point_view_t = 
  let fp = Ghost.hide (B.loc_union (B.loc_buffer p.x) (B.loc_buffer p.y)) in
  let inv h = 
    B.live h p.x /\ B.live h p.y /\ B.loc_disjoint (B.loc_buffer p.x) (B.loc_buffer p.y) in
  let sel (h:imem inv) = 
    { 
      x_view = Seq.index (B.as_seq h p.x) 0; 
      y_view = Seq.index (B.as_seq h p.y) 0
    } 
  in
  reveal_view ();
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let sel_x (p:point) (h:imem (inv (as_resource (point_view p)))) : GTot int = 
  (sel (point_view p) h).x_view
  
let sel_y (p:point) (h:imem (inv (as_resource (point_view p)))) : GTot int = 
  (sel (point_view p) h).y_view

let mk_point (x:B.pointer int) (y:B.pointer int) : point = 
  {
    x = x;
    y = y
  }

private
let unpack_point (p:point) 
  : r_includes (as_resource (point_view p)) 
               (ptr_resource p.x <*> ptr_resource p.y) = 
  reveal_view ();
  reveal_ptr ();
  reveal_star ();
  empty_resource
  
private
let move_up_aux (x:B.pointer int) (y:B.pointer int)
  : RST unit (ptr_resource x <*> ptr_resource y)
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel (ptr_view x) h1 = sel (ptr_view x) h0 /\
                sel (ptr_view y) h1 = sel (ptr_view y) h0 + 1) = 
  let y' = frame (star_includes_right (ptr_resource x)) (ptr_read y) in
  frame (star_includes_right (ptr_resource x)) (ptr_write y (y' + 1))

let move_up (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> sel_x p h1 = sel_x p h0 /\
                             sel_y p h1 = sel_y p h0 + 1) = 
  reveal_ptr ();
  frame (unpack_point p) (fun _ -> move_up_aux p.x p.y)

private
let move_down_aux (x:B.pointer int) (y:B.pointer int)
  : RST unit (ptr_resource x <*> ptr_resource y)
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel (ptr_view x) h1 = sel (ptr_view x) h0 /\
                sel (ptr_view y) h1 = sel (ptr_view y) h0 - 1) = 
  let y' = frame (star_includes_right (ptr_resource x)) (ptr_read y) in
  frame (star_includes_right (ptr_resource x)) (ptr_write y (y' - 1))

let move_down (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> sel_x p h1 = sel_x p h0 /\
                             sel_y p h1 = sel_y p h0 - 1) = 
  reveal_ptr ();
  frame (unpack_point p) (fun _ -> move_down_aux p.x p.y)

private
let move_right_aux (x:B.pointer int) (y:B.pointer int)
  : RST unit (ptr_resource x <*> ptr_resource y)
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel (ptr_view x) h1 = sel (ptr_view x) h0 + 1 /\
                sel (ptr_view y) h1 = sel (ptr_view y) h0) = 
  let x' = frame (star_includes_left (ptr_resource y)) (ptr_read x) in
  frame (star_includes_left (ptr_resource y)) (ptr_write x (x' + 1))

let move_right (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> sel_x p h1 = sel_x p h0 + 1 /\
                             sel_y p h1 = sel_y p h0) = 
  reveal_ptr ();
  frame (unpack_point p) (fun _ -> move_right_aux p.x p.y)

private
let move_left_aux (x:B.pointer int) (y:B.pointer int)
  : RST unit (ptr_resource x <*> ptr_resource y)
             (fun _ -> True)
             (fun h0 _ h1 -> 
                sel (ptr_view x) h1 = sel (ptr_view x) h0 - 1 /\
                sel (ptr_view y) h1 = sel (ptr_view y) h0) = 
  let x' = frame (star_includes_left (ptr_resource y)) (ptr_read x) in
  frame (star_includes_left (ptr_resource y)) (ptr_write x (x' - 1))

let move_left (p:point)
  : RST unit (as_resource (point_view p))
             (fun _ -> True)
             (fun h0 _ h1 -> sel_x p h1 = sel_x p h0 - 1 /\
                             sel_y p h1 = sel_y p h0) = 
  reveal_ptr ();
  frame (unpack_point p) (fun _ -> move_left_aux p.x p.y)
