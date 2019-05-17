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
module EqPoint.TwoIndex

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST.TwoIndex
open LowStar.RST.Pointer.TwoIndex

open LowStar.BufferOps

abstract
noeq
type eq_point = {
    x: B.pointer int;
    y: B.pointer int
  }

type eq_point_view_t = {
    x_view: int;
    y_view: y_view:int{x_view = y_view}
  }

abstract
let eq_point_view (p:eq_point) : view eq_point_view_t = 
  let fp = Ghost.hide (B.loc_union (B.loc_addr_of_buffer p.x) (B.loc_addr_of_buffer p.y)) in
  let inv h = 
    B.live h p.x /\ B.live h p.y /\ B.freeable p.x /\ B.freeable p.y /\ 
    B.loc_disjoint (B.loc_addr_of_buffer p.x) (B.loc_addr_of_buffer p.y) /\
    Seq.index (B.as_seq h p.x) 0 == Seq.index (B.as_seq h p.y) 0 
  in
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

let eq_point_resource (p:eq_point) = 
  as_resource (eq_point_view p)

let sel_x (p:eq_point) (h:imem (inv (eq_point_resource p))) : GTot int = 
  (sel (eq_point_view p) h).x_view
  
let sel_y (p:eq_point) (h:imem (inv (eq_point_resource p))) : GTot int = 
  (sel (eq_point_view p) h).y_view

let mk_eq_point (x y:B.pointer int) 
  : Pure eq_point (requires (B.loc_disjoint (B.loc_buffer x) (B.loc_buffer y)))
                  (ensures (fun _ -> True)) = 
  {
    x = x;
    y = y
  }

let unpack (p:eq_point)
  : RST (B.pointer int & B.pointer int) 
        (eq_point_resource p)
        (fun (x,y) -> ptr_resource x <*> ptr_resource y)
        (fun _ -> True)
        (fun h0 (x,y) h1 -> 
          sel_x p h0 = sel (ptr_view x) h1 /\ 
          sel_y p h0 = sel (ptr_view y) h1 /\
          sel (ptr_view x) h1 = sel (ptr_view y) h1) = 
  reveal_star ();
  reveal_ptr ();
  reveal_rst_inv ();
  reveal_modifies ();
  (p.x,p.y)

let pack (x y:B.pointer int)
  : RST eq_point
        (ptr_resource x <*> ptr_resource y)
        (fun p -> eq_point_resource p)
        (fun h -> sel (ptr_view x) h = sel (ptr_view y) h)
        (fun h0 p h1 -> 
          sel_x p h1 = sel (ptr_view x) h0 /\ 
          sel_y p h1 = sel (ptr_view y) h0) = 
  reveal_star ();
  reveal_ptr ();
  reveal_rst_inv ();
  reveal_modifies ();
  mk_eq_point x y

let get (p:eq_point)
  : RST int (eq_point_resource p)
            (fun _ -> eq_point_resource p)
            (fun _ -> True)
            (fun h0 xy h1 -> 
               sel_x p h1 = xy /\
               sel_y p h1 = xy /\
               sel_x p h1 = sel_x p h0 /\
               sel_y p h1 = sel_y p h0) = 
  reveal_star ();
  reveal_ptr ();
  reveal_rst_inv ();
  reveal_modifies ();
  rst_frame #(ptr_resource p.x <*> ptr_resource p.y) #_ #_
            #(fun _ -> ptr_resource p.x <*> ptr_resource p.y)
            (ptr_resource p.y) 
            (fun _ -> ptr_read p.x)

let move_up (p:eq_point)
  : RST unit (eq_point_resource p)
             (fun _ -> eq_point_resource p)
             (fun _ -> True)
             (fun h0 _ h1 ->
                sel_x p h1 = sel_x p h0 + 1 /\
                sel_y p h1 = sel_y p h0 + 1) =
  reveal_star ();
  reveal_ptr ();
  reveal_rst_inv ();
  reveal_modifies ();
  let xy = get p in 
  rst_frame #(ptr_resource p.x <*> ptr_resource p.y) #_ #_
            #(fun _ -> ptr_resource p.x <*> ptr_resource p.y)
            (ptr_resource p.y) 
            (fun _ -> ptr_write p.x (xy + 1));
  rst_frame #(ptr_resource p.x <*> ptr_resource p.y) #_ #_
            #(fun _ -> ptr_resource p.x <*> ptr_resource p.y)
            (ptr_resource p.x) 
            (fun _ -> ptr_write p.y (xy + 1))

let move_down (p:eq_point)
  : RST unit (eq_point_resource p)
             (fun _ -> eq_point_resource p)
             (fun _ -> True)
             (fun h0 _ h1 ->
                sel_x p h1 = sel_x p h0 - 1 /\
                sel_y p h1 = sel_y p h0 - 1) =
  reveal_star ();
  reveal_ptr ();
  reveal_rst_inv ();
  reveal_modifies ();
  let xy = get p in 
  rst_frame #(ptr_resource p.x <*> ptr_resource p.y) #_ #_
            #(fun _ -> ptr_resource p.x <*> ptr_resource p.y)
            (ptr_resource p.y) 
            (fun _ -> ptr_write p.x (xy - 1));
  rst_frame #(ptr_resource p.x <*> ptr_resource p.y) #_ #_
            #(fun _ -> ptr_resource p.x <*> ptr_resource p.y)
            (ptr_resource p.x) 
            (fun _ -> ptr_write p.y (xy - 1))
