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

(* Views and resources *)

let imem inv = m:HS.mem{inv m}

let eloc = Ghost.erased B.loc
let as_loc (x:eloc) : GTot B.loc = Ghost.reveal x


let sel_reads_fp #b fp #inv (sel:(imem inv) -> GTot b) =
  forall (h0 h1:imem inv) loc. {:pattern  (B.modifies loc h0 h1); (sel h1)}
    B.loc_disjoint (as_loc fp) loc /\
    B.modifies loc h0 h1 ==>
    sel h0 == sel h1

let inv_reads_fp fp inv =
  forall h0 h1 loc.{:pattern (B.modifies loc h0 h1); (inv h1)}
    inv h0 /\
    B.loc_disjoint (as_loc fp) loc /\
    B.modifies loc h0 h1 ==>
    inv h1

unfold
let view_t a b = a -> GTot b

noeq 
type view_aux a = {
    fp: eloc;
    inv: HS.mem -> Type0;
    sel: view_t (imem inv) a
  }

let view a = 
  view:view_aux a{
    sel_reads_fp view.fp view.sel /\
    inv_reads_fp view.fp view.inv
  }

noeq 
type resource : Type u#1 = {
    t: Type u#0;
    view: view t
  }

let as_resource (#a:Type) (view:view a) : resource = {
    t = a;
    view = view
  }

let view_of (res:resource) = 
  res.view

abstract
let fp (res:resource) = 
  res.view.fp

abstract
let inv (res:resource) (h:HS.mem) =
  res.view.inv h

abstract
let sel (#a:Type) (view:view a) (h:imem (inv (as_resource view))) =
  view.sel h

abstract
let modifies (res:resource) (h0 h1:HS.mem) =
    B.modifies (as_loc (fp res)) h0 h1 /\
    HST.equal_domains h0 h1

let modifies_refl (res:resource) (h:HS.mem) 
  : Lemma (modifies res h h)
           [SMTPat (modifies res h h)]
  = ()

let modifies_trans (res:resource) (h0 h1 h2:HS.mem) 
  : Lemma (requires 
             modifies res h0 h1 /\
             modifies res h1 h2)
           (ensures
             modifies res h0 h2)
           [SMTPat (modifies res h0 h2);
            SMTPat (modifies res h0 h1)]
  = ()

let reveal ()
  : Lemma ((forall res.{:pattern view_of res} view_of res == res.view) /\
           (forall res h .{:pattern inv res h} inv res h <==> res.view.inv h) /\ 
           (forall res .{:pattern fp res} fp res == res.view.fp) /\ 
           (forall a (view:view a) h .{:pattern sel view h} sel view h == view.sel h) /\
           (forall res h0 h1.{:pattern modifies res h0 h1}
             modifies res h0 h1 <==>
             B.modifies (as_loc (fp res)) h0 h1 /\
             HST.equal_domains h0 h1)) =
  ()

(* Separating conjunction on views and resources *)

unfold
let r_disjoint (res1 res2:resource) = 
  B.loc_disjoint (as_loc (fp res1)) (as_loc (fp res2))

abstract
let ( <*> ) (res1 res2:resource) : res:resource = 
  let fp = Ghost.hide (B.loc_union (as_loc (fp res1)) (as_loc (fp res2))) in 
  let inv h = inv res1 h /\ inv res2 h /\ r_disjoint res1 res2 in
  let sel h = (sel res1.view h,sel res2.view h) in
  let t = res1.t & res2.t in 
  let view = {
      fp = fp;
      inv = inv;
      sel = sel
    } in 
  {
    t = t;
    view = view
  }

let reveal_star_inv (res1 res2:resource) (h:HS.mem)
  : Lemma ((inv (res1 <*> res2) h) 
           <==> 
           (inv res1 h /\ inv res2 h /\ r_disjoint res1 res2))
          [SMTPat (inv (res1 <*> res2) h)] =                    // [DA: we might consider removing this SMTPat 
                                                                //      at the cost of having to have expicitly 
                                                                //      call reveals in specs involving <*>]
  ()

let reveal_star () 
  : Lemma ((forall res1 res2 .{:pattern as_loc (fp (res1 <*> res2))} 
              as_loc (fp (res1 <*> res2)) == B.loc_union (as_loc (fp res1)) (as_loc (fp res2))) /\
           (forall res1 res2 .{:pattern (res1 <*> res2).t} 
              (res1 <*> res2).t == res1.t & res2.t) /\
           (forall res1 res2 h .{:pattern (res1 <*> res2).view.sel h} 
              (res1 <*> res2).view.sel h == (sel res1.view h,sel res2.view h))) = 
  ()

(* Constructive resource inclusion *)

noeq
type r_includes_t (res1 res2:resource) = {
    inc: view_t res1.t res2.t;   // viewing larger resource as a smaller one
    delta: resource              // delta separating the two resources
  }

let r_includes res1 res2 = 
  inc:r_includes_t res1 res2 {
    // Views are mapped to views
    (forall (h:imem (fun h -> inv res1 h /\ inv res2 h)) .{:pattern (inc.inc (sel (view_of res1) h))} 
               inc.inc (sel (view_of res1) h) == sel (view_of res2) h) /\
    // Delta is disjoint from the smaller resource
    r_disjoint inc.delta res2 /\
    // Footprint of the larger resource is union of delta and the smaller resource
    as_loc (fp res1) == B.loc_union (as_loc (fp inc.delta)) (as_loc (fp res2)) /\
    // Larger resource's invariant implies the smaller resource's invariant (e.g., liveness)
    (forall h .{:pattern (inv res1 h); (inv res2 h)} inv res1 h ==> inv res2 h) /\
    // Larger invariant is equivalent to delta and the smaller invariant
    (forall h . inv res1 h <==> inv res2 h /\ inv inc.delta h)
  }

(* Left and right inclusions for separating conjunction *)

let star_includes_left (#fp:resource) 
                       (frame:resource{r_disjoint fp frame})
                     : r_includes (fp <*> frame) fp = 
  let inc (xy:(fp <*> frame).t) = fst xy in 
  {
    inc = inc;
    delta = frame
  }

let star_includes_right (#fp:resource) 
                        (frame:resource{r_disjoint frame fp})
                      : r_includes (frame <*> fp) fp = 
  let inc (xy:(frame <*> fp).t) = snd xy in 
  {
    inc = inc;
    delta = frame
  }

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

let frame_left 
          (#frame:resource)
          (#a:Type)
          (#fp:resource)
          (#pre:r_pre fp)
          (#post:r_post fp a)
          ($f:unit -> RST a fp pre post)
        : RST a (fp <*> frame)
                (frame_left_pre pre) 
                (frame_left_post post) =
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

let frame_right 
           (#frame:resource)
           (#a:Type)           
           (#fp:resource)
           (#pre:r_pre fp)
           (#post:r_post fp a)
           ($f:unit -> RST a fp pre post)
         : RST a (frame <*> fp) 
                 (frame_right_pre pre) 
                 (frame_right_post post) =
  f ()

(* Generic frame operation for RST computations (through resource inclusion) *)

unfold
let frame_pre (#outer:resource)
                (#inner:resource)
                (inc:r_includes outer inner)
                (pre:r_pre inner)
                (h:imem (inv outer)) =
  pre h

unfold
let frame_post (#outer:resource)
                 (#inner:resource)
                 (inc:r_includes outer inner)
                 (#a:Type)
                 (post:r_post inner a)
                 (h0:imem (inv outer))
                 (x:a)
                 (h1:imem (inv outer)) = 
  post h0 x h1 /\
  sel (view_of inc.delta) h0 == sel (view_of inc.delta) h1
  
let frame (#a:Type)
              (#outer:resource)
              (#inner:resource)
              (inc:r_includes outer inner)  // eventually we will want to infer this argument through metaprogramming
              (#pre:r_pre inner)
              (#post:r_post inner a)
              ($f:unit -> RST a inner pre post)
            : RST a outer (frame_pre inc pre) (frame_post inc post) =
  f ()

(* Weaker form of resource inclusion (with invariant inclusion instead of equivalence) *)

noeq
type r_weakly_includes_t (res1 res2:resource) = {
    inc: view_t res1.t res2.t;   // viewing larger resource as a smaller one
    delta: resource              // delta separating the two resources
  }

let r_weakly_includes res1 res2 = 
  inc:r_weakly_includes_t res1 res2 {
    // Views are mapped to views
    (forall (h:imem (fun h -> inv res1 h /\ inv res2 h)) .
            {:pattern (inc.inc (sel (view_of res1) h))} 
              inc.inc (sel (view_of res1) h) == sel (view_of res2) h) /\
    // Delta is disjoint from the smaller resource
    r_disjoint inc.delta res2 /\
    // Footprint of the larger resource is union of delta and the smaller resource
    as_loc (fp res1) == B.loc_union (as_loc (fp inc.delta)) (as_loc (fp res2)) /\
    // Larger resource's invariant implies the smaller resource's invariant (e.g., liveness)
    (forall h .{:pattern (inv res1 h); (inv res2 h)} inv res1 h ==> inv res2 h) /\
    // Larger invariant is equivalent to delta and the smaller invariant
    (forall h . inv res1 h ==> inv res2 h /\ inv inc.delta h)
  }

(* Weaker form of framing, a bit similar to snapshot restoration in monotonic state *)

unfold
let weak_frame_pre (#outer:resource)
                   (#inner:resource)
                   (inc:r_weakly_includes outer inner)
                   (pre:r_pre inner)
                   (h:imem (inv outer)) =
  pre h

// The postcondition of the inner computation has to allow us to restore the outer invariant
let inner_post #outer #inner (inc:r_weakly_includes outer inner) a = 
  post:r_post inner a{forall h0 x h1 . inv outer h0 /\ post h0 x h1 ==> inv outer h1}

unfold
let weak_frame_post (#outer:resource)
                    (#inner:resource)
                    (inc:r_weakly_includes outer inner)
                    (#a:Type)
                    (post:r_post inner a)
                    (h0:imem (inv outer))
                    (x:a)
                    (h1:imem (inv outer)) = 
  post h0 x h1 /\
  sel (view_of inc.delta) h0 == sel (view_of inc.delta) h1
  
let weak_frame (#a:Type)
               (#outer:resource)
               (#inner:resource)
               (inc:r_weakly_includes outer inner)  // eventually we will want to infer this argument through metaprogramming
               (#pre:r_pre inner)
               (#post:inner_post inc a)
               ($f:unit -> RST a inner pre post)
             : RST a outer (weak_frame_pre inc pre) 
                           (weak_frame_post inc post) =
  f ()
