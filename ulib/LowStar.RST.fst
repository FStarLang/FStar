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

let view_t a b = a -> GTot b

let view_reads_fp #b fp #inv (view:view_t (imem inv) b) =
  forall (h0 h1:imem inv) loc. {:pattern  (B.modifies loc h0 h1); (view h1)}
    B.loc_disjoint (as_loc fp) loc /\
    B.modifies loc h0 h1 ==>
    view h0 == view h1

let r_view_t fp inv a =
  sel:view_t (imem inv) a {
    view_reads_fp fp sel
  }

noeq
type r_view fp inv : Type u#1 = {
    t: Type0;
    sel: r_view_t fp inv t
  }

noeq
type resource_t : Type u#1 = {
    fp: eloc;
    inv: HS.mem -> Type0;
    view: r_view fp inv         // might become a list of (r_view inv fp)'s one day
  }

let invariant_reads_fp fp inv =
  forall h0 h1 loc.{:pattern (B.modifies loc h0 h1); (inv h1)}
    inv h0 /\
    B.loc_disjoint (as_loc fp) loc /\
    B.modifies loc h0 h1 ==>
    inv h1

let resource =
  res:resource_t {
    invariant_reads_fp res.fp res.inv
  }

abstract
let inv (res:resource) (h:HS.mem) =
  res.inv h

abstract
let fp (res:resource) = 
  res.fp
  
abstract
let sel (res:resource) (h:imem (inv res)) =
  res.view.sel h

let reveal ()
  : Lemma ((forall res h .{:pattern inv res h} inv res h <==> res.inv h) /\ 
           (forall res .{:pattern fp res} fp res == res.fp) /\ 
           (forall res h .{:pattern sel res h} sel res h == res.view.sel h)) =
  ()

(* Separating conjunction on views and resources *)

unfold
let r_disjoint (res1 res2:resource) = 
  B.loc_disjoint (as_loc (fp res1)) (as_loc (fp res2))

abstract
let ( <*> ) (res1 res2:resource) : res:resource{res.view.t == res1.view.t & res2.view.t} = 
  let fp = Ghost.hide (B.loc_union (as_loc (fp res1)) (as_loc (fp res2))) in 
  let inv h = inv res1 h /\ inv res2 h /\ r_disjoint res1 res2 in
  let view = (
    let t = res1.view.t & res2.view.t in 
    let sel h = (sel res1 h,sel res2 h) in 
    {
      t = t;
      sel = sel
    }) in
  {
    fp = fp;
    inv = inv;
    view = view
  }

let reveal_star_inv (res1 res2:resource) (h:HS.mem)
  : Lemma ((inv (res1 <*> res2) h) <==> (inv res1 h /\ inv res2 h /\ r_disjoint res1 res2))
          [SMTPat (inv (res1 <*> res2) h)] = 
  ()

let reveal_star_fp (res1 res2:resource) 
  : Lemma (as_loc (fp (res1 <*> res2)) == B.loc_union (as_loc (fp res1)) (as_loc (fp res2))) = 
  ()

let reveal_star_view_t (res1 res2:resource)
  : Lemma ((res1 <*> res2).view.t == res1.view.t & res2.view.t) = 
  ()

(* (Constructive) view and resource inclusion *)

noeq
type r_includes_t (res1 res2:resource) = {
    view_inc: res1.view.t -> res2.view.t;
    fp_delta: eloc
  }

let r_includes res1 res2 =
  inc:r_includes_t res1 res2 {
    // Difference in resource footprints is exactly inc.fp_delta
    (B.loc_disjoint (as_loc inc.fp_delta) (as_loc (fp res2))) /\ 
    (as_loc (fp res1) == B.loc_union (as_loc inc.fp_delta) (as_loc (fp res2))) /\
    // Larger resource's invariant implies the smaller resource's one (e.g., liveness)
    (forall h .{:pattern (inv res1 h); (inv res2 h)} inv res1 h ==> inv res2 h) /\
    // Views are mapped to views
    (forall h .{:pattern (inc.view_inc (sel res1 h))} 
               inc.view_inc (sel res1 h) == sel res2 h) /\
    // Larger resource's invariant can be framed across modifications by the smaller resource
    (forall h0 h1 .{:pattern (inv res1 h1); (B.modifies (as_loc (fp res2)) h0 h1)} 
                   inv res1 h0 /\ B.modifies (as_loc (fp res2)) h0 h1 /\ inv res2 h1 ==> inv res1 h1)
                   // [DA: can we get rid of this modifies somehow?]
  }

(* Left and right inclusions for separating conjunction *)

let star_includes_left (res1:resource) 
                       (res2:resource{B.loc_disjoint (as_loc (fp res1)) (as_loc (fp res2))})
                     : r_includes (res1 <*> res2) res1 = 
  let view_inc (xy:(res1 <*> res2).view.t) = fst xy in 
  let fp_delta = fp res2 in
  {
    view_inc = view_inc;
    fp_delta = fp_delta
  }

let star_includes_right (res1:resource) 
                        (res2:resource{B.loc_disjoint (as_loc (fp res1)) (as_loc (fp res2))})
                      : r_includes (res1 <*> res2) res2 = 
  let view_inc (xy:(res1 <*> res2).view.t) = snd xy in 
  let fp_delta = fp res1 in
  {
    view_inc = view_inc;
    fp_delta = fp_delta
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
                 B.modifies (as_loc (fp res)) h0 h1 /\  //Ensure that only resource's footprint is modified
                 HST.equal_domains h0 h1 /\
                 post h0 x h1 ==>                       //Ensure the post-condition
                 k x h1))                               //prove the continuation under this hypothesis

(* Simple packaging of resources with readers-writers for them *)
noeq
type resource_w_rw = {
    res: resource;
    reader: unit -> RST (res.view.t) res (fun _ -> True) (fun h0 x h1 -> sel res h0 == x /\ x == sel res h1);
    writer: x:res.view.t -> RST unit res (fun _ -> True) (fun _ _ h1 -> sel res h1 == x)
  }

(* Framing for RST computations *)

let frame_left_pre (#res1:resource)
              (#res2:resource)
              (pre:r_pre res1)
              (h:imem (inv (res1 <*> res2))) = 
  pre h

let frame_left_post (#res1:resource)
               (#res2:resource)
               (#a:Type)
               (post:r_post res1 a)
               (h0:imem (inv (res1 <*> res2)))
               (x:a)
               (h1:imem (inv (res1 <*> res2))) =
  post h0 x h1 /\
  sel res2 h0 == sel res2 h1

let frame_left (#a:Type)
          (#res1:resource)
          (#res2:resource)
          (#pre:r_pre res1)
          (#post:r_post res1 a)
          ($f:unit -> RST a res1 pre post)
        : RST a (res1 <*> res2) 
                (frame_left_pre pre) 
                (frame_left_post post) =
  f ()

let frame_right_pre (#res1:resource)
               (#res2:resource)
               (pre:r_pre res2)
               (h:imem (inv (res1 <*> res2))) = 
  pre h

let frame_right_post (#res1:resource)
                (#res2:resource)
                (#a:Type)
                (post:r_post res2 a)
                (h0:imem (inv (res1 <*> res2)))
                (x:a)
                (h1:imem (inv (res1 <*> res2))) =
  post h0 x h1 /\
  sel res1 h0 == sel res1 h1

let frame_right (#a:Type)
           (#res1:resource)
           (#res2:resource)
           (#pre:r_pre res2)
           (#post:r_post res2 a)
           ($f:unit -> RST a res2 pre post)
         : RST a (res1 <*> res2) 
                 (frame_right_pre pre) 
                 (frame_right_post post) =
  f ()

(* Resource inclusion for RST computations *)

let include_pre (#res1:resource)
                (#res2:resource)
                (inc:r_includes res1 res2)
                (pre:r_pre res2)
                (h:imem (inv res1)) =
  pre h

let include_post (#res1:resource)
                 (#res2:resource)
                 (inc:r_includes res1 res2)
                 (#a:Type)
                 (post:r_post res2 a)
                 (h0:imem (inv res1))
                 (x:a)
                 (h1:imem (inv res1)) = 
  (post h0 x h1) /\
  (B.modifies (as_loc (fp res2)) h0 h1) // [DA: can we get rid of this modifies somehow?]

let r_include (#a:Type)
              (#res1:resource)
              (#res2:resource)
              (inc:r_includes res1 res2)
              (#pre:r_pre res2)
              (#post:r_post res2 a)
              ($f:unit -> RST a res2 pre post)
            : RST a res1 (include_pre inc pre) (include_post inc post) =
  f ()
