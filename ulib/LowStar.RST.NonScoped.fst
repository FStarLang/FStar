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
module LowStar.RST.NonScoped

open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open LowStar.Resource

(* Additional (currently assumed) lemma: 
     Reasonable when addresses are not reused after deallocation, 
     but currently not provided by the LowStar.Buffer library
     (Nik and/or Tahina will look into adding it to ulib) *)
(*assume val lemma_loc_not_unused_in_modifies (l:B.loc) (h0 h1:HS.mem)
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l /\ B.modifies l h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l))*)

assume val lemma_loc_not_unused_in_modifies_includes (l0 l1:B.loc) (h0 h1:HS.mem)
  : Lemma (requires (B.loc_includes (B.loc_not_unused_in h0) l0 /\ 
                     B.loc_includes l1 l0 /\
                     B.modifies l1 h0 h1))
          (ensures  (B.loc_includes (B.loc_not_unused_in h1) l1))

(* Abstract modifies clause for the resource-indexed state effect *)

abstract
let modifies (res:resource) (h0 h1:HS.mem) =
    B.modifies (as_loc (fp res)) h0 h1 // /\
    //HST.equal_domains h0 h1

let modifies_refl (res:resource) (h:HS.mem) 
  : Lemma (modifies res h h)
           [SMTPat (modifies res h h)]
  = ()

let modifies_trans (res0 res1:resource) (h0 h1 h2:HS.mem) 
  : Lemma (requires 
             modifies res0 h0 h1 /\
             modifies res1 h1 h2)
           (ensures
             modifies (r_union res0 res1) h0 h2)
           [SMTPat (modifies (r_union res0 res1) h0 h2);
            SMTPat (modifies res0 h0 h1)]
  = ()

let reveal_modifies ()
  : Lemma (forall res h0 h1.{:pattern modifies res h0 h1}
             modifies res h0 h1 <==>
             B.modifies (as_loc (fp res)) h0 h1) // /\
             //HST.equal_domains h0 h1)
  = ()

(* State effect indexed by resources *)

let r_pre (res:resource) = imem (inv res) -> Type0
let r_post res0 a res1 = imem (inv res0) -> x:a -> imem (inv (res1 x)) -> Type0

abstract
let rst_inv (res:resource) (h:HS.mem) =
  B.loc_includes (B.loc_not_unused_in h) (as_loc (fp res))

let reveal_rst_inv ()
  : Lemma (forall res h . 
             rst_inv res h 
             <==>
             B.loc_includes (B.loc_not_unused_in h) (as_loc (fp res)))
  = ()

let prov_resource res0 =
  res1:resource{(forall frame . r_disjoint frame res0 ==> r_disjoint frame res1)}

effect RST (a:Type)
           (res0:resource)                                      //Resources expected
           (res1:a -> prov_resource res0)                       //Resources provided
           (pre:r_pre res0)
           (post:r_post res0 a res1) = 
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               inv res0 h0 /\                                    //Require the resource invariant
               rst_inv res0 h0 /\                                //Require the additional footprints invariant
               pre h0 /\                                         //Require the pre-condition
               (forall (x:a) (h1:HS.mem).
                 inv (res1 x) h1 /\                              //Ensure the resource invariant
                 rst_inv (res1 x) h1 /\                          //Ensure the additional footprints invariant
                 modifies (r_union res0 (res1 x)) h0 h1 /\       //Ensure that only resource's footprint is modified
                 post h0 x h1 ==>                                //Ensure the post-condition
                 k x h1))                                         //Prove the continuation under this hypothesis

(* Generic frame operation for RST computations (through resource inclusion) *)

unfold
let frame_pre (frame:resource)
              (#fp:resource)
              (pre:r_pre fp)
              (h:imem (inv (frame <*> fp))) =
  pre h

unfold
let frame_post (frame:resource)
               (#fp0:resource)
               (#a:Type)
               (#fp1:a -> prov_resource fp0)
               (post:r_post fp0 a fp1)
               (h0:imem (inv (frame <*> fp0)))
               (x:a)
               (h1:imem (inv (frame <*> fp1 x))) = 
  post h0 x h1 /\
  sel (view_of frame) h0 == sel (view_of frame) h1

let frame (#frame:resource)
          (#fp0:resource)
          (#a:Type)
          (#fp1:a -> prov_resource fp0)
          (#pre:r_pre fp0)
          (#post:r_post fp0 a fp1)
          ($f:unit -> RST a fp0 fp1 pre post)
        : RST a (frame <*> fp0) 
                (fun x -> reveal_star (); frame <*> fp1 x) 
                (frame_pre frame pre) 
                (frame_post frame post) =
  reveal_view ();
  reveal_star ();
  let h0 = get () in 
  let x = f () in 
  let h1 = get () in 
  lemma_loc_not_unused_in_modifies_includes 
    (as_loc (fp (frame <*> fp0))) 
    (as_loc (fp (r_union (frame <*> fp0) (frame <*> fp1 x)))) 
    h0 h1;
  x


unfold
let weaken_pre (#outer0:resource)
               (#inner0:resource)
               (delta0:r_includes outer0 inner0)
               (pre:r_pre inner0)
               (h:imem (inv outer0)) =
  pre h

unfold
let weaken_post (#outer0:resource)
                (#inner0:resource)
                (#a:Type)
                (#outer1:a -> prov_resource outer0)
                (#inner1:a -> prov_resource inner0)
                (delta0:r_includes outer0 inner0)
                (delta1:(x:a -> r_includes (outer1 x) (inner1 x)))
                (post:r_post inner0 a inner1)
                (h0:imem (inv outer0))
                (x:a)
                (h1:imem (inv (outer1 x))) = 
  assert (inv (outer1 x) h1 ==> inv (delta1 x) h1); // needed to trigger (inv (outer1 x) h1 ==> inv (inner1 x) h1) from (delta1 x)
  post h0 x h1 /\
  sel (view_of delta0) h0 === sel (view_of (delta1 x)) h1 // only makes sense if the deltas have the views with same types

let weaken (#outer0:resource)
           (#inner0:resource)
           (#a:Type)
           (#outer1:a -> prov_resource outer0)
           (#inner1:a -> prov_resource inner0)
           (delta0:r_includes outer0 inner0)
           (delta1:(x:a -> r_includes (outer1 x) (inner1 x)))
           (#pre:r_pre inner0)
           (#post:r_post inner0 a inner1)
           ($f:unit -> RST a inner0 inner1 pre post)
         : RST a outer0 outer1 (weaken_pre delta0 pre) 
                               (weaken_post delta0 delta1 post) =
  reveal_view ();
  let h0 = get () in 
  let x = f () in 
  let h1 = get () in 
  assert (inv (inner1 x) h1);
  admit ()
