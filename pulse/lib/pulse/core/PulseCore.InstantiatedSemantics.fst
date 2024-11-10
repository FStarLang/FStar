(*
   Copyright 2024 Microsoft Research

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
module PulseCore.InstantiatedSemantics

module Sem = PulseCore.Semantics
module Sep = PulseCore.IndirectionTheorySep
module ITA = PulseCore.IndirectionTheoryActions
module U = FStar.Universe
module F = FStar.FunctionalExtensionality

open PulseCore.IndirectionTheorySep

let laws ()
: squash (
    Sem.associative star /\
    Sem.commutative star /\
    Sem.is_unit emp star
  )
= Sep.sep_laws()

let state0 (e:inames) : Sem.state u#4 = {
    s = Sep.mem;
    is_full_mem = Sep.is_full;
    pred = slprop;
    emp = emp;
    star = star;
    interp = ITA.interpret;
    invariant = mem_invariant e;
    laws = laws ();
}

let state : Sem.state = state0 GhostSet.empty

let _eq : squash (slprop == state.pred) = ()
let timeless p = Sep.timeless p
let emp = emp

let pure p = pure p
let op_Star_Star = star
let op_exists_Star #a p = op_exists_Star #a p
let later_credit = later_credit
let later = later
let equiv = equiv
let later_credit_add n m = later_credit_add n m
let later_credit_zero () = later_credit_zero()
let iref = iref
let inv i p = inv i p

let prop_squash_idem (p:prop)
  : Tot (squash (p == squash p))
  = FStar.PropositionalExtensionality.apply p (squash p)

let slprop_equiv p q = p == q

let return_slprop_equiv (p q:slprop) (_:squash (p == q))
: slprop_equiv p q
= FStar.Squash.join_squash #(equals p p) ()

let unsquash (p:squash (slprop_equiv 'p 'q)) : slprop_equiv 'p 'q =
    prop_squash_idem (slprop_equiv 'p 'q);
    coerce_eq () p
    
let slprop_equiv_refl p = return_slprop_equiv p p ()
    
let slprop_equiv_elim p q = ()

let slprop_equiv_unit p = unsquash ()
let slprop_equiv_comm p1 p2 = unsquash ()
let slprop_equiv_assoc p1 p2 p3 = unsquash ()
module T = FStar.Tactics.V2
let slprop_equiv_exists 
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. slprop_equiv (p x) (q x)))
= assert (F.feq p q);
  assert (F.feq (F.on_dom a p) (F.on_dom a q));
  Sep.exists_ext p q;
  return_slprop_equiv (op_exists_Star p) (op_exists_Star q) ()

(* The type of general-purpose computations *)
let lower (t:Type u#a) : Type0 = unit -> Dv t
let stt (a:Type u#a) 
        (pre:slprop)
        (post:a -> slprop)
: Type0
= lower (Sem.m u#4 u#a u#100 #state a pre (F.on_dom a post))

let return (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x) p
= fun _ -> Sem.ret x (F.on_dom a p)

let bind
    (#a:Type u#a) (#b:Type u#b)
    (#pre1:slprop) (#post1:a -> slprop) (#post2:b -> slprop)
    (e1:stt a pre1 post1)
    (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2
= fun _ -> Sem.mbind (e1()) (fun x -> e2 x ())

let frame
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
: stt a (pre `star` frame) (fun x -> post x `star` frame)
= fun _ -> Sem.frame frame (e())

let conv (#a:Type u#a)
         (pre1:slprop)
         (pre2:slprop)
         (post1:a -> slprop)
         (post2:a -> slprop)
         (pf1:slprop_equiv pre1 pre2)
         (pf2:slprop_post_equiv post1 post2)
: Lemma (stt a pre1 post1 == stt a pre2 post2)
= slprop_equiv_elim pre1 pre2;
  introduce forall x. post1 x == post2 x
  with slprop_equiv_elim (post1 x) (post2 x);
  Sem.conv #state a #pre1 #(F.on_dom _ post1) (F.on_dom _ post2);
  ()

let sub (#a:Type u#a)
        (#pre1:slprop)
        (pre2:slprop)
        (#post1:a -> slprop)
        (post2:a -> slprop)
        (pf1:slprop_equiv pre1 pre2)
        (pf2:slprop_post_equiv post1 post2)
        (e:stt a pre1 post1)
: stt a pre2 post2
= coerce_eq (conv pre1 pre2 post1 post2 pf1 pf2) e

let par f0 f1 = fun _ -> Sem.par (f0 ()) (f1 ())

let hide_div #a #pre #post (f:unit -> Dv (stt a pre post))
: stt a pre post
= fun _ -> f () ()
