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
module Mem = PulseCore.MemoryAlt
module U = FStar.Universe
module F = FStar.FunctionalExtensionality

open PulseCore.MemoryAlt

let laws ()
: squash (
    Sem.associative star /\
    Sem.commutative star /\
    Sem.is_unit emp star
  )
= let equiv_eq (x y:slprop)
    : Lemma (x `equiv` y <==> x == y)
          [SMTPat (x `equiv` y)]
    = introduce x `equiv` y ==> x == y
      with _h . slprop_extensionality x y
  in
  let _ : squash (Sem.associative star) =
    introduce 
        forall x y z. 
            ((x `star` y) `star` z) ==
            (x `star` (y `star` z))
    with star_associative x y z
  in
  let _ : squash (Sem.commutative star) = 
    introduce 
        forall x y.
            x `star` y == y `star` x
        with star_commutative x y
  in
  let _ : squash (Sem.is_unit emp star) =
    introduce
        forall x.
            (x `star` emp) == x /\
            (emp `star` x) == x
        with emp_unit x
  in
  ()

let state0 (e:inames) : Sem.state u#4 = {
    // max_act = U.raise_t u#0 u#100 unit;
    s = mem u#1;
    is_full_mem = full_mem_pred;
    pred = slprop;
    emp = emp;
    star = star;
    interp = interp;
    // evolves = mem_evolves;
    invariant = mem_invariant e;
    laws = laws ()
}

let state : Sem.state = state0 Set.empty

let slprop = slprop
let _eq : squash (slprop == state.pred) = ()

let slprop2_base = slprop2_base
let cm_slprop2 = cm_slprop2
let down2 = down2
let up2 = up2
let up2_is_slprop2 = up2_is_slprop2

let slprop1_base = slprop1_base
let cm_slprop1 = cm_slprop1
let down1 = down1
let up1 = up1
let up1_is_slprop1 = up1_is_slprop1

let slprop_1_is_2 (s:slprop)
  : Lemma (is_slprop1 s ==> is_slprop2 s)
  = slprop_1_is_2 s

let emp = emp

let pure p = pure p
let ( ** ) p q = p `star` q
let ( exists* ) #a p = h_exists (F.on_dom a p)

let slprop2_star p q = slprop2_star_congruence p q
let slprop2_exists #a p = slprop2_exists_congruence #a (F.on_dom a p)
let slprop1_star p q = slprop1_star_congruence p q
let slprop1_exists #a p = slprop1_exists_congruence #a (F.on_dom a p)

let up2_emp    = up2_emp
let down2_emp  = down2_emp
let up2_star   = up2_star
let down2_star = down2_star

let up1_emp    = up1_emp
let down1_emp  = down1_emp
let up1_star   = up1_star
let down1_star = down1_star

let iref = iref
let inv i p = inv i p

let prop_squash_idem (p:prop)
  : Tot (squash (p == squash p))
  = FStar.PropositionalExtensionality.apply p (squash p)

let slprop_equiv p q = Mem.equiv p q

let unsquash (p:squash (slprop_equiv 'p 'q)) : slprop_equiv 'p 'q =
    prop_squash_idem (slprop_equiv 'p 'q);
    coerce_eq () p
    
let slprop_equiv_refl p = unsquash ()
    
let slprop_equiv_elim p q =
    introduce (p `slprop_equiv` q) ==> p==q
    with _ . Mem.slprop_extensionality p q

let slprop_equiv_unit p = unsquash ()
let slprop_equiv_comm p1 p2 = unsquash ()
let slprop_equiv_assoc p1 p2 p3 = unsquash ()
module T = FStar.Tactics.V2
let slprop_equiv_exists 
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. slprop_equiv (p x) (q x)))
= introduce forall x. p x == q x
  with slprop_equiv_elim (p x) (q x);
  F.extensionality _ _ p q;
  let pf : squash (eq2 #(F.arrow a (fun _ -> slprop))
                        (F.on_dom a p)
                        (F.on_dom a q)) = ()
  in
  let x : squash (op_exists_Star p == op_exists_Star q) = _ by (
      T.norm [delta_only [`%op_exists_Star; `%F.on_dom]; unascribe];
      let bindings = T.cur_vars() in
      let bindings = List.Tot.rev bindings in
      match bindings with
      | hd::_ -> (
        match T.term_as_formula hd.sort with
        | T.Comp (T.Eq _) lhs rhs ->
          T.grewrite lhs rhs;
          T.trefl();
          T.exact (T.binding_to_term hd)
        | _ -> T.fail "Unexpected type of hd"
      )
      | _ ->
        T.fail "empty bindings"
  ) in
  unsquash x

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
