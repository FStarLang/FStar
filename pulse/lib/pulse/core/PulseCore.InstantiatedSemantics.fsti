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

[@@erasable]
val slprop : Type u#4

(* Previously "big" *)
[@@erasable]
val slprop2_repr : Type u#3
val cm_slprop2 : FStar.Algebra.CommMonoid.cm slprop2_repr
val down2 (s:slprop) : slprop2_repr
val up2 (s:slprop2_repr) : slprop
let is_slprop2 (s:slprop) = s == up2 (down2 s)
let slprop2 = s:slprop { is_slprop2 s }
val up2_is_slprop2 (b:slprop2_repr) : Lemma (is_slprop2 (up2 b))

(* Previously "small" *)
[@@erasable]
val slprop1_repr : Type u#2
val cm_slprop1 : FStar.Algebra.CommMonoid.cm slprop1_repr
val down1 (s:slprop) : slprop1_repr
val up1 (s:slprop1_repr) : slprop
let is_slprop1 (s:slprop) = s == up1 (down1 s)
let slprop1 = s:slprop { is_slprop1 s }
val up1_is_slprop1 (b:slprop1_repr) : Lemma (is_slprop1 (up1 b))

val slprop_1_is_2 (s:slprop)
  : Lemma (is_slprop1 s ==> is_slprop2 s)

val emp : slprop1
val pure (p:prop) : slprop1
val ( ** ) (p q : slprop) : slprop
val ( exists* ) (#a:Type u#a) (p: a -> slprop) : slprop

val big_star (p q:slprop2) : squash (is_slprop2 (p ** q))
val big_exists (#a:Type u#a) (p: a -> slprop)
: Lemma (requires forall x. is_slprop2 (p x))
        (ensures is_slprop2 (op_exists_Star p))

val small_star (p q:slprop1) : squash (is_slprop1 (p ** q))
val small_exists (#a:Type u#a) (p: a -> slprop)
: Lemma (requires forall x. is_slprop1 (p x))
        (ensures is_slprop1 (op_exists_Star p))

(* Q: Can the star lemmas be provided pointfree? Is that useful? *)
val up2_emp    ()      : Lemma (up2 cm_slprop2.unit == emp)
val down2_emp  ()      : Lemma (down2 emp == cm_slprop2.unit)
val up2_star   (p q:_) : Lemma (up2 (p `cm_slprop2.mult` q) == up2 p ** up2 q)
val down2_star (p q:_) : Lemma (down2 (p ** q) == down2 p `cm_slprop2.mult` down2 q)

val up1_emp    ()      : Lemma (up1 cm_slprop1.unit == emp)
val down1_emp  ()      : Lemma (down1 emp == cm_slprop1.unit)
val up1_star   (p q:_) : Lemma (up1 (p `cm_slprop1.mult` q) == up1 p ** up1 q)
val down1_star (p q:_) : Lemma (down1 (p ** q) == down1 p `cm_slprop1.mult` down1 q)

[@@ erasable]
val iref : Type0
val inv (i:iref) (p:slprop) : slprop

val slprop_equiv (p q:slprop) : prop

val slprop_equiv_refl (p:slprop)
: slprop_equiv p p

val slprop_equiv_elim (p q:slprop)
: Lemma (p `slprop_equiv` q <==> p==q)

val slprop_equiv_unit (x:slprop)
: slprop_equiv (emp ** x) x

val slprop_equiv_comm (p1 p2:slprop)
: slprop_equiv (p1 ** p2) (p2 ** p1)

val slprop_equiv_assoc (p1 p2 p3:slprop)
: slprop_equiv (p1 ** p2 ** p3) (p1 ** (p2 ** p3))

val slprop_equiv_exists 
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. slprop_equiv (p x) (q x)))
: slprop_equiv (op_exists_Star p) (op_exists_Star q)

val stt (a:Type u#a) 
        (pre:slprop)
        (post:a -> slprop)
: Type0

val return (#a:Type u#a) (x:a) (p:a -> slprop)
: stt a (p x) p

val bind
    (#a:Type u#a) (#b:Type u#b)
    (#pre1:slprop) (#post1:a -> slprop) (#post2:b -> slprop)
    (e1:stt a pre1 post1)
    (e2:(x:a -> stt b (post1 x) post2))
: stt b pre1 post2

val frame
  (#a:Type u#a)
  (#pre:slprop) (#post:a -> slprop)
  (frame:slprop)
  (e:stt a pre post)
: stt a (pre ** frame) (fun x -> post x ** frame)

let slprop_post_equiv #a (p q:a -> slprop)
: prop
= forall x. slprop_equiv (p x) (q x)

val conv (#a:Type u#a)
         (pre1:slprop)
         (pre2:slprop)
         (post1:a -> slprop)
         (post2:a -> slprop)
         (pf1:slprop_equiv pre1 pre2)
         (pf2:slprop_post_equiv post1 post2)
: Lemma (stt a pre1 post1 == stt a pre2 post2)

val sub (#a:Type u#a)
        (#pre1:slprop)
        (pre2:slprop)
        (#post1:a -> slprop)
        (post2:a -> slprop)
        (pf1:slprop_equiv pre1 pre2)
        (pf2:slprop_post_equiv post1 post2)
        (e:stt a pre1 post1)
: stt a pre2 post2

val par (#p0 #q0 #p1 #q1:_)
        (f0:stt unit p0 (fun _ -> q0))
        (f1:stt unit p1 (fun _ -> q1))
: stt unit (p0 ** p1) (fun _ -> q0 ** q1)

val hide_div #a #pre #post (f:unit -> Dv (stt a pre post))
: stt a pre post

