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

[@@erasable]
val big_slprop : Type u#3
val down (s:slprop) : big_slprop
val up (s:big_slprop) : slprop
let is_big (s:slprop) = s == up (down s)
let big_vprop = s:slprop { is_big s }

[@@erasable]
val small_slprop : Type u#2
val down2 (s:slprop) : small_slprop
val up2 (s:small_slprop) : slprop
let is_small (s:slprop) : prop = up2 (down2 s) == s
let vprop = s:slprop { is_small s }

val small_is_also_big (s:slprop)
  : Lemma (is_small s ==> is_big s)

val emp : vprop
val pure (p:prop) : vprop
val ( ** ) (p q : slprop) : slprop
val ( exists* ) (#a:Type u#a) (p: a -> slprop) : slprop

val big_star (p q:big_vprop) : squash (is_big (p ** q))
val big_exists (#a:Type u#a) (p: a -> slprop)
: Lemma (requires forall x. is_big (p x))
        (ensures is_big (op_exists_Star p))

val small_star (p q:vprop) : squash (is_small (p ** q))
val small_exists (#a:Type u#a) (p: a -> slprop)
: Lemma (requires forall x. is_small (p x))
        (ensures is_small (op_exists_Star p))

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
