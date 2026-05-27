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
module FStar.ReflexiveTransitiveClosure

open FStar.Tactics.V2
open FStar.Nonempty
#set-options "--max_ifuel 1 --fuel 0"

noeq
type _closure (#a:Type u#a) (r:binrel u#a a) : a -> a -> Type u#a =
| Refl: x:a -> _closure r x x
| Step: x:a -> y:a -> squash (r x y) ->_closure r x y
| Closure: x:a -> y:a -> z:a -> _closure r x y -> _closure r y z -> _closure r x z

let _closure0 (#a:Type) (r:binrel a) (x y: a) : prop =
  nonempty (_closure r x y)

let rec induct_ (#a:Type) (r:binrel a) (p: a -> a -> prop)
               (f_refl: (x:a -> squash (p x x)))
               (f_step: (x:a -> y:a { r x y } -> squash (p x y)))
               (f_closure: (x:a -> y:a -> z:a { p x y /\ p y z } -> squash (p x z)))
               (x:a) (y:a) (xy:_closure r x y)
: Tot (squash (p x y)) (decreases xy)
= match xy with
  | Refl x -> f_refl x
  | Step x y _ -> f_step x y
  | Closure x y z xy yz ->
    let p1 = induct_ r p f_refl f_step f_closure x y xy in
    let p2 = induct_ r p f_refl f_step f_closure y z yz in
    f_closure x y z

let get_squash (#a:Type) (r:binrel a) (x:a) (y:a{_closure0 r x y})
  : GTot (_closure r x y)
  = nonempty_elim (_closure r x y)

val closure_reflexive: #a:Type u#a -> r:binrel u#a a -> Lemma (reflexive (_closure0 r))
let closure_reflexive #a r =
  introduce forall x. _closure0 r x x with nonempty_intro (Refl x)

val closure_transitive: #a:Type u#a -> r:binrel u#a a -> Lemma (transitive (_closure0 r))
let closure_transitive #a r =
  introduce forall x y z. _closure0 r x y /\ _closure0 r y z ==> _closure0 r x z with
  introduce _ ==> _ with _.
  nonempty_intro (Closure x y z (nonempty_elim _) (nonempty_elim _))

let closure #a r =
  closure_reflexive r;
  closure_transitive r;
  _closure0 r

let closure_step #a r x y =
  introduce r x y ==> closure r x y with _.
  nonempty_intro (Step x y ())

val closure_one_aux: #a:Type u#a -> r:binrel u#a a -> x:a -> y:a
  -> xy:_closure r x y
  -> Tot (either (squash (x == y))
                (z:a & squash (r x z) & _closure r z y))
    (decreases xy)
let rec closure_one_aux #a r x y xy =
  match xy with
  | Refl _ -> Inl ()
  | Step _ _ pr -> Inr (| y, pr, Refl y |)
  | Closure x i y xi iy ->
    match closure_one_aux r i y iy with
    | Inl _ -> closure_one_aux r x y xi
    | Inr (| z, r_i_z, c_z_y |) ->
      let c_z_y : _closure r z y = c_z_y in
      match closure_one_aux r x i xi with
      | Inl _ -> Inr (| z, r_i_z, c_z_y |)
      | Inr (| w, r_x_w, c_w_i |) ->
        let step : _closure r i z = Step #a #r i z r_i_z in
        let c_i_y : _closure r i y = Closure i z y step c_z_y in
        let c_w_y : _closure r w y =  Closure w i y c_w_i c_i_y in
        Inr (| w, r_x_w, c_w_y |)

let closure_one_aux' (#a:Type u#a) (r:binrel u#a a) (x y:a)
                     (xy:_closure r x y)
  : GTot (squash (x == y \/ (exists z. r x z /\ closure r z y)))
  = let p = closure_one_aux r x y xy in
    match p with
    | Inl _ -> ()
    | Inr (| z, rxz, _c_zy |) ->
      assert r x z;
      nonempty_intro _c_zy;
      assert (closure r z y);
      ()

val closure_one: #a:Type u#a -> r:binrel u#a a -> x:a -> y:a
  -> xy:squash (closure r x y)
  -> GTot (squash (x == y \/ (exists z. r x z /\ closure r z y)))
let closure_one #a r x y xy =
  closure_one_aux' r x y (nonempty_elim _)

let closure_inversion #a r x y = closure_one r x y ()

val _stable_on_closure: #a:Type u#a -> r:binrel u#a a -> p:(a -> prop)
  -> p_stable_on_r: squash (forall x y. p x /\ r x y ==> p y)
  -> x: a
  -> y: a
  -> xy: _closure r x y
  -> px: squash (p x)
  -> GTot (squash (p y)) (decreases xy)
let rec _stable_on_closure #a r p p_stable_on_r x y xy px =
  match xy with
  | Refl _ -> ()
  | Step _ _ _ -> ()
  | Closure x a y xa ay ->
    let hi = _stable_on_closure r p p_stable_on_r in
    let pa = hi x a xa px in
    hi a y ay pa

let stable_on_closure #a r p hr =
  introduce forall x y. p x /\ closure r x y ==> p y with
  introduce p x /\ closure r x y ==> p y with _.
  nonempty_intro (_stable_on_closure r p () x y (nonempty_elim _) ())

let induct
      (#a:Type) (r:binrel a) (p: a -> a -> prop)
      (f_refl: (x:a -> squash (p x x)))
      (f_step: (x:a -> y:a { r x y } -> squash (p x y)))
      (f_closure: (x:a -> y:a -> z:a { p x y /\ p y z } -> squash (p x z)))
      (x:a) (y:a) (xy:squash (closure r x y))
: squash (p x y) =
  induct_ r p f_refl f_step f_closure x y (nonempty_elim _)