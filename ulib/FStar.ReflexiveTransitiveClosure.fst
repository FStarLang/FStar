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
#set-options "--max_ifuel 1 --max_fuel 0"

noeq
type _closure (#a:Type u#a) (r:binrel u#a u#r a) : a -> a -> Type u#(max a r) =
| Refl: x:a -> _closure r x x
| Step: x:a -> y:a -> squash (r x y) ->_closure r x y
| Closure: x:a -> y:a -> z:a -> _closure r x y -> _closure r y z -> _closure r x z

let _closure0 (#a:Type) (r:binrel a) (x y: a) : prop =
  squash (_closure r x y)

let get_squash (#a:Type) (r:binrel a) (x:a) (y:a{_closure0 r x y})
  : Tot (squash (_closure r x y))
  = assert_norm (_closure0 r x y ==> squash (_closure r x y))

val closure_reflexive: #a:Type u#a -> r:binrel u#a u#r a -> Lemma (reflexive (_closure0 r))
let closure_reflexive #a r =
  assert (forall x. _closure0 r x x) by
    (let x = forall_intro () in
     mapply (`FStar.Squash.return_squash);
     mapply (`Refl))

#push-options "--warn_error -271"
val closure_transitive: #a:Type u#a -> r:binrel u#a u#r a -> Lemma (transitive (_closure0 r))
let closure_transitive #a r =
  let open FStar.Squash in
  let aux (x y z:a)
          (s0:squash (_closure r x y))
          (s1:squash (_closure r y z))
    : GTot (squash (_closure r x z))
    = bind_squash s0 (fun p0 ->
      bind_squash s1 (fun p1 ->
      return_squash (Closure x y z p0 p1)))
  in
  let aux (x y z:a)
    : Lemma (requires (_closure0 r x y /\ _closure0 r y z))
            (ensures _closure0 r x z)
            [SMTPat ()]
    = get_squash r x y; get_squash r y z; aux x y z () ()
  in
  ()
#pop-options

let closure #a r =
  closure_reflexive r;
  closure_transitive r;
  _closure0 r

let closure_step #a r x y =
  let q : squash (r x y)  = () in
  assert (squash (r x y) ==> closure r x y) by
    (let xy = implies_intro () in
     let xy : squash (r x y) = unquote (binding_to_term xy) in
     squash_intro ();
     mapply (`Step);
     assumption())

val closure_one_aux: #a:Type u#a -> r:binrel u#a u#r a -> x:a -> y:a
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

let closure_one_aux' (#a:Type u#a) (r:binrel u#a u#r a) (x y:a)
                     (xy:_closure r x y)
  : GTot (squash (x == y \/ (exists z. squash (r x z) /\ closure r z y)))
  = let p = closure_one_aux r x y xy in
    match p with
    | Inl _ -> ()
    | Inr (| z, rxz, _c_zy |) ->
      assert (squash (r x z));
      let s : closure r z y  = FStar.Squash.return_squash _c_zy in
      let ss = FStar.Squash.return_squash s in
      FStar.Squash.give_proof ss;
      assert (closure r z y);
      ()

val closure_one: #a:Type u#a -> r:binrel u#a u#r a -> x:a -> y:a
  -> xy:squash (closure r x y)
  -> GTot (squash (x == y \/ (exists z. squash (r x z) /\ closure r z y)))
let closure_one #a r x y xy =
  let open FStar.Squash in
  bind_squash xy (fun xy ->
  bind_squash xy (closure_one_aux' r x y))

let closure_inversion #a r x y = closure_one r x y ()

val _stable_on_closure: #a:Type u#a -> r:binrel u#a u#r a -> p:(a -> Type0)
  -> p_stable_on_r: squash (forall x y. p x /\ squash (r x y) ==> p y)
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

let squash_implies_to_arrow (p:Type u#p) (q:Type)
  : Lemma (requires (squash (p -> GTot q)))
          (ensures squash p ==> q)
  = ()

let squash_double_arrow (#a:Type u#a) (#p:Type0)
                        (f:(squash (a -> Tot (squash p))))
                     : Tot (squash (a -> GTot p)) =
                     FStar.Squash.squash_double_arrow f

let stable_on_closure #a r p hr =
  assert (forall x y. p x ==> closure r x y ==> p y) by
    (let x = forall_intro () in
     let y = forall_intro () in
     let x : a = unquote (binding_to_term x) in
     let y : a = unquote (binding_to_term y) in
     let px = implies_intro () in
     mapply (`squash_implies_to_arrow);
     mapply (`FStar.Squash.return_squash);
     apply (`squash_double_arrow);
     mapply (`FStar.Squash.return_squash);
     let xy = intro () in
     let xy : _closure r x y = unquote (binding_to_term xy) in
     exact (quote (_stable_on_closure r p hr x y xy (Squash.get_proof _))))
