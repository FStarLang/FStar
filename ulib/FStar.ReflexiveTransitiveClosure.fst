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

open FStar.Tactics

#set-options "--max_ifuel 1 --max_fuel 0"

noeq
type _closure (#a:Type0) (r:relation a) : a -> a -> Type0 =
| Refl: x:a -> _closure r x x
| Step: x:a -> y:a -> r x y ->_closure r x y
| Closure: x:a -> y:a -> z:a -> _closure r x y -> _closure r y z -> _closure r x z

val closure_reflexive: #a:Type0 -> r:relation a -> Lemma (reflexive (_closure r))
let closure_reflexive #a r =
  assert (forall x. _closure r x x) by
    (let x = forall_intro () in mapply (`Refl))

val closure_transitive: #a:Type0 -> r:relation a -> Lemma (transitive (_closure r))
let closure_transitive #a r =
  assert (transitive (_closure r)) by
    (let x = forall_intro () in
     let y = forall_intro () in
     let z = forall_intro () in
     let h = implies_intro () in
     let _ = destruct_and h in
     seq (fun _ -> mapply (`Closure)) assumption)

let closure #a r =
  closure_reflexive r;
  closure_transitive r;
  _closure r

let closure_step #a r x y =
  assert (r x y ==> closure r x y) by
    (let xy = implies_intro () in
     let xy : r x y = unquote xy in
     squash_intro ();
     exact (quote (Step #a #r x y xy)))

val closure_one: #a:Type0 -> r:relation a -> x:a -> y:a
  -> xy:_closure r x y
  -> GTot (squash (x == y \/ (exists z. r x z /\ closure r z y)))
    (decreases xy)
let rec closure_one #a r x y xy =
  match xy with
  | Refl _ -> ()
  | Step _ _ _ -> ()
  | Closure x a y xa ay -> closure_one r a y ay; closure_one r x a xa

let closure_inversion #a r x y =
  assert (_closure r x y ==> x == y \/ (exists z. r x z /\ closure r z y)) by
    (let xy = implies_intro () in
     let xy : _closure r x y = unquote xy in
     exact (quote (closure_one r x y xy)))

val _stable_on_closure: #a:Type0 -> r:relation a -> p:(a -> Type0)
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
  assert (forall x y. p x /\ closure r x y ==> p y) by
    (let x = forall_intro () in
     let y = forall_intro () in
     let x : a = unquote x in
     let y : a = unquote y in
     let h = implies_intro () in
     let (px, xy) = destruct_and h in
     let xy : closure r x y = unquote xy in
     exact (quote (_stable_on_closure r p hr x y xy (Squash.get_proof _))))
