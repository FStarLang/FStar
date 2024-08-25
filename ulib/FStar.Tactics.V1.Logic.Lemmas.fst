(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.V1.Logic.Lemmas

let fa_intro_lem (#a:Type) (#p:a -> Type) (f:(x:a -> squash (p x))) : Lemma (forall (x:a). p x) =
  FStar.Classical.lemma_forall_intro_gtot
    ((fun x -> FStar.IndefiniteDescription.elim_squash (f x)) <: (x:a -> GTot (p x)))

let split_lem #a #b sa sb = ()

let imp_intro_lem #a #b f =
  FStar.Classical.give_witness (FStar.Classical.arrow_to_impl (fun (x:squash a) -> FStar.Squash.bind_squash x f))

let __lemma_to_squash #req #ens (_ : squash req) (h : (unit -> Lemma (requires req) (ensures ens))) : squash ens =
  h ()

let vbind #p #q sq f = FStar.Classical.give_witness_from_squash (FStar.Squash.bind_squash sq f)

let or_ind #p #q #phi o l r = ()

let bool_ind b phi l r = ()

let or_intro_1 #p #q _ = ()

let or_intro_2 #p #q _ = ()

let __and_elim #p #q #phi p_and_q f = ()

let __and_elim' #p #q #phi p_and_q f = ()

let __witness #a x #p _ = ()

let __elim_exists' #t (#pred : t -> Type0) #goal (h : (exists x. pred x))
                          (k : (x:t -> pred x -> squash goal)) : squash goal =
  FStar.Squash.bind_squash #(x:t & pred x) h (fun (|x, pf|) -> k x pf)

let __forall_inst #t (#pred : t -> Type0) (h : (forall x. pred x)) (x : t) : squash (pred x) =
    ()

let __forall_inst_sq #t (#pred : t -> Type0) (h : squash (forall x. pred x)) (x : t) : squash (pred x) =
    ()

let sklem0 (#a:Type) (#p : a -> Type0) ($v : (exists (x:a). p x)) (phi:Type0) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()

let lemma_from_squash #a #b f x = let _ = f x in assert (b x)

let lem1_fa #a #pre #post
  ($lem : (x:a -> Lemma (requires pre x) (ensures post x))) :
  Lemma (forall (x:a). pre x ==> post x) =
  let l' x : Lemma (pre x ==> post x) =
    Classical.move_requires lem x
  in
  Classical.forall_intro l'

let lem2_fa #a #b #pre #post
  ($lem : (x:a -> y:b -> Lemma (requires pre x y) (ensures post x y))) :
  Lemma (forall (x:a) (y:b). pre x y ==> post x y) =
  let l' x y : Lemma (pre x y ==> post x y) =
    Classical.move_requires (lem x) y
  in
  Classical.forall_intro_2 l'

let lem3_fa #a #b #c #pre #post
  ($lem : (x:a -> y:b -> z:c -> Lemma (requires pre x y z) (ensures post x y z))) :
  Lemma (forall (x:a) (y:b) (z:c). pre x y z ==> post x y z) =
  let l' x y z : Lemma (pre x y z ==> post x y z) =
    Classical.move_requires (lem x y) z
  in
  Classical.forall_intro_3 l'

let revert_squash #a #b s x = let x : (_:unit{forall x. b x}) = s in ()