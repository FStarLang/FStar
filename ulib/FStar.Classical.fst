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

module FStar.Classical

let impl_to_arrow #a #b impl sx = ()

let arrow_to_impl #a #b f =
  if a then f () else ()

let impl_intro_gtot #p #q f = arrow_to_impl f

let impl_intro_tot #p #q f = arrow_to_impl f

let impl_intro #p #q f = arrow_to_impl #p #q fun h -> f h

let move_requires #a #p #q f x =
  arrow_to_impl #(p x) #(q x) fun h -> f x

let move_requires_2 #a #b #p #q f x y = move_requires (f x) y

let move_requires_3 #a #b #c #p #q f x y z = move_requires (f x y) z

let move_requires_4 #a #b #c #d #p #q f x y z w = move_requires (f x y z) w

let impl_intro_gen #p #q f =
  if p then f () else ()

let forall_intro_gtot #a #p f =
  if exists x. ~(p x) then
    f (indefinite_description fun x -> ~(p x))
  else
    ()

let lemma_forall_intro_gtot #a #p f =
  forall_intro_gtot #a #p f

let gtot_to_lemma #a #p f x = f x

let forall_intro_squash_gtot #a #p f =
  forall_intro_gtot #a #p f

let forall_intro_squash_gtot_join #a #p f =
  forall_intro_gtot #a #p f

let forall_intro #a #p f =
  let f (x: a) : squash (p x) = f x in
  forall_intro_gtot #a #p f

let forall_intro_with_pat #a #c #p pat f = forall_intro #a #p f

let forall_intro_sub #a #p f = forall_intro f

(* Some basic stuff, should be moved to FStar.Squash, probably *)
let forall_intro_2 #a #b #p f =
  let g: x: a -> Lemma (forall (y: b x). p x y) = fun x -> forall_intro (f x) in
  forall_intro g

let forall_intro_2_with_pat #a #b #c #p pat f = forall_intro_2 #a #b #p f

let forall_intro_3 #a #b #c #p f =
  let g: x: a -> Lemma (forall (y: b x) (z: c x y). p x y z) = fun x -> forall_intro_2 (f x) in
  forall_intro g

let forall_intro_3_with_pat #a #b #c #d #p pat f = forall_intro_3 #a #b #c #p f

let forall_intro_4 #a #b #c #d #p f =
  let g: x: a -> Lemma (forall (y: b x) (z: c x y) (w: d x y z). p x y z w) =
    fun x -> forall_intro_3 (f x)
  in
  forall_intro g

let forall_impl_intro #a #p #q f =
  let f' (x: a) : Lemma (requires (p x)) (ensures (q x)) = f x () in
  forall_intro (move_requires f')

let ghost_lemma #a #p #q f =
  let lem (x: a) : Lemma (p x ==> q x ()) =
    impl_intro_gen #(p x) #(q x) fun _ -> f x in
  forall_intro lem

(*** Existential quantification *)
let exists_intro #a p witness = ()

let exists_intro_not_all_not (#a:Type) (#p:a -> prop)
                             ($f: (x:a -> Lemma (~(p x))) -> Lemma False)
    : Lemma (exists x. p x) =
  arrow_to_impl #(forall x. ~(p x)) #False (fun _ -> f fun x -> ())

let forall_to_exists #a #p #r f = forall_intro f

let forall_to_exists_2 #a #p #b #q #r f = forall_intro_2 f

let exists_elim goal #a #p have f =
  f (indefinite_description p)

(*** Disjunction *)
let or_elim #l #r #goal hl hr =
  impl_intro_gen #l #(fun _ -> goal ()) hl;
  impl_intro_gen #r #(fun _ -> goal ()) hr

let excluded_middle (p: prop) = ()