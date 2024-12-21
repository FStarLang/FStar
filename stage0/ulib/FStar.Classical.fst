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

open FStar.Squash

let give_witness #a x = return_squash x

let give_witness_from_squash #a x = x

let lemma_to_squash_gtot #a #p f x =
  f x;
  get_proof (p x)

val get_squashed (#b a: Type) : Pure a (requires (a /\ a == squash b)) (ensures (fun _ -> True))

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
[@@ noextract_to "FSharp"]
let get_squashed #b a =
  let p = get_proof a in
  join_squash #b p
#pop-options

let get_equality #t a b = get_squashed #(equals a b) (a == b)

let impl_to_arrow #a #b impl sx =
  bind_squash #(a -> GTot b) impl (fun f -> bind_squash sx (fun x -> return_squash (f x)))

let arrow_to_impl #a #b f = squash_double_arrow (return_squash (fun x -> f (return_squash x)))

let impl_intro_gtot #p #q f = return_squash f

let impl_intro_tot #p #q f = return_squash #(p -> GTot q) f

let impl_intro #p #q f =
  give_witness #(p ==> q) (squash_double_arrow (return_squash (lemma_to_squash_gtot f)))

let move_requires #a #p #q f x =
  give_proof (bind_squash (get_proof (l_or (p x) (~(p x))))
        (fun (b: l_or (p x) (~(p x))) ->
            bind_squash b
              (fun (b': Prims.sum (p x) (~(p x))) ->
                  match b' with
                  | Prims.Left hp ->
                    give_witness hp;
                    f x;
                    get_proof (p x ==> q x)
                  | Prims.Right hnp -> give_witness hnp)))

let move_requires_2 #a #b #p #q f x y = move_requires (f x) y

let move_requires_3 #a #b #c #p #q f x y z = move_requires (f x y) z

let move_requires_4 #a #b #c #d #p #q f x y z w = move_requires (f x y z) w

// Thanks KM, CH and SZ
let impl_intro_gen #p #q f =
  let g () : Lemma (requires p) (ensures (p ==> q ())) = give_proof #(q ()) (f (get_proof p)) in
  move_requires g ()

(*** Universal quantification *)
let get_forall #a p =
  let t = (forall (x:a). p x) in
  assert (norm [delta; delta_only [`%l_Forall]] t == (squash (x:a -> GTot (p x))));
  norm_spec [delta; delta_only [`%l_Forall]] t;
  get_squashed #(x: a -> GTot (p x)) (forall (x: a). p x)

(* TODO: Maybe this should move to FStar.Squash.fst *)
let forall_intro_gtot #a #p f =
  let id (#a: Type) (x: a) = x in
  let h:(x: a -> GTot (id (p x))) = fun x -> f x in
  return_squash #(forall (x: a). id (p x)) ()

let lemma_forall_intro_gtot #a #p f = give_witness (forall_intro_gtot #a #p f)

let gtot_to_lemma #a #p f x = give_proof #(p x) (return_squash (f x))

let forall_intro_squash_gtot #a #p f =
  bind_squash #(x: a -> GTot (p x))
    #(forall (x: a). p x)
    (squash_double_arrow #a #p (return_squash f))
    (fun f -> lemma_forall_intro_gtot #a #p f)

let forall_intro_squash_gtot_join #a #p f =
  join_squash (bind_squash #(x: a -> GTot (p x))
        #(forall (x: a). p x)
        (squash_double_arrow #a #p (return_squash f))
        (fun f -> lemma_forall_intro_gtot #a #p f))

let forall_intro #a #p f = give_witness (forall_intro_squash_gtot (lemma_to_squash_gtot #a #p f))

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
  let f' (x: a) : Lemma (requires (p x)) (ensures (q x)) = f x (get_proof (p x)) in
  forall_intro (move_requires f')


let ghost_lemma #a #p #q f =
  let lem: x: a -> Lemma (p x ==> q x ()) =
    (fun x ->
      (* basically, the same as above *)
      give_proof (bind_squash (get_proof (l_or (p x) (~(p x))))
            (fun (b: l_or (p x) (~(p x))) ->
                bind_squash b
                  (fun (b': Prims.sum (p x) (~(p x))) ->
                      match b' with
                      | Prims.Left hp ->
                        give_witness hp;
                        f x;
                        get_proof (p x ==> q x ())
                      | Prims.Right hnp -> give_witness hnp))))
  in
  forall_intro lem

(*** Existential quantification *)
let exists_intro #a p witness = ()

#push-options "--warn_error -271" //local SMT pattern misses variables
let exists_intro_not_all_not (#a:Type) (#p:a -> Type)
                             ($f: (x:a -> Lemma (~(p x))) -> Lemma False)
  : Lemma (exists x. p x)
  = let open FStar.Squash in
    let aux ()
        : Lemma (requires (forall x. ~(p x)))
                (ensures False)
                [SMTPat ()]
        = bind_squash
           (get_proof (forall x. ~ (p x)))
           (fun (g: (forall x. ~ (p x))) ->
             bind_squash #(x:a -> GTot (~(p x))) #Prims.empty g
             (fun (h:(x:a -> GTot (~(p x)))) -> f h))
    in
    ()
#pop-options

let forall_to_exists #a #p #r f = forall_intro f

let forall_to_exists_2 #a #p #b #q #r f = forall_intro_2 f

let exists_elim goal #a #p have f =
  bind_squash #_
    #goal
    (join_squash have)
    (fun (| x , pf |) ->
        return_squash pf;
        f x)

(*** Disjunction *)
let or_elim #l #r #goal hl hr =
  impl_intro_gen #l #(fun _ -> goal ()) hl;
  impl_intro_gen #r #(fun _ -> goal ()) hr

let excluded_middle (p: Type) = ()
