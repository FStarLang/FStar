(*
   Copyright 2015 Chantal Keller and Catalin Hritcu, Microsoft Research and Inria

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

(* Defining accessibility predicates and well-founded recursion like in Coq
   https://coq.inria.fr/library/Coq.Init.Wf.html
*)

module FStar.WellFounded

open FStar.Preorder

(*
 * The accessibility relation
 *)
noeq
type acc (#a:Type) (r:relation a) (x:a) : Type =
  | AccIntro : (y:a -> r y x -> acc r y) -> acc r x

(*
 * A relation r is well-founded if every element is accessible
 *)
let well_founded (#a:Type) (r:relation a) = x:a -> acc r x

(*
 * Accessibility predicates can be used for implementing
 *   total fix points
 *)
let acc_inv (#aa:Type) (#r:relation aa) (x:aa) (a:acc r x)
  : (e:(y:aa -> r y x -> acc r y){e << a})
  = match a with | AccIntro h1 -> h1

let rec fix_F (#aa:Type) (#r:relation aa) (#p:(aa -> Type))
              (f: (x:aa -> (y:aa -> r y x -> p y) -> p x))
              (x:aa) (a:acc r x)
  : Tot (p x) (decreases a)
  = f x (fun y h -> fix_F f y (acc_inv x a y h))

let fix (#aa:Type) (#r:relation aa) (rwf:well_founded r)
        (p:aa -> Type) (f:(x:aa -> (y:aa -> r y x -> p y) -> p x))
        (x:aa)
  : p x
  = fix_F f x (rwf x)


(*
 * An erasable version of the accessibility relation,
 *   may be well-suited when the relation is in squashed form,
 *   and when you want to use the internalized support for
 *   accessibility-based termination proofs in F*
 *)
[@@ erasable]
noeq
type acc_g (#a:Type) (r:relation a) (x:a) : Type =
  | AccIntro_g : (y:a -> r y x -> acc_g r y) -> acc_g r x

type is_well_founded (#a:Type) (rel:relation a) =
  forall (x:a). squash (acc_g rel x)

type well_founded_relation (a:Type) = rel:relation a{is_well_founded rel}

open FStar.IndefiniteDescription

(*
 * Given a well-founded relation, we can extract accessibility proof
 *)
let well_founded_acc_g (#a:Type) (r:relation a{is_well_founded r}) (x:a)
  : acc_g r x
  = elim_squash ()

(*
 * Use as_well_founded to get a well-founded relation
 *   passing in a proof for accessibility
 *)

#push-options "--warn_error -271"
unfold
let as_well_founded (#a:Type) (#rel:relation a) (f:(x:a -> acc_g rel x))
  : well_founded_relation a
  = let aux (x:a)
      : Lemma (squash (acc_g rel x))
              [SMTPat ()]
      = FStar.Squash.return_squash (f x) in
    rel
#pop-options

(*
 * map_squash_well_founded can be used to move between squash and non-squash worlds
 *
 * See FStar.LexicographicOrdering.fst for an example
 *)

#push-options "--warn_error -271"
let map_squash_is_well_founded (#a:Type) (#r1 #r2:relation a)
  (map:(x:a -> y:a -> r1 x y -> squash (r2 x y)))
  (wf2:well_founded r2)
  : Lemma (is_well_founded r1)
  = let aux (x:a)
      : Lemma (squash (acc_g r1 x))
              [SMTPat ()]
      = let rec acc_y (x:a) (acc2_x:acc r2 x) (y:a) (p:r1 y x)
          : Tot (acc_g r1 y)
                (decreases acc2_x)
          = AccIntro_g (acc_y y
              (match acc2_x with
               | AccIntro f -> f y (elim_squash (map y x p)))) in
        Squash.return_squash (AccIntro_g (acc_y x (wf2 x)))
    in
    ()
#pop-options

unfold
let map_squash_well_founded (#a:Type) (#r1 #r2:relation a)
  (map:(x:a -> y:a -> r1 x y -> squash (r2 x y)))
  (wf2:well_founded r2)
  : well_founded_relation a
  = map_squash_is_well_founded map wf2;
    r1
