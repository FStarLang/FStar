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

open FStar.IndefiniteDescription

(*
 * Proofs that subrelation and inverse image commute with well-foundedness
 *
 * Reference: Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355
 *)

let subrelation_wf (#a:Type) (#r #sub_r:relation a)
  (sub_w:(x:a -> y:a -> sub_r x y -> r x y))
  (r_wf:well_founded r)
  : well_founded sub_r
  = let rec aux (x:a) (acc_r:acc r x) : Tot (acc sub_r x) (decreases acc_r) =
      AccIntro (fun y sub_r_y_x ->
        aux y
          (match acc_r with
           | AccIntro f -> f y (sub_w y x sub_r_y_x))) in
    fun x -> aux x (r_wf x)

#push-options "--warn_error -271"
let subrelation_squash_wf (#a:Type) (#r #sub_r:relation a)
  (sub_w:(x:a -> y:a -> sub_r x y -> squash (r x y)))
  (r_wf:well_founded r)
  : Lemma (is_well_founded sub_r)
  = let aux (x:a)
      : Lemma (squash (acc_g sub_r x))
              [SMTPat ()]
      = let rec acc_y (x:a) (acc_r:acc r x) (y:a) (p:sub_r y x)
          : Tot (acc_g sub_r y)
                (decreases acc_r)
          = AccIntro_g (acc_y y
              (match acc_r with
               | AccIntro f -> f y (elim_squash (sub_w y x p)))) in
        Squash.return_squash (AccIntro_g (acc_y x (r_wf x)))
    in
    ()
#pop-options

unfold
let subrelation_as_wf (#a:Type) (#r #sub_r:relation a)
  (sub_w:(x:a -> y:a -> sub_r x y -> squash (r x y)))
  (r_wf:well_founded r)
  : well_founded_relation a
  = subrelation_squash_wf sub_w r_wf;
    sub_r

let inverse_image (#a #b:Type) (r_b:relation b) (f:a -> b) : relation a =
  fun x y -> r_b (f x) (f y)

let inverse_image_wf (#a #b:Type) (#r_b:relation b)
  (f:a -> b)
  (r_b_wf:well_founded r_b)
  : well_founded (inverse_image r_b f)
  = let rec aux (x:a) (acc_r_b:acc r_b (f x))
      : Tot (acc (inverse_image r_b f) x)
            (decreases acc_r_b) =
      let get_acc_r_b_y (y:a) (p:(inverse_image r_b f) y x)
        : Tot (acc_r_b_y:acc r_b (f y){acc_r_b_y << acc_r_b})
        = match acc_r_b with
          | AccIntro g -> g (f y) p in
      AccIntro (fun y p -> aux y (get_acc_r_b_y y p)) in
    fun x -> aux x (r_b_wf (f x))
