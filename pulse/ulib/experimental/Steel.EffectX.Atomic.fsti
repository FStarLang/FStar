(*
   Copyright 2020 Microsoft Research

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


module Steel.EffectX.Atomic
open FStar.PCM
open Steel.Memory

val observability : Type0
val has_eq_observability (_:unit) : Lemma (hasEq observability)
val observable : observability
val unobservable : observability

let obs_at_most_one o1 o2 =
  o1==unobservable \/ o2==unobservable

(*
 * AR: removing the refinement obs_at_most_one,
 *     instead adding it to precondition of bind, see below
 *)
let join_obs (o1:observability) (o2:observability) =
  has_eq_observability();
  if observable = o1 || observable = o2
  then observable
  else unobservable

val atomic_repr (a:Type u#a)
                (opened_invariants:inames)
                (g:observability)
                (pre:slprop u#1)
                (post:a -> slprop u#1)
  : Type u#(max a 2)

val return (a:Type u#a)
           (x:a)
           (opened_invariants:inames)
           (p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable (p x) p

val bind (a:Type u#a)
         (b:Type u#b)
         (opened_invariants:inames)
         (o1:observability)
         (o2:observability)
         (pre_f:slprop)
         (post_f:a -> slprop)
         (post_g:b -> slprop)
         (f:atomic_repr a opened_invariants o1 pre_f post_f)
         (g:(x:a -> atomic_repr b opened_invariants o2 (post_f x) post_g))
  : Pure (atomic_repr b opened_invariants (join_obs o1 o2) pre_f post_g)
      (requires obs_at_most_one o1 o2)
      (ensures fun _ -> True)

[@@allow_informative_binders]
total
reifiable reflectable
layered_effect {
  SteelAtomicX : a:Type
              -> opened_invariants:inames
              -> o:observability
              -> pre:slprop u#1
              -> post:(a -> slprop u#1)
              -> Effect
  with
  repr = atomic_repr;
  return = return;
  bind = bind
}

inline_for_extraction
val lift_pure_steel_atomic (a:Type)
                           (opened_invariants:inames)
                           (p:slprop)
                           (wp:pure_wp a)
                           (f:eqtype_as_type unit -> PURE a wp)
  : Pure (atomic_repr a opened_invariants unobservable p (fun _ -> p))
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)

sub_effect PURE ~> SteelAtomicX = lift_pure_steel_atomic

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#o:observability)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelAtomicX a opened_invariants o fp fp'

val new_invariant (opened_invariants:inames) (p:slprop)
  : SteelAtomicX (inv p) opened_invariants unobservable p (fun _ -> emp)

let set_add i o : inames = Set.union (Set.singleton i) o
val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#o:observability)
                   (#p:slprop)
                   (i:inv p{not (i `Set.mem` opened_invariants)})
                   (f:unit -> SteelAtomicX a (set_add i opened_invariants) o
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : SteelAtomicX a opened_invariants o fp fp'

val frame (#a:Type)
          (#opened_invariants:inames)
          (#o:observability)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:unit -> SteelAtomicX a opened_invariants o pre post)
  : SteelAtomicX a opened_invariants o
                (pre `star` frame)
                (fun x -> post x `star` frame)

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelAtomicX unit opened_invariants unobservable p (fun _ -> q)

// Some utilities
let return_atomic #a #opened_invariants #p (x:a)
  : SteelAtomicX a opened_invariants unobservable (p x) p
  = SteelAtomicX?.reflect (return a x opened_invariants p)

#push-options "--query_stats" //working around some flakiness
let h_assert_atomic (#opened_invariants:_) (p:slprop)
  : SteelAtomicX unit opened_invariants unobservable p (fun _ -> p)
  = change_slprop p p (fun m -> ())
#pop-options

let h_intro_emp_l (#opened_invariants:_) (p:slprop)
  : SteelAtomicX unit opened_invariants unobservable p (fun _ -> emp `star` p)
  = change_slprop p (emp `star` p) (fun m -> emp_unit p; star_commutative p emp)

let h_elim_emp_l (#opened_invariants:_) (p:slprop)
  : SteelAtomicX unit opened_invariants unobservable (emp `star` p) (fun _ -> p)
  = change_slprop (emp `star` p) p (fun m -> emp_unit p; star_commutative p emp)

let intro_pure #opened_invariants (#p:slprop) (q:prop { q })
  : SteelAtomicX unit opened_invariants unobservable p (fun _ -> p `star` pure q)
  = change_slprop p (p `star` pure q) (fun m -> emp_unit p; pure_star_interp p q m)

let h_commute (#opened_invariants:_) (p q:slprop)
  : SteelAtomicX unit opened_invariants unobservable (p `star` q) (fun _ -> q `star` p)
  = change_slprop (p `star` q) (q `star` p) (fun m -> star_commutative p q)

let h_assoc_left (#opened_invariants:_) (p q r:slprop)
  : SteelAtomicX unit opened_invariants unobservable ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
  = change_slprop ((p `star` q) `star` r) (p `star` (q `star` r)) (fun m -> star_associative p q r)

let h_assoc_right (#opened_invariants:_) (p q r:slprop)
  : SteelAtomicX unit opened_invariants unobservable (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = change_slprop (p `star` (q `star` r)) ((p `star` q) `star` r) (fun m -> star_associative p q r)

let intro_h_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> slprop)
  : SteelAtomicX unit opened_invariants unobservable (p x) (fun _ -> h_exists p)
  = change_slprop (p x) (h_exists p) (fun m -> intro_h_exists x p m)

let intro_h_exists_erased (#a:Type) (#opened_invariants:_) (x:Ghost.erased a) (p:a -> slprop)
  : SteelAtomicX unit opened_invariants unobservable (p x) (fun _ -> h_exists p)
  = change_slprop (p x) (h_exists p) (fun m -> Steel.Memory.intro_h_exists (Ghost.reveal x) p m)

let h_affine (#opened_invariants:_) (p q:slprop)
  : SteelAtomicX unit opened_invariants unobservable (p `star` q) (fun _ -> p)
  = change_slprop (p `star` q) p (fun m -> affine_star p q m)

(* Witnessing an existential can only be done for frame-monotonic properties.
 * Most PCMs we use have a witness-invariant pts_to, which means this
 * condition is usually trivial and can be hidden from programs. *)
val witness_h_exists (#a:Type) (#opened_invariants:_) (#p:(a -> slprop){is_frame_monotonic p}) (_:unit)
  : SteelAtomicX (Ghost.erased a) opened_invariants unobservable
                (h_exists p) (fun x -> p x)

module U = FStar.Universe

val lift_h_exists_atomic (#a:_) (#u:_) (p:a -> slprop)
  : SteelAtomicX unit u unobservable
                (h_exists p)
                (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

let h_exists_cong_atomic (#a:_) #u (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelAtomicX unit u unobservable
                (h_exists p)
                (fun _ -> h_exists q)
  = change_slprop _ _ (fun m -> h_exists_cong p q)


val elim_pure (#uses:_) (p:prop)
  : SteelAtomicX (_:unit{p}) uses unobservable
                (pure p)
                (fun _ -> emp)
