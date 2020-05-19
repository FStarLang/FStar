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


module Steel.PCM.Effect.Atomic
open Steel.PCM
open Steel.PCM.Memory

let observability : Type = bool
let observable = true
let unobservable = false

let obs_at_most_one o1 o2 : bool =
  not (o1 && o2)

let join_obs (o1:observability) (o2:observability{obs_at_most_one o1 o2}) = o1 || o2

let obs_pcm : pcm observability = {
  p = {
    composable = (fun x y -> ~(x==true /\ y==true));
    op = join_obs;
    one = unobservable;
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}


type atomic_repr (a:Type)
                 (opened_invariants:inames)
                 (g:observability)
                 (pre:slprop)
                 (post:a -> slprop) =
  action_except a opened_invariants pre post

let return (a:Type u#a) (x:a) (opened_invariants:inames) (p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable (p x) p
  = fun _ -> x

let bind (a:Type)
         (b:Type)
         (opened_invariants:inames)
         (o1:observability)
         (o2:observability{obs_at_most_one o1 o2})
         (pre_f:slprop)
         (post_f:a -> slprop)
         (post_g:b -> slprop)
         (f:atomic_repr a opened_invariants o1 pre_f post_f)
         (g:(x:a -> atomic_repr b opened_invariants o2 (post_f x) post_g))
  : atomic_repr b opened_invariants (join_obs o1 o2) pre_f post_g
  = fun m0 ->
    let x = f () in
    g x ()

let subcomp (a:Type)
            (opened_invariants:inames)
            (o:observability)
            (pre:slprop)
            (post:a -> slprop)
            (f:atomic_repr a opened_invariants o pre post)
  : Pure (atomic_repr a opened_invariants o pre post)
         (requires True)
         (ensures fun _ -> True)
  = f

let if_then_else (a:Type)
                 (opened_invariants:inames)
                 (o:observability)
                 (pre:slprop)
                 (post:a -> slprop)
                 (f:atomic_repr a opened_invariants o pre post)
                 (g:atomic_repr a opened_invariants o pre post)
                 (p:Type0)
  : Type
  = atomic_repr a opened_invariants o pre post

total
reifiable reflectable
layered_effect {
  SteelAtomic : a:Type
              -> opened_invariants:inames
              -> o:observability
              -> pre:slprop u#1
              -> post:(a -> slprop u#1)
              -> Effect
  with
  repr = atomic_repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

inline_for_extraction
let lift_pure_steel_atomic (a:Type)
                           (opened_invariants:inames)
                           (p:slprop)
                           (wp:pure_wp a)
                           (f:unit -> PURE a wp)
  : Pure (atomic_repr a opened_invariants unobservable p (fun _ -> p))
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun _ -> let x = f () in x

sub_effect PURE ~> SteelAtomic = lift_pure_steel_atomic

[@@warn_on_use "as_atomic_action is a trusted primitive"]
let as_atomic_action #a (#opened_invariants:inames) (#o:observability) (#fp:slprop) (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelAtomic a opened_invariants o fp fp'
  = SteelAtomic?.reflect f

let new_invariant (opened_invariants:inames) (p:slprop)
  : SteelAtomic (inv p) opened_invariants unobservable p (fun _ -> emp)
  = SteelAtomic?.reflect (Steel.PCM.Memory.new_invariant opened_invariants p)

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#o:observability)
                   (#p:slprop)
                   (i:inv p{not (i `Set.mem` opened_invariants)})
                   (f:unit -> SteelAtomic a (Set.union (Set.singleton i) opened_invariants) o (p `star` fp) (fun x -> p `star` fp' x))
  : SteelAtomic a opened_invariants o fp fp'
  = SteelAtomic?.reflect (Steel.PCM.Memory.with_invariant i (reify (f())))

assume
val frame_action_except (#a:Type) (#opened_invariants:inames)
                        (#pre:slprop) (#post:a -> slprop)
                        (frame:slprop)
                        ($f:action_except a opened_invariants pre post)
    : action_except a opened_invariants (pre `star` frame) (fun x -> post x `star` frame)

let frame (#a:Type) (#opened_invariants:inames) (#o:observability)
          (#pre:slprop) (#post:a -> slprop)
          (frame:slprop)
          ($f:unit -> SteelAtomic a opened_invariants o pre post)
  : SteelAtomic a opened_invariants o
                (pre `star` frame)
                (fun x -> post x `star` frame)
  = SteelAtomic?.reflect (frame_action_except frame (reify (f ())))

assume
val change_slprop_action_except (#opened_invariants:inames)
                                (p q:slprop)
                                (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : action_except unit opened_invariants p (fun _ -> q)

let change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelAtomic unit opened_invariants unobservable p (fun _ -> q)
  = SteelAtomic?.reflect (change_slprop_action_except p q proof)
