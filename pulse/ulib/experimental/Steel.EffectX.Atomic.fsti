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

#set-options "--warn_error -330"  //turn off the experimental feature warning

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

val join_preserves_interp (hp:slprop) (m0 m1:mem)
  : Lemma
    (requires (interp hp m0 /\ disjoint m0 m1))
    (ensures (interp hp (join m0 m1)))
    [SMTPat (interp hp (join m0 m1))]

val respects_fp (#fp:slprop) (p: hmem fp -> prop) : prop
#push-options "--query_stats"
val reveal_respects_fp (#fp:_) (p:hmem fp -> prop)
  : Lemma (respects_fp p <==>
           (forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)))
          [SMTPat (respects_fp #fp p)]
#pop-options
let fp_mprop (fp:slprop) = p:(hmem fp -> prop) { respects_fp p }

val respects_binary_fp (#a:Type) (#pre:slprop) (#post:a -> slprop)
                       (q:(hmem pre -> x:a -> hmem (post x) -> prop)) : prop

val reveal_respects_binary_fp (#a:Type) (#pre:slprop) (#post:a -> slprop)
                              (q:(hmem pre -> x:a -> hmem (post x) -> prop))
  : Lemma (respects_binary_fp q <==>
            //at this point we need to know interp pre (join h_pre h) -- use join_preserves_interp for that
            (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
              q h_pre x h_post <==> q (join h_pre h) x h_post) /\
            //can join any disjoint heap to the post-heap and q is still valid
            (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
              q h_pre x h_post <==> q h_pre x (join h_post h)))
           [SMTPat (respects_binary_fp #a #pre #post q)]

let fp_binary_mprop #a (pre:slprop) (post: a -> slprop) =
  p:(hmem pre -> x:a -> hmem (post x) -> prop){ respects_binary_fp p }


val atomic_repr (a:Type u#a)
                (opened_invariants:inames)
                (g:observability)
                (pre:slprop u#1)
                (post:a -> slprop u#1)
                (req:fp_mprop pre)
                (ens:fp_binary_mprop pre post)
  : Type u#(max a 2)

unfold
let return_req (p:slprop) : fp_mprop p = fun _ -> True

unfold
let return_ens (#a:Type) (x:a) (p:a -> slprop) : fp_binary_mprop (p x) p = fun _ r _ -> r == x

val return (a:Type u#a)
           (x:a)
           (opened_invariants:inames)
           (p:a -> slprop u#1)
  : atomic_repr a opened_invariants unobservable (p x) p (return_req (p x)) (return_ens x p)

unfold
let bind_req (#a:Type) (#pre_f:slprop) (#post_f:a -> slprop)
             (req_f:fp_mprop pre_f) (ens_f:fp_binary_mprop pre_f post_f)
             (req_g:(x:a -> fp_mprop (post_f x)))
  : fp_mprop pre_f
  = fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1)

unfold
let bind_ens (#a:Type) (#b:Type) (#pre_f:slprop) (#post_f:a -> slprop)
             (req_f:fp_mprop pre_f) (ens_f:fp_binary_mprop pre_f post_f)
             (#post_g:b -> slprop) (ens_g:(x:a -> fp_binary_mprop (post_f x) post_g))
  : fp_binary_mprop pre_f post_g
  = fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2)

val bind (a:Type u#a)
         (b:Type u#b)
         (opened_invariants:inames)
         (o1:observability)
         (o2:observability)
         (pre_f:slprop)
         (post_f:a -> slprop)
         (req_f:fp_mprop pre_f)
         (ens_f:fp_binary_mprop pre_f post_f)
         (post_g:b -> slprop)
         (req_g:(x:a -> fp_mprop (post_f x)))
         (ens_g:(x:a -> fp_binary_mprop (post_f x) post_g))
         (f:atomic_repr a opened_invariants o1 pre_f post_f req_f ens_f)
         (g:(x:a -> atomic_repr b opened_invariants o2 (post_f x) post_g (req_g x) (ens_g x)))
  : Pure (atomic_repr b opened_invariants (join_obs o1 o2)
                      pre_f
                      post_g
                      (bind_req req_f ens_f req_g)
                      (bind_ens req_f ens_f ens_g)
          )
      (requires obs_at_most_one o1 o2)
      (ensures fun _ -> True)

unfold
let subcomp_pre (#a:Type)
                (#pre:slprop)
                (#post:a -> slprop)
                (req_f:fp_mprop pre)
                (ens_f:fp_binary_mprop pre post)
                (req_g:fp_mprop pre)
                (ens_g:fp_binary_mprop pre post)
   : pure_pre
   = (forall h. req_g h ==> req_f h) /\
     (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1)

val subcomp (a:Type)
            (opened_invariants:inames)
            (o:observability)
            (pre:slprop)
            (post:a -> slprop)
            (req_f:fp_mprop pre)
            (ens_f:fp_binary_mprop pre post)
            (req_g:fp_mprop pre)
            (ens_g:fp_binary_mprop pre post)
            (f:atomic_repr a opened_invariants o pre post req_f ens_f)
  : Pure (atomic_repr a opened_invariants o pre post req_g ens_g)
         (requires subcomp_pre req_f ens_f req_g ens_g)
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
              -> req:fp_mprop pre
              -> ens:fp_binary_mprop pre post
              -> Effect
  with
  repr = atomic_repr;
  return = return;
  bind = bind;
  subcomp = subcomp
}

unfold
let trivial_req (p:slprop) : fp_mprop p = fun _ -> True

unfold
let trivial_ens (#a:Type) (pre:slprop) (post:a -> slprop) : fp_binary_mprop pre post
  = fun _ _ _ -> True


inline_for_extraction
val lift_pure_steel_atomic (a:Type)
                           (opened_invariants:inames)
                           (p:slprop)
                           (wp:pure_wp a)
                           (f:eqtype_as_type unit -> PURE a wp)
  : Pure (atomic_repr a opened_invariants unobservable
           p (fun _ -> p)
           (trivial_req p) (trivial_ens p (fun _ -> p))
         )
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)

sub_effect PURE ~> SteelAtomicX = lift_pure_steel_atomic

effect SteelAtomicXT (a:Type) (opened:inames) (o:observability) (pre:slprop) (post:a -> slprop) =
  SteelAtomicX a opened o pre post (fun _ -> True) (fun _ _ _ -> True)

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#o:observability)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : SteelAtomicXT a opened_invariants o fp fp'

val new_invariant (opened_invariants:inames) (p:slprop)
  : SteelAtomicXT (inv p) opened_invariants unobservable p (fun _ -> emp)

let set_add i o : inames = Set.union (Set.singleton i) o
val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#o:observability)
                   (#p:slprop)
                   (i:inv p{not (i `Set.mem` opened_invariants)})
                   (f:unit -> SteelAtomicXT a (set_add i opened_invariants) o
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : SteelAtomicXT a opened_invariants o fp fp'

val frame (#a:Type)
          (#opened_invariants:inames)
          (#o:observability)
          (#pre:slprop)
          (#post:a -> slprop)
          (#req:fp_mprop pre)
          (#ens:fp_binary_mprop pre post)
          (frame:slprop)
          ($f:unit -> SteelAtomicX a opened_invariants o pre post req ens)
  : SteelAtomicX a opened_invariants o
                (pre `star` frame)
                (fun x -> post x `star` frame)
                req
                ens

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelAtomicXT unit opened_invariants unobservable p (fun _ -> q)

// Some utilities
let return_atomic #a #opened_invariants #p (x:a)
  : SteelAtomicX a opened_invariants unobservable (p x) p (return_req (p x)) (return_ens x p)
  = SteelAtomicX?.reflect (return a x opened_invariants p)

let h_assert_atomic (#opened_invariants:_) (p:slprop)
  : SteelAtomicXT unit opened_invariants unobservable p (fun _ -> p)
  = change_slprop p p (fun m -> ())

let h_intro_emp_l (#opened_invariants:_) (p:slprop)
  : SteelAtomicXT unit opened_invariants unobservable p (fun _ -> emp `star` p)
  = change_slprop p (emp `star` p) (fun m -> emp_unit p; star_commutative p emp)

let h_elim_emp_l (#opened_invariants:_) (p:slprop)
  : SteelAtomicXT unit opened_invariants unobservable (emp `star` p) (fun _ -> p)
  = change_slprop (emp `star` p) p (fun m -> emp_unit p; star_commutative p emp)

let intro_pure #opened_invariants (#p:slprop) (q:prop { q })
  : SteelAtomicXT unit opened_invariants unobservable p (fun _ -> p `star` pure q)
  = change_slprop p (p `star` pure q) (fun m -> emp_unit p; pure_star_interp p q m)

let h_commute (#opened_invariants:_) (p q:slprop)
  : SteelAtomicXT unit opened_invariants unobservable (p `star` q) (fun _ -> q `star` p)
  = change_slprop (p `star` q) (q `star` p) (fun m -> star_commutative p q)

let h_assoc_left (#opened_invariants:_) (p q r:slprop)
  : SteelAtomicXT unit opened_invariants unobservable ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
  = change_slprop ((p `star` q) `star` r) (p `star` (q `star` r)) (fun m -> star_associative p q r)

let h_assoc_right (#opened_invariants:_) (p q r:slprop)
  : SteelAtomicXT unit opened_invariants unobservable (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = change_slprop (p `star` (q `star` r)) ((p `star` q) `star` r) (fun m -> star_associative p q r)

let intro_h_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> slprop)
  : SteelAtomicXT unit opened_invariants unobservable (p x) (fun _ -> h_exists p)
  = change_slprop (p x) (h_exists p) (fun m -> intro_h_exists x p m)

let intro_h_exists_erased (#a:Type) (#opened_invariants:_) (x:Ghost.erased a) (p:a -> slprop)
  : SteelAtomicXT unit opened_invariants unobservable (p x) (fun _ -> h_exists p)
  = change_slprop (p x) (h_exists p) (fun m -> Steel.Memory.intro_h_exists (Ghost.reveal x) p m)

let h_affine (#opened_invariants:_) (p q:slprop)
  : SteelAtomicXT unit opened_invariants unobservable (p `star` q) (fun _ -> p)
  = change_slprop (p `star` q) p (fun m -> affine_star p q m)

(* Witnessing an existential can only be done for frame-monotonic properties.
 * Most PCMs we use have a witness-invariant pts_to, which means this
 * condition is usually trivial and can be hidden from programs. *)
val witness_h_exists (#a:Type) (#opened_invariants:_) (#p:(a -> slprop){is_frame_monotonic p}) (_:unit)
  : SteelAtomicXT (Ghost.erased a) opened_invariants unobservable
                (h_exists p) (fun x -> p x)

module U = FStar.Universe

val lift_h_exists_atomic (#a:_) (#u:_) (p:a -> slprop)
  : SteelAtomicXT unit u unobservable
                (h_exists p)
                (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

let h_exists_cong_atomic (#a:_) #u (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelAtomicXT unit u unobservable
                (h_exists p)
                (fun _ -> h_exists q)
  = change_slprop _ _ (fun m -> h_exists_cong p q)


val elim_pure (#uses:_) (p:prop)
  : SteelAtomicXT (_:unit{p}) uses unobservable
                (pure p)
                (fun _ -> emp)
