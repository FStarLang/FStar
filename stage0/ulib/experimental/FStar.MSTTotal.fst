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

module FStar.MSTTotal
module W = FStar.Witnessed.Core
module P = FStar.Preorder

open FStar.Monotonic.Pure

type pre_t (state:Type u#2) = state -> Type0
type post_t (state:Type u#2) (a:Type u#a) = state -> a -> state -> Type0

type repr
      (a:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req:pre_t state)
      (ens:post_t state a)
    =
  s0:state ->
  PURE (a & state)
    (as_pure_wp (fun p ->
                        req s0 /\
                        (forall (x:a) (s1:state). (ens s0 x s1 /\ rel s0 s1) ==> p (x, s1))))

let return
      (a:Type)
      (x:a)
      (state:Type u#2)
      (rel:P.preorder state)
    : repr a state rel
      (fun _ -> True)
      (fun s0 r s1 -> r == x /\ s0 == s1)
    =
  fun s0 -> x, s0

let bind
      (a:Type)
      (b:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req_f:pre_t state)
      (ens_f:post_t state a)
      (req_g:a -> pre_t state)
      (ens_g:a -> post_t state b)
      (f:repr a state rel req_f ens_f)
      (g:(x:a -> repr b state rel (req_g x) (ens_g x)))
    : repr b state rel
      (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
      (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
    =
  fun s0 ->
    let x, s1 = f s0 in
    (g x) s1

let subcomp
      (a:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req_f:pre_t state)
      (ens_f:post_t state a)
      (req_g:pre_t state)
      (ens_g:post_t state a)
      (f:repr a state rel req_f ens_f)
    : Pure (repr a state rel req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)
    =
  f

let if_then_else
      (a:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req_then:pre_t state)
      (ens_then:post_t state a)
      (req_else:pre_t state)
      (ens_else:post_t state a)
      (f:repr a state rel req_then ens_then)
      (g:repr a state rel req_else ens_else)
      (p:bool)
    : Type
    =
  repr a state rel
    (fun s -> (b2t p ==> req_then s) /\ ((~ (b2t p)) ==> req_else s))
    (fun s0 x s1 -> (b2t p ==> ens_then s0 x s1) /\ ((~ (b2t p)) ==> ens_else s0 x s1))

[@@ primitive_extraction]
total
reflectable
effect {
  MSTATETOT (a:Type)
            ([@@@ effect_param] state:Type u#2)
            ([@@@ effect_param] rel:P.preorder state)
            (req:pre_t state)
            (ens:post_t state a)
  with { repr; return; bind; subcomp; if_then_else }
}

[@@ noextract_to "krml"]
let get (#state:Type u#2) (#rel:P.preorder state) ()
    : MSTATETOT state state rel
      (fun _ -> True)
      (fun s0 r s1 -> s0 == r /\ r == s1)
    =
  MSTATETOT?.reflect (fun s0 -> s0, s0)

[@@ noextract_to "krml"]
let put (#state:Type u#2) (#rel:P.preorder state) (s:state)
    : MSTATETOT unit state rel
      (fun s0 -> rel s0 s)
      (fun _ _ s1 -> s1 == s)
    =
  MSTATETOT?.reflect (fun _ -> (), s)

assume
val witness (state:Type u#2)
            (rel:P.preorder state)
            (p:W.s_predicate state)
    : MSTATETOT (W.witnessed state rel p) state rel
      (fun s0 -> p s0 /\ W.stable state rel p)
      (fun s0 _ s1 -> s0 == s1)

assume
val recall (state:Type u#2)
           (rel:P.preorder state)
           (p:W.s_predicate state)
           (w:W.witnessed state rel p)
    : MSTATETOT unit state rel
      (fun _ -> True)
      (fun s0 _ s1 -> s0 == s1 /\ p s1)


(*
 * AR: why do we need the first conjunct in the postcondition?
 *
 *  without this some proofs that use `assert e by t` fail
 *  the way `assert e by t` works is that, it is desugared into `with_tactic e t`
 *  that is abstract and remains in the VC as is at some point, we take a pass over
 *  the VC, find the `with_tactic e t` nodes in it, farm out `G |= e by t` where `G`
 *  is the context at that point in the VC in the original VC, `with_tactic e t`
 *  is simply replace by `True`.
 *  So why is it OK to replace it by `True`, don't we lose the fact that `e` holds for
 *  the rest of the VC?
 *  In the wp world of things, this works fine, since the wp of `assert e by t` is
 *  (fun _ -> with_tactic e t /\ (e ==> ...))
 *  i.e. the type of `assert e by t` already introduces a cut, so replacing it by
 *  `True` works fine.
 *
 *   But this doesn't work when we use the intricate `~ (wp (fun r -> r =!= x))`
 *   combinator to convert from wp to pre post
 *
 *   Basically, the shape of the VC in that case becomes:
 *     (with_tactic e t /\ (((~ with_tactic e t) \/ (e /\ ...)) ==> ...))
 *
 *   In this VC, if we replace the first `with_tactic e t` with `True`, for the second conjunct,
 *   the solver can no longer reason that the first disjunct cannot hold
 *
 *   The wp (fun _ -> True) below helps add that assumption to the second conjunct
 *)

let lift_pure_mst_total
      (a:Type)
      (wp:pure_wp a)
      (state:Type u#2)
      (rel:P.preorder state)
      (f:eqtype_as_type unit -> PURE a wp)
    : repr a state rel
      (fun s0 -> wp (fun _ -> True))
      (fun s0 x s1 -> wp (fun _ -> True) /\  (~ (wp (fun r -> r =!= x \/ s0 =!= s1))))
    =
  elim_pure_wp_monotonicity wp;
  fun s0 ->
    let x = f () in
    x, s0

sub_effect PURE ~> MSTATETOT = lift_pure_mst_total


let mst_tot_assume (#state:Type u#2) (#rel:P.preorder state) (p:Type)
    : MSTATETOT unit state rel (fun _ -> True) (fun m0 _ m1 -> p /\ m0 == m1)
    =
  assume p

let mst_tot_admit (#state:Type u#2) (#rel:P.preorder state) (#a:Type) ()
    : MSTATETOT a state rel (fun _ -> True) (fun _ _ _ -> False)
    =
  admit ()

let mst_tot_assert (#state:Type u#2) (#rel:P.preorder state) (p:Type)
    : MSTATETOT unit state rel (fun _ -> p) (fun m0 _ m1 -> p /\ m0 == m1)
    =
  assert p
