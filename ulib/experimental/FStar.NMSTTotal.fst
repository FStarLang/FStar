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

module FStar.NMSTTotal

module W = FStar.Witnessed.Core
module P = FStar.Preorder

module M = FStar.MSTTotal

open FStar.Monotonic.Pure

type tape = nat -> bool

type repr
      (a:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req:M.pre_t state)
      (ens:M.post_t state a)
    =
  (tape & nat) ->
    M.MSTATETOT (a & nat) state rel req (fun s0 (x, _) s1 -> ens s0 x s1)


let return (a:Type) (x:a) (state:Type u#2) (rel:P.preorder state)
    : repr a state rel (fun _ -> True) (fun s0 r s1 -> r == x /\ s0 == s1)
    =
  fun (_, n) -> x, n

let bind
      (a:Type)
      (b:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req_f:M.pre_t state)
      (ens_f:M.post_t state a)
      (req_g:a -> M.pre_t state)
      (ens_g:a -> M.post_t state b)
      (f:repr a state rel req_f ens_f)
      (g:(x:a -> repr b state rel (req_g x) (ens_g x)))
    : repr b state rel
      (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
      (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
    =
  fun (t, n) ->
    let x, n1 = f (t, n) in
    (g x) (t, n1)

let subcomp
      (a:Type)
      (state:Type u#2)
      (rel:P.preorder state)
      (req_f:M.pre_t state)
      (ens_f:M.post_t state a)
      (req_g:M.pre_t state)
      (ens_g:M.post_t state a)
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
      (req_then:M.pre_t state)
      (ens_then:M.post_t state a)
      (req_else:M.pre_t state)
      (ens_else:M.post_t state a)
      (f:repr a state rel req_then ens_then)
      (g:repr a state rel req_else ens_else)
      (p:bool)
    : Type
    =
  repr a state rel
    (fun s0 -> (p ==> req_then s0) /\ ((~ p) ==> req_else s0))
    (fun s0 x s1 -> (p ==> ens_then s0 x s1) /\ ((~ p) ==> ens_else s0 x s1))

[@@ primitive_extraction]
total
reflectable
effect {
  NMSTATETOT (a:Type)
             ([@@@ effect_param] state:Type u#2)
             ([@@@ effect_param] rel:P.preorder state)
             (req:M.pre_t state)
             (ens:M.post_t state a)
  with { repr; return; bind; subcomp; if_then_else }
}

[@@ noextract_to "krml"]
let get (#state:Type u#2) (#rel:P.preorder state) ()
    : NMSTATETOT state state rel
      (fun _ -> True)
      (fun s0 s s1 -> s0 == s /\ s == s1)
    =
  NMSTATETOT?.reflect (fun (_, n) -> MSTTotal.get (), n)

[@@ noextract_to "krml"]
let put (#state:Type u#2) (#rel:P.preorder state) (s:state)
    : NMSTATETOT unit state rel
      (fun s0 -> rel s0 s)
      (fun _ _ s1 -> s1 == s)
    =
  NMSTATETOT?.reflect (fun (_, n) -> MSTTotal.put s, n)


[@@ noextract_to "krml"]
let witness (state:Type u#2) (rel:P.preorder state) (p:W.s_predicate state)
    : NMSTATETOT (W.witnessed state rel p) state rel
      (fun s0 -> p s0 /\ W.stable state rel p)
      (fun s0 _ s1 -> s0 == s1)
    =
  NMSTATETOT?.reflect (fun (_, n) -> M.witness state rel p, n)

[@@ noextract_to "krml"]
let recall (state:Type u#2)
           (rel:P.preorder state)
           (p:W.s_predicate state)
           (w:W.witnessed state rel p)
    : NMSTATETOT unit state rel
      (fun _ -> True)
      (fun s0 _ s1 -> s0 == s1 /\ p s1)
    =
  NMSTATETOT?.reflect (fun (_, n) -> M.recall state rel p w, n)

[@@ noextract_to "krml"]
let sample (#state:Type u#2) (#rel:P.preorder state) ()
    : NMSTATETOT bool state rel
      (fun _ -> True)
      (fun s0 _ s1 -> s0 == s1)
    =
  NMSTATETOT?.reflect (fun (t, n) -> t n, n+1)

let lift_pure_nmst
      (a:Type)
      (wp:pure_wp a)
      (state:Type u#2)
      (rel:P.preorder state)
      (f:eqtype_as_type unit -> PURE a wp)
    : repr a state rel
      (fun s0 -> wp (fun _ -> True))
      (fun s0 x s1 -> wp (fun _ -> True) /\  (~ (wp (fun r -> r =!= x \/ s0 =!= s1))))
    =
  fun (_, n) ->
    elim_pure_wp_monotonicity wp;
    let x = f () in
    x, n

sub_effect PURE ~> NMSTATETOT = lift_pure_nmst

let nmst_tot_assume (#state:Type u#2) (#rel:P.preorder state) (p:Type)
    : NMSTATETOT unit state rel (fun _ -> True) (fun m0 _ m1 -> p /\ m0 == m1)
    =
  assume p

let nmst_tot_admit (#state:Type u#2) (#rel:P.preorder state) (#a:Type) ()
    : NMSTATETOT a state rel (fun _ -> True) (fun _ _ _ -> False)
    =
  admit ()

let nmst_tot_assert (#state:Type u#2) (#rel:P.preorder state) (p:Type)
    : NMSTATETOT unit state rel (fun _ -> p) (fun m0 _ m1 -> p /\ m0 == m1)
    =
  assert p
