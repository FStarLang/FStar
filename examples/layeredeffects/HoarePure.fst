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

module HoarePure

type repr (a:Type) (req:pure_pre) (ens:pure_post a) =
  unit -> PURE a (as_wp a req ens)

let return (a:Type) (x:a)
: repr a True (fun r -> r == x)
= fun _ -> x

let bind (a:Type) (b:Type)
  (req_f:pure_pre) (ens_f:pure_post a)
  (req_g:a -> pure_pre) (ens_g:a -> pure_post b)
  (f:repr a req_f ens_f) (g:(x:a -> repr b (req_g x) (ens_g x)))
: repr b
    (req_f /\ (forall (x:a). ens_f x ==> req_g x))
    (fun y -> exists (x:a). ens_f x /\ (ens_g x) y)
= fun _ -> g (f ()) ()

let subcomp (a:Type)
  (req_f:pure_pre) (ens_f:pure_post a)
  (req_g:pure_pre) (ens_g:pure_post a)
  (f:repr a req_f ens_f)
: Pure (repr a req_g ens_g)
  (requires
    (req_g ==> req_f) /\
    (forall (x:a). (req_g /\ ens_f x) ==> ens_g x))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type)
  (req_then:pure_pre) (ens_then:pure_post a)
  (req_else:pure_pre) (ens_else:pure_post a)
  (f:repr a req_then ens_then)
  (g:repr a req_else ens_else)
  (p:Type0)
: Type
= repr a
    ((p ==> req_then) /\ ((~ p) ==> req_else))
    (fun x -> (p ==> ens_then x) /\ ((~ p) ==> ens_else x))

layered_effect {
  HoarePure : a:Type -> pure_pre -> pure_post a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

assume WP_pure_monotonic:
  forall (a:Type) (wp:pure_wp a).
    (forall p q. (forall x. p x ==> q x) ==>
            (wp p ==> wp q))

module T = FStar.Tactics

let lift_pure_hoarepure (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a (as_requires_opaque wp) (as_ensures_opaque wp)
by (T.norm [delta_only [`%as_requires_opaque; `%as_ensures_opaque]])
= fun _ -> f ()

sub_effect PURE ~> HoarePure = lift_pure_hoarepure

assume val p : Type0
assume val f : unit -> Pure unit True (fun _ -> True)
assume val g : squash p -> HoarePure int True (fun n -> n > 2)

#restart-solver
#set-options "--log_queries --fuel 0 --ifuel 0 --using_facts_from 'Prims FStar.Pervasives' --print_full_names"
let test () : HoarePure int p (fun n -> n > 0) =
  f ();
  f ();
  let x = g () in
  f ();
  f ();
  x


assume val f1 : unit -> Pure int (requires True) (ensures fun n -> n > 1)
assume val g1 : unit -> HoarePure int True (fun n -> n > 2)

// #set-options "--debug HoarePure --debug_level WPReqEns --print_universes --print_implicits --print_full_names --debug_level Extreme --ugly --debug_level Rel --print_effect_args --debug_level TwoPhases"

//#restart-solver
//#set-options "--log_queries --fuel 0 --ifuel 0 --using_facts_from 'Prims FStar.Pervasives' --print_full_names" //--debug HoarePure --debug_level WPReqEns"
let test1 () : HoarePure int True (fun n -> n > 0) =
  let x1 = f1 () in
  let x2 = g1 () in
  let x3 = f1 () in
  x3 + 1000

  // let x4 = f1 () in
  // x1 + x2 + x3 + x4
