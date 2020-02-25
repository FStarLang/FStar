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

module HoareDiv

/// A hoare style DIV effect (the specs are hoare triples rather than wp-based)


type repr (a:Type) (req:Type0) (ens:a -> Type0) =
  unit -> DIV a (fun p -> req /\ (forall (x:a). ens x ==> p x))

let return (a:Type) (x:a)
: repr a True (fun r -> r == x)
= fun _ -> x

let bind (a:Type) (b:Type)
  (req_f:Type0) (ens_f:a -> Type0)
  (req_g:a -> Type0) (ens_g:a -> b -> Type0)
  (f:repr a req_f ens_f) (g:(x:a -> repr b (req_g x) (ens_g x)))
: repr b
  (req_f /\ (forall (x:a). ens_f x ==> req_g x))
  (fun y -> exists x. ens_f x /\ ens_g x y)
= fun _ ->
  let x = f () in
  g x ()

let subcomp (a:Type)
  (req_f:Type0) (ens_f:a -> Type0)
  (req_g:Type0) (ens_g:a -> Type0)
  (f:repr a req_f ens_f)
: Pure (repr a req_g ens_g)
  (requires
    (req_g ==> req_f) /\
    (forall (x:a). ens_f x ==> ens_g x))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type)
  (req_then:Type0) (ens_then:a -> Type0)
  (req_else:Type0) (ens_else:a -> Type0)
  (f:repr a req_then ens_then) (g:repr a req_else ens_else)
  (p:Type0)
: Type
= repr a
  ((p ==> req_then) /\ ((~ p) ==> req_else))
  (fun x -> (p ==> ens_then x) /\ ((~ p) ==> ens_else x))


reifiable reflectable
layered_effect {
  HoareDiv : a:Type -> req:Type0 -> ens:(a -> Type0) -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

assume WP_pure_monotonic:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall (x:a). p x ==> q x) ==>
       (wp p ==> wp q))

let lift_pure_meff (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a
  (wp (fun _ -> True))
  (fun x -> ~ (wp (fun r -> r =!= x)))
= fun _ -> f ()

sub_effect PURE ~> HoareDiv = lift_pure_meff

let test ()
: HoareDiv unit True (fun _ -> True)
= ()
