(*
   Copyright 2019 Microsoft Research

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

module MST

module P = FStar.Preorder

type pre_t (state:Type u#1) = state -> Type0
type post_t (state:Type u#1) (a:Type u#a) = state -> a -> state -> Type0

type repr (a:Type) (state:Type u#1) (rel:P.preorder state) (req:pre_t state) (ens:post_t state a) =
  s0:state ->
  Div (a & state)
  (requires req s0)
  (ensures fun (r, s1) ->
    ens s0 r s1 /\
    rel s0 s1)


let return (a:Type) (x:a) (state:Type u#1) (rel:P.preorder state)
: repr a state rel
  (fun _ -> True)
  (fun s0 r s1 -> r == x /\ s0 == s1)
= fun s0 -> x, s0

let bind (a:Type) (b:Type) (state:Type u#1) (rel:P.preorder state)
  (req_f:pre_t state) (ens_f:post_t state a)
  (req_g:a -> pre_t state) (ens_g:a -> post_t state b)
  (f:repr a state rel req_f ens_f) (g:(x:a -> repr b state rel (req_g x) (ens_g x)))
: repr b state rel
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (ens_g x) s1 r s2))
= fun s0 ->
  let x, s1 = f s0 in
  (g x) s1

let subcomp (a:Type) (state:Type u#1) (rel:P.preorder state)
  (req_f:pre_t state) (ens_f:post_t state a)
  (req_g:pre_t state) (ens_g:post_t state a)
  (f:repr a state rel req_f ens_f)
: Pure (repr a state rel req_g ens_g)
  (requires
    (forall s. req_g s ==> req_f s) /\
    (forall s0 x s1. ens_f s0 x s1 ==> ens_g s0 x s1))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type) (state:Type u#1) (rel:P.preorder state)
  (req_then:pre_t state) (ens_then:post_t state a)
  (req_else:pre_t state) (ens_else:post_t state a)
  (f:repr a state rel req_then ens_then)
  (g:repr a state rel req_else ens_else)
  (p:Type0)
: Type
= repr a state rel
  (fun s -> (p ==> req_then s) /\ ((~ p) ==> req_else s))
  (fun s0 x s1 -> (p ==> ens_then s0 x s1) /\ ((~ p) ==> ens_else s0 x s1))

reifiable reflectable
layered_effect {
  MST : a:Type -> state:Type u#1 -> rel:P.preorder state -> req:pre_t state -> ens:post_t state a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let get (state:Type u#1) (rel:P.preorder state) ()
: MST state state rel
  (fun _ -> True)
  (fun s0 r s1 -> s0 == r /\ r == s1)
= MST?.reflect (fun s0 -> s0, s0)

let put (state:Type u#1) (rel:P.preorder state) (s:state)
: MST unit state rel
  (fun s0 -> rel s0 s)
  (fun _ _ s1 -> s1 == s)
= MST?.reflect (fun _ -> (), s)


type s_predicate (state:Type u#1) = state -> Type0

let stable (state:Type u#1) (rel:P.preorder state) (p:s_predicate state) =
  forall s0 s1. (p s0 /\ rel s0 s1) ==> p s1

assume val witnessed (state:Type u#1) (rel:P.preorder state) (p:s_predicate state) : Type0

assume val witness (state:Type u#1) (rel:P.preorder state) (p:s_predicate state)
: MST unit state rel
  (fun s0 -> p s0 /\ stable state rel p)
  (fun s0 _ s1 -> s0 == s1 /\ witnessed state rel p)

assume val recall (state:Type u#1) (rel:P.preorder state) (p:s_predicate state)
: MST unit state rel
  (fun _ -> witnessed state rel p)
  (fun s0 _ s1 -> s0 == s1 /\ p s1)
