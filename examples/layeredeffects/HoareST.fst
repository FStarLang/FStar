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

module HoareST

open FStar.Heap
open FStar.ST

/// ST effect implemented as a layered effect over STATE

#set-options "--max_fuel 0 --max_ifuel 0"

type pre_t = heap -> Type0
type post_t (a:Type) = heap -> a -> heap -> Type0

/// It has two indices: one for the precondition and one for the postcondition
///
/// Its encoding in STATE is as expected

type repr (a:Type) (pre:pre_t) (post:post_t a) : Type =
  unit -> STATE a (fun p h -> pre h /\ (forall (x:a) (h1:heap). post h x h1 ==> p x h1))

let return (a:Type) (x:a)
: repr a (fun _ -> True) (fun h0 r h1 -> r == x /\ h0 == h1)
= fun _ -> x

/// bind bakes in the weakening of f's post to compose it with g's pre

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:a -> post_t b)
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) (post_g x)))
: repr b
  (fun h0 -> pre_f h0 /\ (forall (x:a) (h1:heap). post_f h0 x h1 ==> pre_g x h1))
  (fun h0 y h2 -> exists (x:a) (h1:heap). post_f h0 x h1 /\ post_g x h1 y h2)
= fun _ ->
  let x = f () in
  g x ()

/// sub comp rule

let subcomp (a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:pre_t) (post_g:post_t a)
  (f:repr a pre_f post_f)
: Pure (repr a pre_g post_g)
  (requires
    (forall (h:heap). pre_g h ==> pre_f h) /\
    (forall (h0 h1:heap) (x:a). post_f h0 x h1 ==> post_g h0 x h1))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:pre_t) (post_g:post_t a)
  (f:repr a pre_f post_f)
  (g:repr a pre_g post_g)
  (p:Type0)
  : Type
= repr a
  (fun h -> (p ==> pre_f h) /\ ((~ p) ==> pre_g h))
  (fun h0 r h1 -> (p ==> post_f h0 r h1) /\ ((~ p) ==> post_g h0 r h1))

// let conjunction_is_stronger_f (a:Type)
//   (pre_f:pre_t) (post_f:post_t a)
//   (pre_g:pre_t) (post_g:post_t a)
//   (f:repr a pre_f post_f)
// : Tot _
// = stronger a (fun h -> pre_f h /\ pre_g h) (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1) pre_f post_f f

// let conjunction_is_stronger_g (a:Type)
//   (pre_f:pre_t) (post_f:post_t a)
//   (pre_g:pre_t) (post_g:post_t a)
//   (f:repr a pre_g post_g)
// : Tot _
// = stronger a (fun h -> pre_f h /\ pre_g h) (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1) pre_g post_g f

/// Actions

/// We define read action with the effect, but write will be defined via reflect later

let read (a:Type0) (r:ref a)
: repr a (fun _ -> True) (fun h0 x h1 -> h0 == h1 /\ x == sel h0 r)
= fun _ -> read r 

reifiable reflectable
layered_effect {
  HoareST : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else;

       read = read
}

let mread = HoareST?.read

let mwrite (a:Type0) (r:ref a) (x:a)
: HoareST unit
  (fun _ -> True)
  (fun h0 _ h1 ->
    sel h1 r == x /\
    modifies (Set.singleton (addr_of r)) h0 h1 /\
    equal_dom h0 h1)
= HoareST?.reflect (fun _ -> write r x)

assume val wp_monotonic_pure (_:unit)
  : Lemma
    (forall (a:Type) (wp:pure_wp a).
       (forall (p q:pure_post a).
          (forall (x:a). p x ==> q x) ==>
          (wp p ==> wp q)))

/// lift from PURE

let lift_pure_hoarest (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a
  (fun _ -> wp (fun _ -> True))
  (fun h0 r h1 -> ~ (wp (fun x -> x =!= r \/ h0 =!= h1)))
= wp_monotonic_pure ();
  fun _ ->
  f ()

sub_effect PURE ~> HoareST = lift_pure_hoarest
