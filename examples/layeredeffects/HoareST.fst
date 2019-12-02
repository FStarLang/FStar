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

module P = FStar.Preorder
module ST = FStar.ST

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
  (fun h0 y h2 -> exists (x:a) (h1:heap). pre_f h0 /\ post_f h0 x h1 /\ post_g x h1 y h2)
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
    (forall (h0 h1:heap) (x:a). (pre_g h0 /\ post_f h0 x h1) ==> post_g h0 x h1))
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

reifiable reflectable
layered_effect {
  HoareST : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else
}


/// Effect actions from FStar.ST

let recall (#a:Type) (#rel:P.preorder a) (r:mref a rel)
: HoareST unit
  (fun _ -> True)
  (fun h0 _ h1 ->
    h0 == h1 /\
    h1 `Heap.contains` r)
= HoareST?.reflect (fun _ -> recall r)

let alloc (#a:Type) (#rel:P.preorder a) (init:a)
: HoareST (mref a rel)
  (fun _ -> True)
  (fun h0 r h1 ->
    fresh r h0 h1 /\
    modifies Set.empty h0 h1 /\
    sel h1 r == init)
= HoareST?.reflect (fun _ -> alloc init)

let op_Bang (#a:Type) (#rel:P.preorder a) (r:mref a rel)
: HoareST a
  (fun _ -> True)
  (fun h0 x h1 ->
    h0 == h1 /\
    x == sel h1 r)
= HoareST?.reflect (fun _ -> read r)

let op_Colon_Equals (#a:Type) (#rel:P.preorder a) (r:mref a rel) (x:a)
: HoareST unit
  (fun h -> rel (sel h r) x)
  (fun h0 _ h1 ->
    modifies (Set.singleton (addr_of r)) h0 h1 /\
    equal_dom h0 h1 /\
    sel h1 r == x)
= HoareST?.reflect (fun _ -> write r x)

let get ()
: HoareST heap
  (fun _ -> True)
  (fun h0 h h1 -> h0 == h1 /\ h == h1)
= HoareST?.reflect get

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
  fun _ -> f ()

sub_effect PURE ~> HoareST = lift_pure_hoarest


/// Implementing the array library using the layered effect


module Seq = FStar.Seq


type array (a:Type0) = ref (Seq.seq a)

let op_At_Bar (#a:Type0) (s1:array a) (s2:array a)
: HoareST (array a)
  (fun _ -> True)
  (fun h0 r h1 ->
    sel h1 r == Seq.append (sel h0 s1) (sel h0 s2) /\
    modifies Set.empty h0 h1)
= let s1 = !s1 in
  let s2 = !s2 in
  alloc (Seq.append s1 s2)

let index (#a:Type0) (x:array a) (i:nat)
: HoareST a
  (fun h -> i < Seq.length (sel h x))
  (fun h0 v h1 ->
    i < Seq.length (sel h0 x) /\
    h0 == h1 /\
    v == Seq.index (sel h0 x) i)
= let s = !x in
  Seq.index s i

let upd (#a:Type0) (x:array a) (i:nat) (v:a)
: HoareST unit
  (fun h -> i < Seq.length (sel h x))
  (fun h0 _ h1 ->
    i < Seq.length (sel h0 x) /\
    modifies (Set.singleton (addr_of x)) h0 h1 /\
    sel h1 x == Seq.upd (sel h0 x) i v)
= let s = !x in
  let s = Seq.upd s i v in
  x := s

let length (#a:Type0) (x:array a)
: HoareST nat
  (fun _ -> True)
  (fun h0 y h1 -> y == Seq.length (sel h0 x) /\ h0 == h1)
= let s = !x in
  Seq.length s

let swap (#a:Type0) (x:array a) (i:nat) (j:nat{i <= j})
: HoareST unit
  (fun h -> j < Seq.length (sel h x))
  (fun h0 _ h1 ->
    j < Seq.length (sel h0 x) /\
    modifies (Set.singleton (addr_of x)) h0 h1 /\
    sel h1 x == Seq.swap (sel h0 x) i j)
= let v_i = index x i in
  let v_j = index x j in
  upd x j v_i;
  upd x i v_j

let rec copy_aux
  (#a:Type) (s:array a) (cpy:array a) (ctr:nat)
: HoareST unit
  (fun h ->
    addr_of s =!= addr_of cpy /\
    Seq.length (sel h cpy) == Seq.length (sel h s) /\
    ctr <= Seq.length (sel h cpy) /\
    (forall (i:nat). i < ctr ==> Seq.index (sel h s) i == Seq.index (sel h cpy) i))
  (fun h0 _ h1 ->
    modifies (only cpy) h0 h1 /\
    Seq.equal (sel h1 cpy) (sel h1 s))
= recall s; recall cpy;
  let len = length cpy in
  match len - ctr with
  | 0 -> ()
  | _ ->
    upd cpy ctr (index s ctr);
    copy_aux s cpy (ctr + 1)


let copy (#a:Type0) (s:array a)
: HoareST (array a)
  (fun h -> Seq.length (sel h s) > 0)
  (fun h0 r h1 ->
    modifies Set.empty h0 h1 /\
    r `unused_in` h0 /\
    contains h1 r /\
    sel h1 r == sel h0 s)
= recall s;
  let cpy = alloc (Seq.create (length s) (index s 0)) in
  copy_aux s cpy 0;
  cpy
