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

module HoareSTPolyBind

open SimpleHeap
open ExampleST

/// ST effect implemented as a layered effect over ExST (STATE_h SimpleHeap.heap)
///
/// This module uses polymonadic binds to compose HoareST and PURE computations

#set-options "--fuel 0 --ifuel 0"

type pre_t = heap -> prop
type post_t (a:Type) = heap -> a -> heap -> prop

type repr (a:Type) (pre:pre_t) (post:post_t a) : Type =
  unit -> ExST a (fun p h -> pre h /\ (forall (x:a) (h1:heap). post h x h1 ==> p x h1))

let returnc (a:Type) (x:a)
: repr a (fun _ -> True) (fun h0 r h1 -> r == x /\ h0 == h1)
= fun _ -> x

let bind (a:Type) (b:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) (post_g x)))
: repr b
  (fun h0 -> pre_f h0 /\ (forall (x:a) (h1:heap). post_f h0 x h1 ==> pre_g x h1))
  (fun h0 y h2 -> exists (x:a) (h1:heap). pre_f h0 /\ post_f h0 x h1 /\ post_g x h1 y h2)
= fun _ ->
  let x = f () in
  g x ()

let subcomp (a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#pre_g:pre_t) (#post_g:post_t a)
  (f:repr a pre_f post_f)
: Pure (repr a pre_g post_g)
  (requires
    (forall (h:heap). pre_g h ==> pre_f h) /\
    (forall (h0 h1:heap) (x:a). (pre_g h0 /\ post_f h0 x h1) ==> post_g h0 x h1))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (#pre_g:pre_t) (#post_g:post_t a)
  (f:repr a pre_f post_f)
  (g:repr a pre_g post_g)
  (p:bool)
  : Type
= repr a
  (fun h -> (p ==> pre_f h) /\ ((~ p) ==> pre_g h))
  (fun h0 r h1 -> (p ==> post_f h0 r h1) /\ ((~ p) ==> post_g h0 r h1))

reflectable
effect {
  HoareST (a:Type) (pre:pre_t) (post:post_t a)
  with {repr;
        return = returnc;
        bind;
        subcomp;
        if_then_else}
}


/// Effect actions

let alloc (#a:Type0) (init:a)
: HoareST (ref a)
  (fun _ -> True)
  (fun h0 r h1 ->
    fresh r h0 h1 /\
    h1 `contains` r /\
    sel h1 r == init /\
    (forall (b:Type0) (r':ref b). h0 `contains` r' ==> h1 `contains` r' /\ sel h1 r' == sel h0 r'))
= HoareST?.reflect (fun _ -> st_alloc init)

let op_Bang (#a:Type0) (r:ref a)
: HoareST a
  (fun h -> h `contains` r)
  (fun h0 x h1 ->
    h0 `contains` r /\
    h0 == h1 /\
    x == sel h0 r)
= HoareST?.reflect (fun _ -> st_read r)

let op_Colon_Equals (#a:Type0) (r:ref a) (x:a)
: HoareST unit
  (fun h -> h `contains` r)
  (fun h0 _ h1 ->
    h0 `contains` r /\
    modifies (only r) h0 h1 /\
    equal_dom h0 h1 /\
    h1 `contains` r /\
    sel h1 r == x)
= HoareST?.reflect (fun _ -> st_write r x)

let get ()
: HoareST heap
  (fun _ -> True)
  (fun h0 h h1 -> h0 == h1 /\ h == h1)
= HoareST?.reflect (fun _ -> ExampleST.get ())


/// We don't define a traditional lift from PURE to HoareST
///
/// But rather we define two polymonadic binds


let bind_pure_hoarest (a:Type) (b:Type) (wp:pure_wp a) (req:a -> pre_t) (ens:a -> post_t b)
  (f:unit -> PURE a wp) (g:(x:a -> repr b (req x) (ens x)))
: repr b
  (fun h -> wp (fun x -> req x h))
  (fun h0 r h1 -> exists x. (~ (wp (fun r -> r =!= x))) /\ ens x h0 r h1)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun _ ->
  let x = f () in
  g x ()


polymonadic_bind (PURE, HoareST) |> HoareST = bind_pure_hoarest


let bind_hoarest_pure (a:Type u#a) (b:Type u#b) (req:pre_t) (ens:post_t a) (wp:a -> pure_wp b)
  (f:repr a req ens) (g:(x:a -> unit -> PURE b (wp x)))
: repr b
  (fun h -> req h /\ (forall x h1. ens h x h1 ==> (wp x) (fun _ -> True)))
  (fun h0 r h1 -> exists x. ens h0 x h1 /\ (~ ((wp x) (fun y -> y =!= r))))
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#a ();
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall u#b ();
  fun _ ->
  let x = f () in
  (g x) ()


polymonadic_bind (HoareST, PURE) |> HoareST = bind_hoarest_pure


let subcomp_pure_hoarest (a:Type) (wp:pure_wp a) (req:pre_t) (ens:post_t a)
  (f:unit -> PURE a wp)
: Pure (repr a req ens)
  (requires
    (forall h. req h ==>  wp (fun _ -> True)) /\
    (forall h0 r h1. (~ (wp (fun x -> x =!= r \/ h0 =!= h1))) ==>  ens h0 r h1))
  (ensures fun _ -> True)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun _ -> f ()

polymonadic_subcomp PURE <: HoareST = subcomp_pure_hoarest

let test_subcomp () : HoareST int (fun _ -> True) (fun _ r _ -> r == 0) = 0

assume val f_test_subcomp (n:int) : Pure int (n > 0) (fun r -> r > 0)

[@expect_failure]
let test_subcomp2 (n:int) : HoareST int (fun _ -> True) (fun _ _ _ -> True) = f_test_subcomp n

let test_subcomp3 (n:int) : HoareST int (fun _ -> n > 2) (fun _ _ _ -> True) = f_test_subcomp n


assume val f : x:int -> HoareST int (fun _ -> True) (fun _ r _ -> r == x + 1)

let test () : HoareST int (fun _ -> True) (fun _ r _ -> r == 1)
= f 0

open FStar.Monotonic.Pure

assume val g : int -> int -> PURE int (as_pure_wp (fun p -> forall x. p x))

let test2 () : HoareST int (fun _ -> True) (fun _ _ _ -> True)
= g 2 (f 0)


assume type t_int (x:int) : Type0
assume val dep_f (x:int) : HoareST (t_int x) (fun _ -> True) (fun _ _ _ -> True)
assume val pure_g (_:unit) : PURE int (as_pure_wp (fun p -> forall (x:int). x >= 2 ==> p x))

let test_dep_f () : HoareST (t_int (pure_g ())) (fun _ -> True) (fun _ _ _ -> True) =
  dep_f (pure_g ())


let test_dep_f2 () : HoareST (t_int (pure_g ())) (fun _ -> True) (fun _ _ _ -> True) =
  let x = pure_g () in
  dep_f x


module Seq = FStar.Seq

type array (a:Type0) = ref (Seq.seq a)

let op_At_Bar (#a:Type0) (s1:array a) (s2:array a)
: HoareST (array a)
  (fun h -> h `contains` s1 /\ h `contains` s2)
  (fun h0 r h1 ->
    h0 `contains` s1 /\ h0 `contains` s2 /\
    h1 `contains` r /\
    sel h1 r == Seq.append (sel h0 s1) (sel h0 s2))
= let s1 = !s1 in
  let s2 = !s2 in
  alloc (Seq.append s1 s2)

let index (#a:Type0) (x:array a) (i:nat)
: HoareST a
  (fun h -> h `contains` x /\ i < Seq.length (sel h x))
  (fun h0 v h1 ->
    h0 `contains` x /\
    i < Seq.length (sel h0 x) /\
    h0 == h1 /\
    v == Seq.index (sel h0 x) i)
= let s = !x in
  Seq.index s i

let upd (#a:Type0) (x:array a) (i:nat) (v:a)
: HoareST unit
  (fun h -> h `contains` x /\ i < Seq.length (sel h x))
  (fun h0 _ h1 ->
    h0 `contains` x /\
    i < Seq.length (sel h0 x) /\
    modifies (only x) h0 h1 /\
    h1 `contains` x /\
    sel h1 x == Seq.upd (sel h0 x) i v)
= let s = !x in
  let s = Seq.upd s i v in
  x := s

let length (#a:Type0) (x:array a)
: HoareST nat
  (fun h -> h `contains` x)
  (fun h0 y h1 ->
    h0 `contains` x /\
    y == Seq.length (sel h0 x) /\ h0 == h1)
= let s = !x in
  Seq.length s

let swap (#a:Type0) (x:array a) (i:nat) (j:nat{i <= j})
: HoareST unit
  (fun h -> h `contains` x /\ j < Seq.length (sel h x))
  (fun h0 _ h1 ->
    h0 `contains` x /\
    j < Seq.length (sel h0 x) /\
    modifies (only x) h0 h1 /\
    h1 `contains` x /\
    sel h1 x == Seq.swap (sel h0 x) i j)
= let v_i = index x i in
  let v_j = index x j in
  upd x j v_i;
  upd x i v_j


/// `match` with PURE code in one branch and HoareST in another doesn't work
/// since it requires lifts.
/// But we can define a return combinator and use it.

let return (#a:Type) (x:a)
: HoareST a (fun _ -> True) (fun h0 r h1 -> r == x /\ h0 == h1)
= HoareST?.reflect (returnc a x)


let test_lift (b:bool) : HoareST int (fun _ -> b == true) (fun h0 x h1 -> h0 == h1 /\ x == 0)
= match b with
  | true -> return 0
  | false -> return 1
