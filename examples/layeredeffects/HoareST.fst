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

/// Hoare-style ST effect as a layered effect, using SimpleHeap.
///
/// This is a simplified version without preorders or witness/recall.
/// Read operations require a `contains` precondition.

open SimpleHeap
open ExampleST

#set-options "--fuel 0 --ifuel 0"

type pre_t = heap -> prop
type post_t (a:Type) = heap -> a -> heap -> prop

type repr (a:Type) (pre:pre_t) (post:post_t a) : Type =
  unit -> ExST a (fun p h -> pre h /\ (forall (x:a) (h1:heap). post h x h1 ==> p x h1))

let return (a:Type) (x:a)
: repr a (fun _ -> True) (fun h0 r h1 -> r == x /\ h0 == h1)
= fun () -> x

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:a -> post_t b)
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) (post_g x)))
: repr b
  (fun h0 -> pre_f h0 /\ (forall (x:a) (h1:heap). post_f h0 x h1 ==> pre_g x h1))
  (fun h0 y h2 -> exists (x:a) (h1:heap). pre_f h0 /\ post_f h0 x h1 /\ post_g x h1 y h2)
= fun _ ->
  let x = f () in
  g x ()

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
  (p:bool)
  : Type
= repr a
  (fun h -> (p ==> pre_f h) /\ ((~ p) ==> pre_g h))
  (fun h0 r h1 -> (p ==> post_f h0 r h1) /\ ((~ p) ==> post_g h0 r h1))

reflectable
effect {
  HoareST (a:Type) (pre:pre_t) (post:post_t a)
  with {repr; return; bind; subcomp; if_then_else}
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

let get_heap ()
: HoareST heap
  (fun _ -> True)
  (fun h0 h h1 -> h0 == h1 /\ h == h1)
= HoareST?.reflect (fun _ -> get ())

/// lift from PURE

let lift_pure_hoarest (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a
  (fun _ -> wp (fun _ -> True))
  (fun h0 r h1 -> ~ (wp (fun x -> x =!= r \/ h0 =!= h1)))
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun _ -> f ()

sub_effect PURE ~> HoareST = lift_pure_hoarest


/// Array library

module Seq = FStar.Seq

type array (a:Type0) = ref (Seq.seq a)

let op_At_Bar (#a:Type0) (s1:array a) (s2:array a)
: HoareST (array a)
  (fun h -> h `contains` s1 /\ h `contains` s2)
  (fun h0 r h1 ->
    h0 `contains` s1 /\ h0 `contains` s2 /\
    h1 `contains` r /\
    sel h1 r == Seq.append (sel h0 s1) (sel h0 s2))
= let v1 = !s1 in
  let v2 = !s2 in
  alloc (Seq.append v1 v2)

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

/// Top-level effect

effect HoareSTT (a:Type) (post:post_t a) = HoareST a (fun _ -> True) post

#push-options "--warn_error -272" //Warning_TopLevelEffect
let main = FStar.IO.print_string "Hello!"
#pop-options
