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
module FStar.SST

open FStar.StackHeap2
module StackHeap = FStar.StackHeap2
let modifies = StackHeap.modifies

let ref (t:Type) : Type0 = stacked t // JK: old located references

let st_pre = st_pre_h t
let st_post (a:Type) = st_post_h t a
let st_wp (a:Type) = st_wp_h t a
new_effect STATE = STATE_h t
effect State (a:Type) (wp:st_wp a) =
       STATE a wp

effect ST (a:Type) (pre:st_pre) (post: (t -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. post h a h1 ==> p a h1)) (* WP *)

effect STL (a:Type) (pre:st_pre) (post: (t -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. (post h a h1 /\ domain_equality h h1) ==> p a h1)) (* WP *)

effect Stl (a:Type) = STL a (fun h -> True) (fun h0 r h1 -> True)

effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
(* Effect requiring a new frame pushed *)       
effect STF (a:Type) (pre:st_pre) (post: (t -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. post h a h1 ==> p a h1) 
	      /\ top_frame h = Heap.emp) (* WP *)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:t) -> wp (fun a -> p a h)

// JK: pushes a new emtpy frame on the stack
assume val push_frame: unit -> ST unit
  (requires (fun m -> True))
  (ensures (fun (m0:t) _ (m1:t) -> fresh_frame m0 m1))

// JK: removes old frame from the stack
assume val pop_frame: unit -> ST unit
  (requires (fun m -> poppable m))
  (ensures (fun (m0:t) _ (m1:t) -> popped_stack m0 m1))

(* val call: #a:Type -> #b:Type -> #pre:st_pre -> #post:(t -> Tot (st_post t)) -> $(f:a -> STF b (requires (fun h -> pre h)) (fun h0 x h1 -> post h0 b h1)) -> ST b *)
(*   (requires (fun h -> (forall h'. fresh_frame h h' ==> pre h'))) *)
(*   (ensures (fun h0 x h1 -> stack h1 = stack h0)) *)

// JK: allocates on the top-most stack frame
assume val salloc: #a:Type -> init:a -> ST (stacked a)
  (requires (fun m -> True))
  (ensures (fun m0 r m1 -> 
       frame_ids m0 = frame_ids m1
    /\ frameOf r = top_frame_id m1            //frame of the returned ref is the top one
    /\ fresh_rref (as_rref r) m0 m1           //it's a fresh reference in the top frame
    /\ m1=StackHeap.upd m0 r init))           //and it's been initialized

// JK: assigns, provided that the reference is good
assume val op_Colon_Equals: #a:Type -> r:ref a -> v:a -> ST unit
  (requires (fun m -> contains m r))
  (ensures (fun m0 _ m1 -> m1 = StackHeap.upd m0 r v))

// JK: dereferences, provided that the reference is good
assume val op_Bang: #a:Type -> r:ref a -> ST a
  (requires (fun m -> contains m r))
  (ensures (fun s0 v s1 -> s1=s0 /\ v=StackHeap.sel s0 r))

open FStar.Ghost 

// JK: Returns the current stack of heaps --- it should be erased
assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

// JK: Proper function, returning an erased stack of heaps 
// YES, this is the proper one
assume val eget: unit -> ST (erased t)
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=reveal x /\ m1=m0))

assume val recall: #a:Type -> r:ref a -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0=m1 /\ contains m1 r))

assume val recall_region: i:rid -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _ m1 -> m0=m1 /\ contains_frame m1 i))

let lemma_ref_ineq_1 (#a:Type) (#a':Type) (x:ref a) (y:ref a')
  : Lemma (requires (a <> a'))
	  (ensures (as_ref x =!= as_ref y))
	  [SMTPat (a <> a')]
  = stack_to_ref_lemma_3 x y

(* Tests *)
val test_do_nothing: int -> STL int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> True))
let test_do_nothing x = 
  push_frame();
  pop_frame ();
  x

val test_do_something: s:stacked int -> STL int
  (requires (fun h -> contains h s))
  (ensures (fun h r h1 -> contains h s /\ r = sel h s))
let test_do_something x = 
  push_frame();
  let res = !x in
  pop_frame ();
  res

val test_do_something_else: s:stacked int -> v:int -> STL unit
  (requires (fun h -> contains h s))
  (ensures (fun h r h1 -> contains h1 s /\ v = sel h1 s))
let test_do_something_else x v = 
  let h0 = get () in
  push_frame();
  let h = get () in
  x := v;
  let h' = get () in
  pop_frame ();
  let h1 = get () in
  cut (frame_ids h0 = frame_ids h1);
  cut (modifies_ref (frameOf x) !{as_ref x} h0 h1); (* Effect incompatibility *)
  () 

val test_allocate: unit -> Stl unit
let test_allocate () =
  push_frame();
  let h0 = get() in
  let x = salloc 1 in
  x := 2;
  let h1 = get() in
  cut (modifies_one (top_frame_id h0) h0 h1); (* JK: necessary trigger *)
  pop_frame ()

val test_nested_stl: unit -> Stl unit
let test_nested_stl () =
  let x = test_do_nothing 0 in ()

val test_nested_stl2: unit -> Stl unit
let test_nested_stl2 () =
  push_frame ();
  let h0 = get () in
  let x = test_do_nothing 0 in 
  let h1 = get () in
  cut (modifies_one (top_frame_id h0) h0 h1); (* JK: necessary trigger *)
  pop_frame ()
