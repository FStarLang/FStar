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
module Test.HyperStack

open FStar.Preorder
open FStar.HyperStack
open FStar.HyperStack.ST

module HS = FStar.HyperStack

let test0 (m:mem) (r:rid{r `is_above` HS.get_tip m}) = assert (r `is_in` HS.get_hmap m)

let test1 (m:mem) (r:rid{r `is_above` HS.get_tip m}) = assert (r = root \/ is_stack_region r)

let test2 (m:mem) (r:sid{HS.get_tip m `is_above` r /\ HS.get_tip m <> r}) = assert (~ (r `is_in` HS.get_hmap m))

let dc_elim (m:mem) (s:rid{s `is_in` HS.get_hmap m /\ s <> root}) (r:rid)
  : Lemma ((s `is_above` r /\ r `is_in` HS.get_hmap m) ==> is_stack_region s = is_stack_region r)
  = ()

let test3 (m:mem) (r:rid{r <> root /\ is_eternal_region r /\ HS.get_tip m `is_above` r /\ is_stack_region (HS.get_tip m)})
  : Lemma (~ (r `is_in` HS.get_hmap m))
  = root_has_color_zero ()

let test4 (m:mem) (r:rid{r <> root /\ is_eternal_region r /\ r `is_above` HS.get_tip m /\ is_stack_region (HS.get_tip m)})
  : Lemma (~ (r `is_in` HS.get_hmap m))
  = ()

let stronger_fresh_region_was_redundant (i:rid) (m0 m1:mem)  //AR: because of map_invariant
  :Tot unit
  = let stronger_fresh_region (i:rid) (m0 m1:mem) =
      (forall j. includes i j ==> not (j `is_in` HS.get_hmap m0)) /\
      i `is_in` HS.get_hmap m1
    in
    assert (fresh_region i m0 m1 ==> stronger_fresh_region i m0 m1)

let test5 (a:Type0) (b:Type0) (rel_a:preorder a) (rel_b:preorder b) (rel_n:preorder nat)
                              (x:mreference a rel_a) (x':mreference a rel_a)
                              (y:mreference b rel_b) (z:mreference nat rel_n)
                              (h0:mem) (h1:mem) =
  assume (h0 `contains` x);
  assume (h0 `contains` x');
  assume (as_addr x <> as_addr x');
  assume (frameOf x == frameOf x');
  assume (frameOf x <> frameOf y);
  assume (frameOf x <> frameOf z);
  assume (mods [Ref x; Ref y; Ref z] h0 h1);
  assume (modifies_ref (frameOf x) (Set.singleton (as_addr x)) h0 h1);
  assert (modifies (Set.union (Set.singleton (frameOf x))
                              (Set.union (Set.singleton (frameOf y))
                                         (Set.singleton (frameOf z)))) h0 h1);
  ()

(* Tests *)
val test_do_nothing: int -> Stack int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> True))
let test_do_nothing x =
  push_frame();
  pop_frame ();
  x

val test_do_something: #rel:preorder int -> s:mstackref int rel -> Stack int
  (requires (fun h     -> contains h s))
  (ensures (fun h r h1 -> contains h s /\ r = sel h s))
let test_do_something #rel s =
  push_frame();
  let res = !s in
  pop_frame ();
  res

val test_do_something_else: #rel:preorder int -> s:mstackref int rel -> v:int -> Stack unit
  (requires (fun h     -> contains h s /\ rel (HS.sel h s) v))
  (ensures (fun h r h1 -> contains h1 s /\ v = sel h1 s))
let test_do_something_else #rel s v =
  push_frame();
  s := v;
  pop_frame ()

val test_allocate: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_allocate () =
  push_frame();
  let x :stackref int = salloc 1 in
  x := 2;
  pop_frame ()

val test_nested_stl: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_nested_stl () =
  let x = test_do_nothing 0 in ()

val test_nested_stl2: unit -> Stack unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test_nested_stl2 () =
  push_frame ();
  let x = test_do_nothing 0 in
  pop_frame ()

(* Testing mix of Heap and Stack code *)
val test_stack: int -> Stack int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> modifies Set.empty h h1))
let test_stack x =
  push_frame();
  let s :stackref int = salloc x in
  s := (1 + x);
  pop_frame ();
  x

val test_stack_with_long_lived: #rel:preorder int -> s:mreference int rel -> Stack unit
  (requires (fun h -> contains h s /\ rel (HS.sel h s) (HS.sel h s + 1)))
  (ensures  (fun h0 _ h1 -> contains h1 s /\ sel h1 s = (sel h0 s) + 1 /\
                         modifies (Set.singleton (frameOf s)) h0 h1))
#set-options "--z3rlimit 10"
let test_stack_with_long_lived #rel s =
  push_frame();
  let _ = test_stack !s in
  s := !s + 1;
  pop_frame()
#reset-options

val test_heap_code_with_stack_calls: unit -> Heap unit
  (requires (fun h -> heap_only h))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton (HS.get_tip h0)) h0 h1 ))
let test_heap_code_with_stack_calls () =
  let h = get () in
  // How is the following not known ?
  HS.root_has_color_zero ();
  let s :ref int = ralloc (HS.get_tip h) 0 in
  test_stack_with_long_lived s;
  s := 1;
  ()

val test_heap_code_with_stack_calls_and_regions: unit -> Heap unit
  (requires (fun h -> heap_only h))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton (HS.get_tip h0)) h0 h1 ))
let test_heap_code_with_stack_calls_and_regions () =
  let h = get() in
  let color = 0 in
  HS.root_has_color_zero ();
  let new_region = new_colored_region (HS.get_tip h) color in
  let s :ref int = ralloc new_region 1 in
  test_stack_with_long_lived s; // STStack call
  test_heap_code_with_stack_calls (); // STHeap call
  ()

val test_lax_code_with_stack_calls_and_regions: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton HS.root) h0 h1 ))
let test_lax_code_with_stack_calls_and_regions () =
  push_frame();
  let color = 0 in
  HS.root_has_color_zero ();
  let new_region = new_colored_region HS.root color in
  let s :ref int = ralloc new_region 1 in
  test_stack_with_long_lived s; // Stack call
  pop_frame()

val test_lax_code_with_stack_calls_and_regions_2: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> modifies_transitively (Set.singleton HS.root) h0 h1 ))
#set-options "--z3rlimit 10"
let test_lax_code_with_stack_calls_and_regions_2 () =
  push_frame();
  let color = 0 in
  HS.root_has_color_zero ();
  let new_region = new_colored_region HS.root color in
  let s :ref int = ralloc new_region 1 in
  test_stack_with_long_lived s; // Stack call
  test_lax_code_with_stack_calls_and_regions (); // ST call
  pop_frame()
#reset-options

val test_to_be_stack_inlined: unit -> StackInline (reference int)
  (requires (fun h -> is_stack_region (HS.get_tip h)))
  (ensures  (fun h0 r h1 -> ~(contains h0 r) /\ contains h1 r /\ sel h1 r = 2))
let test_to_be_stack_inlined () =
  let r :stackref int = salloc 0 in
  r := 2;
  r

val test_stack_function_with_inline: unit -> Stack int
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let test_stack_function_with_inline () =
  push_frame();
  let x = test_to_be_stack_inlined () in
  let y = !x + !x in
  pop_frame();
  y

val test_st_function_with_inline: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let test_st_function_with_inline () =
  push_frame();
  let x = test_to_be_stack_inlined () in
  let y = !x + !x in
  pop_frame();
  ()

val test_to_be_inlined: unit -> Inline (reference int * reference int)
  (requires (fun h -> is_stack_region (HS.get_tip h)))
  (ensures  (fun h0 r h1 -> True))
let test_to_be_inlined () =
  let r :stackref int = salloc 0 in
  HS.root_has_color_zero ();
  let region = new_region HS.root in
  let r' = ralloc region 1 in
  r := 2;
  r' := 3;
  r,r'

val test_st_function_with_inline_2: unit -> ST unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let test_st_function_with_inline_2 () =
  push_frame();
  let x = test_to_be_stack_inlined () in
  let r, r' = test_to_be_inlined () in
  pop_frame();
  ()

val with_frame: #a:Type -> #pre:st_pre -> #post:(s0:mem -> Tot (st_post' a (pre s0))) -> $f:(unit -> Stack a pre post)
	     -> Stack a (fun s0 -> forall (s1:mem). fresh_frame s0 s1 ==> pre s1)
		     (fun s0 x s1 ->
			exists (s0' s1':mem). fresh_frame s0 s0'
			         /\ poppable s0'
				 /\ post s0' x s1'
				 /\ equal_domains s0' s1'
				 /\ s1 == pop s1')
let with_frame #a #pre #post f =
  push_frame();
  let x = f() in
  pop_frame();
  x

let test_with_frame (x:stackref int) (v:int)
  : Stack unit (requires (fun m -> contains m x))
	       (ensures (fun m0 _ m1 -> modifies (Set.singleton (frameOf x)) m0 m1 /\ sel m1 x = v))
 = admit () //with_frame (fun _ -> x := v)


let as_requires (#a:Type) (wp:st_wp a) = wp (fun x s -> True)
let as_ensures (#a:Type) (wp:st_wp a) = fun s0 x s1 -> wp (fun y s1' -> y=!=x \/ s1=!=s1') s0

assume val as_stack: #a:Type -> #wp:st_wp a -> $f:(unit -> STATE a wp) ->
	   Pure (unit -> Stack a (as_requires wp)
			      (as_ensures wp))
	        (requires (forall s0 x s1. as_ensures wp s0 x s1 ==> equal_domains s0 s1))
 	        (ensures (fun x -> True))

val mm_tests: unit -> Unsafe unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let mm_tests _ =
  let _ = push_frame () in

  let r1 :mmstackref int = salloc_mm 2 in

  //check that the heap contains the reference
  let m = get () in
  let h = HS.get_hmap m `Map.sel` (HS.get_tip m) in
  let _ = assert (Heap.contains h (as_ref r1)) in

  let _ = !r1 in

  let _ = sfree r1 in

  //this fails because the ref has been freed
  //let _ = !r1 in

  //check that the heap does not contain the reference
  let m = get () in
  let h = HS.get_hmap m `Map.sel` (HS.get_tip m) in
  let _ = assert (~ (Heap.contains h (as_ref r1))) in

  let r2 :mmstackref int = salloc_mm 2 in
  let _ = pop_frame () in

  //this fails because the reference is no longer live
  //let _ = sfree r2 in

  let id = new_region HS.root in

  let r3 :mmref int = ralloc_mm id 2 in
  let _ = !r3 in
  let _ = rfree r3 in

  //check that the heap does not contain the reference
  let m = get () in
  let h = HS.get_hmap m `Map.sel` id in
  let _ = assert (~ (Heap.contains h (as_ref r3))) in

  //this fails because the reference is no longer live
  //let _ = !r3 in

  //this fails because recall of mm refs is not allowed
  //let _ = recall r3 in
  ()

(*
 * set up: x and y are in different regions.
 *         x and z are in same region but have different addresses
 *         w is in a region different from x and y
 *         mods_test1 mods [x; y]
 *         we prove that z and w remain same, and usual modifies clauses
 *         we use `mods` to specify the mods_test1
 *)
assume val mods_test1 (a:Type0) (rel:preorder a) (x y z w:mref a rel)
  :ST unit (fun h0 -> True)
	   (fun h0 _ h1 -> mods [ Ref x; Ref y ] h0 h1)

let mods_test2 (a:Type0) (rel:preorder a) (x y z w:mref a rel)
  :ST unit (fun h0 -> frameOf x =!= frameOf y /\ 
                   frameOf z == frameOf x  /\
                   as_addr z =!= as_addr x /\
    	           frameOf w =!= frameOf x /\
	           frameOf w =!= frameOf y)
	   (fun h0 _ h1 -> sel h0 z == sel h1 z /\ sel h0 w == sel h1 w /\
	                modifies (Set.union (Set.singleton (frameOf x))
			                    (Set.singleton (frameOf y))) h0 h1 /\
			modifies_ref (frameOf x) (Set.singleton (as_addr x)) h0 h1 /\
			modifies_ref (frameOf y) (Set.singleton (as_addr y)) h0 h1)
  = recall x; recall y; recall z; recall w;
    mods_test1 a rel x y z w

let test_logical_operators_on_witnessed (p q:mem_predicate)
  = lemma_witnessed_and p q;
    assert (witnessed (fun s -> p s /\ q s) <==> (witnessed p /\ witnessed q));
    lemma_witnessed_or p q;
    assert ((witnessed p \/ witnessed q) ==> witnessed (fun s -> p s \/ q s));
    lemma_witnessed_nested p;
    assert (witnessed (fun _ -> witnessed p) <==> witnessed p)

open FStar.Monotonic.Seq

private let test_alloc (#a:Type0) (p:Seq.seq a -> Type) (r:rid) (init:Seq.seq a{p init})
               : ST unit (requires (fun _ -> witnessed (region_contains_pred r))) (ensures (fun _ _ _ -> True)) =
  let is = alloc_mref_iseq p r init in
  let h = get () in
  assert (i_sel h is == init)
