module FStar.HST
open FStar.HyperStack
module HH = FStar.HyperHeap

let st_pre = st_pre_h mem
let st_post (a:Type) = st_post_h mem a
let st_wp (a:Type) = st_wp_h mem a

new_effect STATE = STATE_h mem

effect State (a:Type) (wp:st_wp a) =
       STATE a wp

effect ST (a:Type) (pre:st_pre) (post: (mem -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. pre h /\ post h a h1 ==> p a h1)) (* WP *)
  
effect STL (a:Type) (pre:st_pre) (post: (mem -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:mem) -> pre h /\ (forall a h1. (post h a h1 /\ equal_domains h h1) ==> p a h1)) (* WP *)

effect Stl (a:Type) = STL a (fun h -> True) (fun h0 r h1 -> True)

effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)

(* Effect requiring that the top frame is fresh *)
effect STF (a:Type) (pre:st_pre) (post: (mem -> Tot (st_post a))) =
       ST a pre (fun m0 x m1 -> post m0 x m1 /\ fresh_frame m0 m1)

sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:mem) -> wp (fun a -> p a h)

// JK: old located references
(* let ref (t:Type) : Type0 = stacked t *)

// JK: pushes a new emtpy frame on the stack
assume val push_frame: unit -> ST unit
  (requires (fun m -> True))
  (ensures (fun (m0:mem) _ (m1:mem) -> fresh_frame m0 m1))

// JK: removes old frame from the stack
assume val pop_frame: unit -> ST unit
  (requires (fun m -> poppable m))
  (ensures (fun (m0:mem) _ (m1:mem) -> poppable m0 /\ m1=pop m0 /\ popped m0 m1))

(* val call: #a:Type -> #b:Type -> #pre:st_pre -> #post:(t -> Tot (st_post t)) -> $(f:a -> STF b (requires (fun h -> pre h)) (fun h0 x h1 -> post h0 b h1)) -> ST b *)
(*   (requires (fun h -> (forall h'. fresh_frame h h' ==> pre h'))) *)
(*   (ensures (fun h0 x h1 -> stack h1 = stack h0)) *)
  
// JK: allocates on the top-most stack frame
assume val salloc: #a:Type -> init:a -> ST (stackref a)
  (requires (fun m -> True))
  (ensures (fun m0 s m1 -> 
      Map.domain m0.h = Map.domain m1.h
    /\ m0.tip = m1.tip
    /\ s.id   = m1.tip
    /\ HH.fresh_rref s.ref m0.h m1.h            //it's a fresh reference in the top frame
    /\ m1=HyperStack.upd m0 s init))           //and it's been initialized

// JK: assigns, provided that the reference is good
assume val op_Colon_Equals: #a:Type -> r:stackref a -> v:a -> STL unit
  (requires (fun m -> contains m r))
  (ensures (fun m0 _ m1 -> contains m0 r /\ m1 = HyperStack.upd m0 r v))

// JK: dereferences, provided that the reference is good
assume val op_Bang: #a:Type -> r:stackref a -> STL a
  (requires (fun m -> HH.includes r.id m.tip))
  (ensures (fun s0 v s1 -> s1=s0 /\ v=HyperStack.sel s0 r))

module G = FStar.Ghost

// JK: Returns the current stack of heaps --- it should be erased
assume val get: unit -> ST mem
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

// JK: Proper function, returning an erased stack of heaps 
// YES, this is the proper one
assume val eget: unit -> ST (G.erased mem)
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=G.reveal x /\ m1=m0))

//We don't have recall since regions and refs can be deallocated
(* assume val recall: #a:Type -> r:ref a -> ST unit *)
(*   (requires (fun m -> True)) *)
(*   (ensures (fun m0 _ m1 -> m0=m1 /\ contains m1 r)) *)

(* assume val recall_region: i:rid -> ST unit *)
(*   (requires (fun m -> True)) *)
(*   (ensures (fun m0 _ m1 -> m0=m1 /\ contains_frame m1 i)) *)

(* Tests *)
val test_do_nothing: int -> STL int
  (requires (fun h -> True))
  (ensures (fun h _ h1 -> True))
let test_do_nothing x = 
  push_frame();
  pop_frame ();
  x

val test_do_something: s:stackref int -> STL int
  (requires (fun h -> contains h s))
  (ensures (fun h r h1 -> contains h s /\ r = sel h s))
let test_do_something x = 
  push_frame();
  let res = !x in
  pop_frame ();
  res

val test_do_something_else: s:stackref int -> v:int -> STL unit
  (requires (fun h -> contains h s))
  (ensures (fun h r h1 -> contains h1 s /\ v = sel h1 s))
let test_do_something_else x v = 
  push_frame();
  x := v;
  pop_frame ()
  
val test_allocate: unit -> Stl unit
let test_allocate () =
  push_frame();
  let x = salloc 1 in
  x := 2;
  pop_frame ()

val test_nested_stl: unit -> Stl unit
let test_nested_stl () =
  let x = test_do_nothing 0 in ()

val test_nested_stl2: unit -> Stl unit
let test_nested_stl2 () =
  push_frame ();
  let x = test_do_nothing 0 in 
  pop_frame ()

val with_frame: #a:Type -> #pre:st_pre -> #post:(mem -> Tot (st_post a)) -> $f:(unit -> STL a pre post) 
	     -> STL a (fun s0 -> forall s1. fresh_frame s0 s1 ==> pre s1)
		     (fun s0 x s1 -> 
			exists s0' s1'. fresh_frame s0 s0' 
			         /\ poppable s0' 
				 /\ post s0' x s1'
				 /\ equal_domains s0' s1'
				 /\ s1 = pop s1')
let with_frame #a #pre #post f = 
  push_frame();
  let x = f() in
  pop_frame();
  x

let test_with_frame (x:stackref int) (v:int) 
  : STL unit (requires (fun m -> contains m x))
	     (ensures (fun m0 _ m1 -> modifies (Set.singleton x.id) m0 m1 /\ sel m1 x = v))
 = with_frame (fun _ -> x := v)


let as_requires (#a:Type) (wp:st_wp a) = wp (fun x s -> True)
let as_ensures (#a:Type) (wp:st_wp a) = fun s0 x s1 -> wp (fun y s1' -> y<>x \/ s1<>s1') s0
assume val as_stl: #a:Type -> #wp:st_wp a -> $f:(unit -> STATE a wp) -> 
	   Pure (unit -> STL a (as_requires wp)
			      (as_ensures wp))
	        (requires (forall s0 x s1. as_ensures wp s0 x s1 ==> equal_domains s0 s1))
 	        (ensures (fun x -> True))
