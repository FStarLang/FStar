module FStar.SST

open FStar.StackHeap
let modifies = StackHeap.modifies

let ref (t:Type) = stacked t // JK: old located references

let st_pre = st_pre_h t
let st_post (a:Type) = st_post_h t a
let st_wp (a:Type) = st_wp_h t a
new_effect STATE = STATE_h t
effect State (a:Type) (wp:st_wp a) =
       STATE a wp wp
effect ST (a:Type) (pre:st_pre) (post: (t -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. post h a h1 ==> p a h1)) (* WP *)
             (fun (p:st_post a) (h:t) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))          (* WLP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:t) -> wp (fun a -> p a h)

// JK: pushes a new emtpy frame on the stack
assume val push_frame: unit -> ST unit
  (requires (fun m -> True))
  (ensures (fun (m0:t) _ (m1:t) -> fresh_frame m0 m1))

// JK: removes old frame from the stack
assume val pop_frame: unit -> ST rid
  (requires (fun m -> poppable m))
  (ensures (fun (m0:t) _ (m1:t) -> popped_stack m0 m1))

// JK: allocates on the stack, only allowed in the topmost frame
assume val salloc: #a:Type -> init:a -> ST (ref a)
  (requires (fun m -> True))
  (ensures (fun m0 r m1 -> (frameOf r) = top_frame_id m0
    /\ frameOf r = top_frame_id m1
    /\ fresh_rref (refOf r) m0 m1 /\ m1=StackHeap.upd m0 r init))

// JK: assigns, provided that the reference is good
assume val op_Colon_Equals: #a:Type -> r:ref a -> v:a -> ST unit
  (requires (fun m -> contains m r))
  (ensures (fun m0 _ m1 -> m1 == StackHeap.upd m0 r v))

// JK: dereferences, provided that the reference is good
assume val op_Bang: #a:Type -> r:ref a -> ST a
  (requires (fun m -> contains m r))
  (ensures (fun s0 v s1 -> s1=s0 /\ v=StackHeap.sel s0 r))

// JK: Returns the current stack of heaps
assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

open FStar.Ghost 

// JK: Proper function, returning an erased stack of heaps
assume val eget: unit -> ST (erased t)
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=reveal x /\ m1=m0))

assume val recall: #a:Type -> r:ref a -> STATE unit
   (fun 'p m0 -> contains m0 r ==> 'p () m0)
   (fun 'p m0 -> contains m0 r ==> 'p () m0)

assume val recall_region: i:rid -> STATE unit
   (fun 'p m0 -> contains_frame m0 i ==> 'p () m0)
   (fun 'p m0 -> contains_frame m0 i ==> 'p () m0)
