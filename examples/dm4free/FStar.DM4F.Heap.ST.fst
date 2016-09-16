(* A state monad with local state built using FStar.DM4F.Heap. 
   
   The very end of the file illustrates how recursion through the heap
   is forbidden because of the universe constraints.

   As such, in this model, storing stateful functions in the heap is
   forbidden. However, storing non-stateful functions, e.g,. Tot or
   Exception function in the heap is acceptable.
*)
module FStar.DM4F.Heap.ST
open FStar.DM4F.Heap

////////////////////////////////////////////////////////////////////////////////
// In the DM sub-language
////////////////////////////////////////////////////////////////////////////////
(* Define a state monad with the `heap` type as the state *)
let st (a: Type) =
  heap -> M (a * heap)

val return_st: a:Type -> x:a -> st a
let return_st a x = fun s -> x, s

val bind_st: a:Type -> b:Type -> f:st a -> g:(a -> st b) -> st b
let bind_st a b f g = fun s0 ->
  let tmp = f s0 in
  let x, s1 = tmp in
  g x s1

let get (_:unit): st heap =
  fun x -> x, x

let put (x: heap): st unit =
  fun _ -> (), x

////////////////////////////////////////////////////////////////////////////////
// Instruct F* to CPS and elaborate the terms above to build a new STATE effect
////////////////////////////////////////////////////////////////////////////////

reifiable reflectable total new_effect_for_free {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
  and effect_actions
       get      = get
     ; put      = put
}

inline let lift_pure_state (a:Type) (wp:pure_wp a) (h:heap) (p:STATE.post a) = wp (fun a -> p (a, h))
sub_effect PURE ~> STATE = lift_pure_state

//ST is an abbreviation for STATE with pre- and post-conditions
//    aka requires and ensures clauses
effect ST (a:Type) (pre: STATE.pre) (post: heap -> a -> heap -> Type0) =
       STATE a (fun n0 p -> pre n0 /\ (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

//STNull is an abbreviation for stateful computations with trivial pre/post
effect STNull (a:Type0) = ST a (fun h -> True) (fun _ _ _ -> True)

////////////////////////////////////////////////////////////////////////////////
//Next, given the primive global state actions STATE.get and STATE.put, 
//we implement local state operations for allocating, reading and writing refs
////////////////////////////////////////////////////////////////////////////////

(* Allocation *)
let alloc (#a:Type) (init:a)
    : ST (ref a)
  	 (requires (fun h -> True))
	 (ensures (fun h0 r h1 ->
	 	    ~ (h0 `contains` r)          //the ref r is fresh
		  /\ h1 `contains_a_well_typed` r //and is well-typed in h1
		  /\ sel h1 r == init             //initialized to init
		  /\ modifies Set.empty h0 h1))   //and no existing ref is modified
    = let h0 = STATE.get () in
      let r, h1 = alloc h0 init in
      STATE.put h1;
      r

(* Reading, aka dereference *)
let read (#a:Type) (r:ref a)
    : ST a
  	 (requires (fun h -> h `contains_a_well_typed` r))
	 (ensures (fun h0 v h1 ->
		     h0 == h1                         //heap does not change
           	  /\  h1 `contains_a_well_typed` r       
		  /\  sel h1 r == v))                  //returns the contents of r
   = let h0 = STATE.get () in
     sel h0 r
let (!) = read

(* Writing, aka assignment *)
let write (#a:Type) (r:ref a) (v:a)
    : ST unit
  	 (requires (fun h -> h `contains_a_well_typed` r))
	 (ensures (fun h0 _ h1 ->
           	     h0 `contains_a_well_typed` r
 		  /\  h1 `contains_a_well_typed` r     //the heap remains well-typed
		  /\  h1 == upd h0 r v))               //and is updated at location r only
    = let h0 = STATE.get () in
      STATE.put (upd h0 r v)
let op_Colon_Equals = write

////////////////////////////////////////////////////////////////////////////////
//A simple example using the local state operations
////////////////////////////////////////////////////////////////////////////////
let incr (r:ref int) 
    :  ST unit
	  (requires (fun h -> h `contains_a_well_typed` r))
	  (ensures (fun h0 s h1 -> 
			     h0 `contains_a_well_typed` r
			   /\ modifies (Set.singleton r) h0 h1
			   /\ sel h1 r = sel h0 r + 1))
    = r := !r + 1

let copy_and_incr (r:ref int) 
    :  ST (ref int)
	  (requires (fun h -> h `contains_a_well_typed` r))
	  (ensures (fun h0 s h1 -> 
			     h0 `contains_a_well_typed` r
			   /\ ~ (h0 `contains` s)
			   /\ h1 `contains_a_well_typed` s
			   /\ modifies (Set.singleton r) h0 h1
			   /\ sel h1 r = sel h0 r + 1
			   /\ sel h1 s = sel h0 r))
    = let s = alloc !r in
      incr r; 
      s
      
////////////////////////////////////////////////////////////////////////////////
//A safe higher-order example
//     Storing non-heap reading functions in the heap is fine
////////////////////////////////////////////////////////////////////////////////
let alloc_addition_and_incr (r:ref int)
    : ST (ref (int -> Tot int))
         (requires (fun h -> h `contains_a_well_typed` r))
	 (ensures (fun h0 s h1 -> 
			     h0 `contains_a_well_typed` r
			   /\ ~ (h0 `contains` s)
			   /\ h1 `contains_a_well_typed` s
			   /\ modifies (Set.singleton r) h0 h1
			   /\ (forall y. sel h1 s y = sel h0 r + y)))
    = let x = !r in
      let s = alloc (fun y -> x + y) in
      s

////////////////////////////////////////////////////////////////////////////////
//Recursive, stateful functions are proven terminating using well-founded orders
////////////////////////////////////////////////////////////////////////////////
val zero: x:ref nat -> ghost_heap:heap{ghost_heap `contains_a_well_typed` x} -> ST unit 
  (requires (fun h -> h==ghost_heap))
  (ensures (fun h0 _ h1 -> h0 `contains_a_well_typed` x
 		       /\ modifies (Set.singleton x) h0 h1
		       /\ sel h1 x = 0))
  (decreases (sel ghost_heap x))
let rec zero x ghost_heap = 
  if !x = 0 
  then ()
  else (x := !x - 1; 
        zero x (STATE.get()))

////////////////////////////////////////////////////////////////////////////////
//An unsafe higher-order example, rightly rejected by an universe inconsistency
//Uncomment the last two lines below to see the following error message:
//   .\FStar.DM4F.Heap.ST.fst(169,29-169,50) : Error
//   Expected expression of type "Type(0)";
//   got expression "(uu___:Prims.int -> STNull Prims.int)" of type "Type((S 0))"
////////////////////////////////////////////////////////////////////////////////
(* #set-options "--print_universes" *)
(* let bad (r:ref int) = alloc #(unit -> STNull unit) (fun () -> incr r) *)
