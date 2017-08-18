(* A state monad with local state built using FStar.DM4F.Heap.

   The very end of the file illustrates how recursion through the heap
   is forbidden because of the universe constraints.

   As such, in this model, storing stateful functions in the heap is
   forbidden. However, storing non-stateful functions, e.g,. Tot or
   Exception function in the heap is acceptable.
*)
module FStar.DM4F.Heap.ST
open FStar.DM4F.Heap

(* Temporary removing it since it does not work with extraction (see #1198) *)
(* open FStar.DM4F.ST *)

////////////////////////////////////////////////////////////////////////////////
// Instruct F* to build a new STATE effect from the elaborated effect STATE_h
////////////////////////////////////////////////////////////////////////////////

(* Temporary inlining the definition by hand since it does not work with extraction (see #1198) *)
(* reifiable reflectable total new_effect STATE = STATE_h heap *)

let st (a:Type) = heap -> M (a * heap)
let return_st (a:Type) (x:a) : st a = fun s0 -> x, s0
let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
= fun (s0:heap) -> let (x,heap) = f s0 in g x heap
let get () : st heap = fun s0 -> s0, s0
let put (x:heap) : st unit = fun _ -> (), x

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
  ; bind     = bind_st
  ; return   = return_st
  ; get      = get
  ; put      = put
}

type st_pre = STATE?.pre
type st_post a = heap -> a -> heap -> Type0
//ST is an abbreviation for STATE with pre- and post-conditions
//    aka requires and ensures clauses
effect ST (a:Type) (pre: st_pre) (post: st_post a) =
       STATE a (fun n0 p -> pre n0 /\ (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

//STNull is an abbreviation for stateful computations with trivial pre/post
effect STNull (a:Type) = ST a (fun h -> True) (fun _ _ _ -> True)

////////////////////////////////////////////////////////////////////////////////
//Next, given the primive global state actions STATE?.get and STATE?.put,
//we implement local state operations for allocating, reading and writing refs
////////////////////////////////////////////////////////////////////////////////

(* Allocation *)
 let alloc (#a:Type) (init:a)
  : ST (ref a)
       (requires (fun h -> True))
       (ensures (fun h0 r h1 ->
	 	 ~ (h0 `contains` r)          /\  //the ref r is fresh
		 h1 `contains_a_well_typed` r /\  //and is well-typed in h1
		 sel h1 r == init             /\  //initialized to init
		 modifies Set.empty h0 h1))  //and no existing ref is modified
    = let h0 = STATE?.get () in
      let r, h1 = alloc h0 init in
      STATE?.put h1;
      r

 let alloc_weak (#a:Type) (init:a)
  :ST (ref a) (requires (fun h0      -> True))
              (ensures  (fun h0 r h1 -> h1 `contains_a_well_typed` r /\
	                             (forall (a:Type) (r':ref a). h0 `contains_a_well_typed` r' ==> h1 `contains_a_well_typed` r')))
  = let h0 = STATE?.get () in
    let r, h1 = FStar.DM4F.Heap.alloc h0 init in
    STATE?.put h1;
    r

(* Reading, aka dereference *)
 let read (#a:Type) (r:ref a)
  : ST a
       (requires (fun h -> h `contains_a_well_typed` r))
       (ensures (fun h0 v h1 ->
		 h0 == h1 /\  //heap does not change
                 h1 `contains_a_well_typed` r /\
		 sel h1 r == v))                  //returns the contents of r
   = let h0 = STATE?.get () in
     sel_tot h0 r

 let (!) = read

 let read_weak (#a:Type) (r:ref a)
  : ST a (requires (fun h0      -> h0 `contains_a_well_typed` r))
         (ensures  (fun h0 v h1 -> forall (a:Type) (r:ref a). h0 `contains_a_well_typed` r ==> h1 `contains_a_well_typed` r))
   = let h0 = STATE?.get () in
     sel_tot h0 r

(* Writing, aka assignment *)
 let write (#a:Type) (r:ref a) (v:a)
    : ST unit
  	 (requires (fun h -> h `contains_a_well_typed` r))
	 (ensures (fun h0 _ h1 -> h0 `contains_a_well_typed` r /\
 		               h1 `contains_a_well_typed` r /\  //the heap remains well-typed
		               h1 == upd h0 r v))  //and is updated at location r only
    = let h0 = STATE?.get () in
      STATE?.put (upd_tot h0 r v)
 let op_Colon_Equals = write

 let write_weak (#a:Type) (r:ref a) (v:a)
    : ST unit (requires (fun h0      -> h0 `contains_a_well_typed` r))
              (ensures  (fun h0 v h1 -> forall (a:Type) (r:ref a). h0 `contains_a_well_typed` r ==> h1 `contains_a_well_typed` r))
  = let h0 = STATE?.get () in
    STATE?.put (upd_tot h0 r v)

////////////////////////////////////////////////////////////////////////////////
//A simple example using the local state operations
////////////////////////////////////////////////////////////////////////////////
let incr (r:ref int)
    :  ST unit
	  (requires (fun h -> h `contains_a_well_typed` r))
	  (ensures (fun h0 s h1 -> h0 `contains_a_well_typed` r /\
			        modifies (Set.singleton (addr_of r)) h0 h1 /\
			        sel h1 r = sel h0 r + 1))
    = r := !r + 1

 let incr' (r:ref int) :ST unit (fun h0      -> h0 `contains_a_well_typed` r)
                                       (fun h0 _ h1 -> h1 `contains_a_well_typed` r)
  = write_weak r (read_weak r + 1)

let incr_increases (r:ref int) (h0:heap{h0 `contains_a_well_typed` r})
  = assert (let _, h1 = (reify (incr' r)) h0 in
            sel h1 r = sel h0 r + 1)

let copy_and_incr (r:ref int)
    :  ST (ref int)
	  (requires (fun h -> h `contains_a_well_typed` r))
	  (ensures (fun h0 s h1 -> h0 `contains_a_well_typed` r               /\
			        ~ (h0 `contains` s)                        /\
			        h1 `contains_a_well_typed` s               /\
			        modifies (Set.singleton (addr_of r)) h0 h1 /\
			        sel h1 r = sel h0 r + 1                    /\
			        sel h1 s = sel h0 r))
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
	 (ensures (fun h0 s h1 -> h0 `contains_a_well_typed` r               /\
			       ~ (h0 `contains` s)                        /\
			       h1 `contains_a_well_typed` s               /\
			       modifies (Set.singleton (addr_of r)) h0 h1 /\
			       (forall y. sel h1 s y = sel h0 r + y)))
    = let x = !r in
      let s = alloc (fun y -> x + y) in
      s

////////////////////////////////////////////////////////////////////////////////
//Recursive, stateful functions are proven terminating using well-founded orders
////////////////////////////////////////////////////////////////////////////////
val zero: x:ref nat -> ghost_heap:heap{ghost_heap `contains_a_well_typed` x} -> ST unit
  (requires (fun h -> h == ghost_heap))
  (ensures (fun h0 _ h1 -> h0 `contains_a_well_typed` x               /\
 		        modifies (Set.singleton (addr_of x)) h0 h1 /\
		        sel h1 x = 0))
  (decreases (sel ghost_heap x))
let rec zero x ghost_heap =
  let cur = !x in //see #881
  if cur = 0
  then ()
  else (x := cur - 1;
        let h = STATE?.get () in //see #881
        zero x h)

let refine_st (#a:Type)
              (#b:Type)
              (#pre : a -> Tot STATE?.pre)
              (#post : a -> Tot (heap -> b -> heap -> Tot Type0))
              ($f :(x:a -> ST b (pre x) (post x)))
              (x:a)
  : ST b (pre x) (fun h0 z h1 -> pre x h0 /\
                              reify (f x) h0 == (z, h1) /\
                              post x h0 z h1)
  = let g (h0:heap)
      : Pure (b * heap)
             (pre x h0)
             (fun (z,h1) -> pre x h0 /\
                       reify (f x) h0 == (z, h1) /\
                       post x h0 z h1)
      = reify (f x) h0
    in
    STATE?.reflect g

////////////////////////////////////////////////////////////////////////////////
//An unsafe higher-order example, rightly rejected by an universe inconsistency
//Uncomment the last two lines below to see the following error message:
//   .\FStar.DM4F.Heap.ST.fst(169,29-169,50) : Error
//   Expected expression of type "Type(0)";
//   got expression "(uu___:Prims.int -> STNull Prims.int)" of type "Type((S 0))"
////////////////////////////////////////////////////////////////////////////////
(* #set-options "--print_universes" *)
(* let bad (r:ref int) = alloc #(unit -> STNull unit) (fun () -> incr r) *)


////////////////////////////////////////////////////////////////////////////////
//
//  Using reification we can run an arbitrary state computation starting
//  from an empty heap. At compilation time, this combinator ought to be
//  treated specially and [runST e] should be compiled to [e ()]. This
//  operation is semantically valid since the operational semantic of ST
//  is an abstraction over the semantic of the heap after compilation.
//
////////////////////////////////////////////////////////////////////////////////
abstract
val runST :
  (#a:Type) ->
  (#post:(heap -> a -> heap -> Type0)) ->
  (unit -> ST a (requires (fun h -> True)) (ensures post)) ->
  Pure a
    (requires True)
    (ensures (fun x -> exists h0 h1. post h0 x h1))
abstract
let runST #a #post s = fst (reify (s ()) FStar.DM4F.Heap.emp)


////////////////////////////////////////////////////////////////////////////////
//
//
//
//
////////////////////////////////////////////////////////////////////////////////

(* Seem to need monotonicity of the wp... *)
(* val ghost_reify : a:Type -> wp:(STATE?.wp a) -> (unit -> STATE a wp) -> Tot (STATE?.repr a wp) *)
(* let ghost_reify a wp f = fun s0 -> reify (f ()) s0 *)

(* Bogus error:
./FStar.DM4F.Heap.ST.fst(157,17-157,18) : (Error) Expected expression of type "(STATE_repr<n158855> a wp)";
got expression "a" of type "Type(n158855)" *)

(* This typechecks but there does not seem to be anyway to force it into ghost *)
private
let ghost_reify (#a:Type) (#wp:STATE?.wp a) (f:unit -> STATE a wp) = reify (f ())


(* To be investigated : the 2 folowing definitions typecheck generating an error from z3 *)
(* FStar.DM4F.Heap.ST: Unexpected output from Z3: (error "line 72169 column 7: named expression already defined") *)
let normalize_reify_incr_test0 (h0 : heap) (r:(ref int){h0 `contains_a_well_typed` r}) =
  assert (snd (normalize_term (reify (write r 42) h0)) == upd h0 r 42)

let normalize_reify_incr_test1 (h0:heap) (r:(ref int){h0 `contains_a_well_typed` r}) =
  assert (snd (normalize_term (reify (incr' r) h0)) == upd h0 r (sel h0 r + 1))


let reify_incr_test0 (r:ref int) (h0:heap)
  : Lemma
    (requires (h0 `contains_a_well_typed` r))
    (ensures (h0 `contains_a_well_typed` r ==>
               sel (snd (reify (incr' r) h0)) r == sel h0 r + 1))
= ()

let reify_incr_test1 (_:unit) : STNull unit =
  let r = alloc 42 in
  let i = !r in
  let h0 = STATE?.get() in
  refine_st incr' r;
  let h1 = STATE?.get() in
  assert(reify (incr' r) h0 == ((), h1));
  assert(h1 `contains_a_well_typed` r);
  let j = !r in
  ()
