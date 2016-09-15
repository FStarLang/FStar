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

reifiable reflectable new_effect_for_free {
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

effect ST (a:Type) (pre: STATE.pre) (post: heap -> a -> heap -> Type0) =
       STATE a (fun n0 p -> pre n0 /\ (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

val alloc : #a:Type0 -> init:a -> ST (ref a)
  	 (requires (fun h -> True))
	 (ensures (fun h0 r h1 ->
	 	     h1 `contains_a_well_typed` r
		  /\ ~ (h0 `contains` r)
		  /\ sel h1 r == init
		  /\ modifies Set.empty h0 h1))
let alloc #a init =
   let h0 = STATE.get () in
   let r, h1 = alloc h0 init in
   STATE.put h1;
   r

val read : #a:Type0 -> r:ref a -> ST a
  	 (requires (fun h -> h `contains_a_well_typed` r))
	 (ensures (fun h0 v h1 ->
		     h0 == h1
           	  /\  h1 `contains_a_well_typed` r
		  /\  sel h1 r == v))
let read #a r =
   let h0 = STATE.get () in
   sel h0 r
let (!) = read

val write : #a:Type0 -> r:ref a -> v:a -> ST unit
  	 (requires (fun h -> h `contains_a_well_typed` r))
	 (ensures (fun h0 _ h1 ->
           	     h0 `contains_a_well_typed` r
 		  /\  h1 `contains_a_well_typed` r
		  /\  h1 == upd h0 r v))
let write #a r v =
   let h0 = STATE.get () in
   STATE.put (upd h0 r v)
let op_Colon_Equals = write

effect STNull (a:Type) = ST a (fun h -> True) (fun _ _ _ -> True)

(* Uncomment the last two lines to see the following error message:
   .\FStar.DM4F.Heap.ST.fst(84,26-84,47) : Error
   Expected expression of type "Type(0)";
   got expression "(uu___:Prims.unit -> STNull (Prims.unit))" of type "Type((S 0))"
#set-options "--print_universes"
let bad (x:unit) = alloc #(unit -> STNull unit) (fun () -> ())
*) 
