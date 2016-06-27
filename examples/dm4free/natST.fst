module NatST

let st_pre = int -> Type0
let st_post (a:Type) = (a * int) -> Type0
let st_wp (a:Type) = int -> st_post a -> Type0
assume val r0: range
inline let st_return_wp (a:Type) (x:a) (n0:int) (post:st_post a) = 
  forall y. y=(x, n0) ==> post y
inline let st_bind_wp (r:range) (a:Type) (b:Type) (f:st_wp a) (g:(a -> Tot (st_wp b))) : st_wp b = 
    fun n0 post -> f n0 (fun x_n1 -> g (fst x_n1) (snd x_n1) post)

inline let st_if_then_else  (a:Type) (p:Type)
                            (wp_then:st_wp a) (wp_else:st_wp a)
                            (h0:int) (post:st_post a) =
     l_ITE p
        (wp_then h0 post)
	(wp_else h0 post)
inline let st_ite_wp        (a:Type)
                            (wp:st_wp a)
                            (h0:int) (post:st_post a) =
     forall (k:st_post a).
	 (forall (x:a) (h:int).{:pattern (guard_free (k (x, h)))} k (x, h) <==> post (x, h))
	 ==> wp h0 k
inline let st_stronger  (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
     (forall (p:st_post a) (h:int). wp1 h p ==> wp2 h p)

inline let st_close_wp      (a:Type) (b:Type)
                            (wp:(b -> GTot (st_wp a)))
                            (h:int) (p:st_post a) =
     (forall (b:b). wp b h p)
inline let st_assert_p      (a:Type) (p:Type)
                            (wp:st_wp a)
                            (h:int) (q:st_post a) =
     p /\ wp h q
inline let st_assume_p      (a:Type) (p:Type)
                            (wp:st_wp a)
                            (h:int) (q:st_post a) =
     p ==> wp h q
inline let st_null_wp       (a:Type)
                            (h:int) (p:st_post a) =
     (forall (x:a) (h:int). p (x,h))
inline let st_trivial       (a:Type)
                            (wp:st_wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
let st_repr (a:Type) (wp:st_wp a) =  
    n0:int -> PURE (a * int) (wp n0)
inline let st_bind (r:range) (a:Type) (b:Type) (wp0:st_wp a) (wp1:(a -> Tot (st_wp b)))
	    (f:st_repr a wp0)
	    (g:(x:a -> Tot (st_repr b (wp1 x)))) 
  : st_repr b (st_bind_wp r a b wp0 wp1)
  = fun n0 -> admit(); let x, n1 = f n0 in g x n1
let st_return (a:Type) (x:a) 
  : st_repr a (st_return_wp a x)
  = fun n0 -> (x, n0)

let st_get (u:unit) : st_repr int (fun n0 post -> post (n0, n0)) 
  = fun n0 -> n0, n0

let st_put (n:int) : st_repr unit (fun n0 post -> post ((), n))
  = fun x -> (), n

//#reset-options "--debug NatST --debug_level SMTEncoding"

reifiable reflectable new_effect {
  STATE : a:Type -> wp:st_wp a -> Effect
  with //repr is new; it's the reprentation of ST as a value type
       repr         = st_repr
       //bind_wp is exactly as it is currently
       //produced by the *-translation of bind above
     ; bind_wp      = st_bind_wp
       //bind is new, it is the elaboration of the bind above
     ; bind         = st_bind
      //return_wp is a renaming of the current return, it is the *-translation of the return above
     ; return_wp    = st_return_wp
      //return is new; it is the elaboration of the return above
     ; return       = st_return
     //the remaining are just as what we have now
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite_wp
     ; stronger     = st_stronger
     ; close_wp     = st_close_wp
     ; assert_p     = st_assert_p
     ; assume_p     = st_assume_p
     ; null_wp      = st_null_wp
     ; trivial      = st_trivial
  and effect_actions
    //these are new
      get  = st_get
    ; put  = st_put
}
inline let lift_pure_state (a:Type) (wp:pure_wp a) (n:int) (p:st_post a) = wp (fun a -> p (a, n))
sub_effect PURE ~> STATE = lift_pure_state

effect ST (a:Type) (pre:st_pre) (post: (int -> a -> int -> GTot Type0)) = 
       STATE a
             (fun n0 p -> pre n0 /\ (forall a n1. pre n0 /\ post n0 a n1 ==> p (a, n1)))

effect St (a:Type) =
       STATE a
             (fun n0 p -> forall x. p x)

////////////////////////////////////////////////////////////////////////////////

val incr : unit -> ST unit (requires (fun n -> True))
			  (ensures (fun n0 _ n1 -> n1 = n0 + 1))
let incr u = 
  let n = STATE.get () in
  STATE.put (n + 1)

reifiable val incr2 : unit -> St unit
let incr2 u =
    let n = STATE.get() in
    STATE.put (n + 1)

(* #set-options "--log_queries" *)
module Test
open NatST
let f (_:unit) : St unit =
    let n0 = STATE.get() in
    let _, n1 = reify (incr2 ()) n0 in
    assert (n1 = n0 + 1);
    STATE.put n1

val g : unit -> St int
let g u =
    let n0 = STATE.get () in
    let f : st_repr unit (fun n0 post -> forall x. snd x=n0+2 ==> post x) =
      fun n0 -> (), n0+2 in
    STATE.reflect f;
    let n1 = STATE.get () in
    assert (n0 + 2 = n1);
    n1

    
    


(* sub_effect PURE ~> STATE { *)
(*   lift_wp: #a:Type -> #wp:pure_wp a -> st_wp a = ... *)
(*   lift   : #a:Type -> #wp:pure_wp a -> f:PURE.repr a wp -> STATE.repr a (lift_star wp) = ... *)
(* }   *)

(* //////////////////////////////////////////////////////////////////////////////// *)
(* (\* let repr_STATE (a:Type) (wp:st_wp a) =  *\) *)
(* (\*   n0:nat -> PURE (a * nat) (fun post -> wp (fun a n -> post (a, n)) n0) *\) *)



(* new_effect STATE = STATE_h nat *)
(* let st_pre = st_pre_h nat *)
(* let st_post a = st_post_h nat a *)
(* let st_wp a = st_wp_h nat a *)
(* inline let lift_pure_state (a:Type) (wp:pure_wp a) (p:st_post a) (n:nat) = wp (fun a -> p a n) *)
(* sub_effect PURE ~> STATE = lift_pure_state *)

(* let reify_STATE (a:Type) = nat -> Tot (a * nat) *)
(* let reify_return (#a:Type) (x:a) : reify_STATE a = fun n -> (x, n) *)
(* let reify_bind (#a:Type) (#b:Type) (f:reify_STATE a) (g:(a -> Tot (reify_STATE b)) ) *)
(*   : reify_STATE b  *)
(*   = fun n0 -> let x, n1 = f n0 in g x n1 *)
(* let reify_get () : reify_STATE nat =  *)
(*   fun n -> n, n *)
(* let reify_put (m:nat) : reify_STATE unit =  *)
(*  fun _ -> (), m *)

(* assume val get : unit -> STATE nat (fun post n -> post n n) *)
(* assume val put : m:nat -> STATE unit (fun post n -> post () m) *)

(* val incr : unit -> STATE unit (fun post n -> post () (n + 1)) *)
(* let incr () =  *)
(*   let n = get () in  *)
(*   put (n + 1) *)

(* val incr2 : unit -> STATE unit (fun post n -> forall m. post () m) *)
(* let incr2 () =  *)
(*   let n = get () in  *)
(*   put (n + 1) *)






(* (\* let repr_STATE (a:Type) (wp:st_wp a) =  *\) *)
(* (\*   n0:nat -> PURE (a * nat) (fun post -> wp (fun a n -> post (a, n)) n0) *\) *)

(* (\* inline let lift_pure_state (a:Type) (wp:pure_wp a) (p:st_post a) (n:nat) = wp (fun a -> p a n) *\) *)
(* (\* sub_effect PURE ~> STATE = lift_pure_state *\) *)
(* (\* assume val r : range *\) *)

(* (\* val repr_bind: #a:Type -> #b:Type -> #wp1:st_wp a -> #wp2:(a -> GTot (st_wp b)) *\) *)
(* (\* 	     -> repr_STATE a wp1 *\) *)
(* (\* 	     -> (x:a -> Tot (repr_STATE b (wp2 x))) *\) *)
(* (\* 	     -> Tot (repr_STATE b (st_bind_wp nat r a b wp1 wp2)) *\) *)
(* (\* #reset-options "--log_queries"	      *\) *)
(* (\* let repr_bind #a #b #wp1 #wp2 f g =  *\) *)
(* (\*   fun n0 -> admit(); //the encoding to SMT isn't sufficiently smart to capture monotonicity *\) *)
(* (\*          let x, n1 = f n0 in *\) *)
(* (\*          g x n1 *\) *)



