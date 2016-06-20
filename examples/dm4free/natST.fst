module NatST

new_effect STATE = STATE_h nat
let st_pre = st_pre_h nat
let st_post a = st_post_h nat a
let st_wp a = st_wp_h nat a
inline let lift_pure_state (a:Type) (wp:pure_wp a) (p:st_post a) (n:nat) = wp (fun a -> p a n)
sub_effect PURE ~> STATE = lift_pure_state

let reify_STATE (a:Type) = nat -> Tot (a * nat)
let reify_return (#a:Type) (x:a) : reify_STATE a = fun n -> (x, n)
let reify_bind (#a:Type) (#b:Type) (f:reify_STATE a) (g:(a -> Tot (reify_STATE b)) )
  : reify_STATE b 
  = fun n0 -> let x, n1 = f n0 in g x n1
let reify_get () : reify_STATE nat = 
  fun n -> n, n
let reify_put (m:nat) : reify_STATE unit = 
 fun _ -> (), m

assume val get : unit -> STATE nat (fun post n -> post n n)
assume val put : m:nat -> STATE unit (fun post n -> post () m)

val incr : unit -> STATE unit (fun post n -> post () (n + 1))
let incr () = 
  let n = get () in 
  put (n + 1)

val incr2 : unit -> STATE unit (fun post n -> forall m. post () m)
let incr2 () = 
  let n = get () in 
  put (n + 1)






(* let repr_STATE (a:Type) (wp:st_wp a) =  *)
(*   n0:nat -> PURE (a * nat) (fun post -> wp (fun a n -> post (a, n)) n0) *)

(* inline let lift_pure_state (a:Type) (wp:pure_wp a) (p:st_post a) (n:nat) = wp (fun a -> p a n) *)
(* sub_effect PURE ~> STATE = lift_pure_state *)
(* assume val r : range *)

(* val repr_bind: #a:Type -> #b:Type -> #wp1:st_wp a -> #wp2:(a -> GTot (st_wp b)) *)
(* 	     -> repr_STATE a wp1 *)
(* 	     -> (x:a -> Tot (repr_STATE b (wp2 x))) *)
(* 	     -> Tot (repr_STATE b (st_bind_wp nat r a b wp1 wp2)) *)
(* #reset-options "--log_queries"	      *)
(* let repr_bind #a #b #wp1 #wp2 f g =  *)
(*   fun n0 -> admit(); //the encoding to SMT isn't sufficiently smart to capture monotonicity *)
(*          let x, n1 = f n0 in *)
(*          g x n1 *)



