module IntST

let pre = int -> Type0
let post (a:Type) = (a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0
assume val r0: range
inline let return_wp (a:Type) (x:a) (n0:int) (post:post a) =
  forall y. y=(x, n0) ==> post y

//working around #517 by adding an explicit 'val'
inline val bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:wp a) -> (g:(a -> Tot (wp b))) -> Tot (wp b)
let bind_wp r a b f g =
    fun n0 post -> f n0 (fun x_n1 -> g (fst x_n1) (snd x_n1) post)

inline let if_then_else  (a:Type) (p:Type)
                            (wp_then:wp a) (wp_else:wp a)
                            (h0:int) (post:post a) =
     l_ITE p
        (wp_then h0 post)
        (wp_else h0 post)
inline let ite_wp        (a:Type)
                            (wp:wp a)
                            (h0:int) (q:post a) =
     forall (k:post a).
         (forall (x:a) (h:int).{:pattern (guard_free (k (x, h)))} k (x, h) <==> q (x, h))
         ==> wp h0 k
inline let stronger  (a:Type) (wp1:wp a) (wp2:wp a) =
     (forall (p:post a) (h:int). wp1 h p ==> wp2 h p)

inline let close_wp      (a:Type) (b:Type)
                            (wp:(b -> GTot (wp a)))
                            (h:int) (p:post a) =
     (forall (b:b). wp b h p)
inline let assert_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p /\ wp h q
inline let assume_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p ==> wp h q
inline let null_wp       (a:Type)
                            (h:int) (p:post a) =
     (forall (x:a) (h:int). p (x,h))
inline let trivial       (a:Type)
                            (wp:wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
let repr (a:Type) (wp:wp a) =
    n0:int -> PURE (a * int) (wp n0)

inline val bind: (a:Type) -> (b:Type) -> (wp0:wp a) -> (wp1:(a -> Tot (wp b)))
                 -> (f:repr a wp0)
                 -> (g:(x:a -> Tot (repr b (wp1 x))))
                 -> Tot (repr b (bind_wp r0 a b wp0 wp1))
let bind a b wp0 wp1 f g
  = fun n0 -> admit(); let (x,n1) = f n0 in g x n1
let return (a:Type) (x:a)
  : repr a (return_wp a x)
  = fun n0 -> (x, n0)

let get (u:unit) : repr int (fun n0 post -> post (n0, n0))
  = fun n0 -> n0, n0

let put (n:int) : repr unit (fun n0 post -> post ((), n))
  = fun x -> (), n

(* #reset-options "--debug NatST --debug_level SMTEncoding" *)

reifiable reflectable new_effect {
  STATE : a:Type -> wp:wp a -> Effect
  with //repr is new; it's the reprentation of ST as a value type
       repr         = repr
       //bind_wp is exactly as it is currently
       //produced by the *-translation of bind above
     ; bind_wp      = bind_wp
       //bind is new, it is the elaboration of the bind above
     ; bind         = bind
      //return_wp is a renaming of the current return, it is the *-translation of the return above
     ; return_wp    = return_wp
      //return is new; it is the elaboration of the return above
     ; return       = return
     //the remaining are just as what we have now
     ; if_then_else = if_then_else
     ; ite_wp       = ite_wp
     ; stronger     = stronger
     ; close_wp     = close_wp
     ; assert_p     = assert_p
     ; assume_p     = assume_p
     ; null_wp      = null_wp
     ; trivial      = trivial
  and effect_actions
    //these are new
      get  = get
    ; put  = put
}
inline let lift_pure_state (a:Type) (wp:pure_wp a) (n:int) (p:post a) = wp (fun a -> p (a, n))
sub_effect PURE ~> STATE = lift_pure_state

effect ST (a:Type) (pre:pre) (post: (int -> a -> int -> GTot Type0)) =
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

let f (_:unit) : St unit =
    let n0 = STATE.get() in
    let _, n1 = reify (incr2 ()) n0 in
    assert (n1 = n0 + 1);
    STATE.put n1

val g : unit -> St int
let g u =
    let n0 = STATE.get () in
    let f : repr unit (fun n0 post -> forall x. snd x=n0+2 ==> post x) =
      fun n0 -> (), n0+2 in
    STATE.reflect f;
    let n1 = STATE.get () in
    assert (n0 + 2 = n1);
    n1

let top =
  let _, one = reify (incr2 ()) 0 in
  FStar.IO.print_string ("incr2 returned: " ^ string_of_int one)

(* (\* sub_effect PURE ~> STATE { *\) *)
(* (\*   lift_wp: #a:Type -> #wp:pure_wp a -> wp a = ... *\) *)
(* (\*   lift   : #a:Type -> #wp:pure_wp a -> f:PURE.repr a wp -> STATE.repr a (lift_star wp) = ... *\) *)
(* (\* }   *\) *)

(* (\* //////////////////////////////////////////////////////////////////////////////// *\) *)
(* (\* (\\* let repr_STATE (a:Type) (wp:wp a) =  *\\) *\) *)
(* (\* (\\*   n0:nat -> PURE (a * nat) (fun post -> wp (fun a n -> post (a, n)) n0) *\\) *\) *)



(* (\* new_effect STATE = STATE_h nat *\) *)
(* (\* let pre = pre_h nat *\) *)
(* (\* let post a = poh nat a *\) *)
(* (\* let wp a = wp_h nat a *\) *)
(* (\* inline let lift_pure_state (a:Type) (wp:pure_wp a) (p:post a) (n:nat) = wp (fun a -> p a n) *\) *)
(* (\* sub_effect PURE ~> STATE = lift_pure_state *\) *)

(* (\* let reify_STATE (a:Type) = nat -> Tot (a * nat) *\) *)
(* (\* let reify_return (#a:Type) (x:a) : reify_STATE a = fun n -> (x, n) *\) *)
(* (\* let reify_bind (#a:Type) (#b:Type) (f:reify_STATE a) (g:(a -> Tot (reify_STATE b)) ) *\) *)
(* (\*   : reify_STATE b  *\) *)
(* (\*   = fun n0 -> let x, n1 = f n0 in g x n1 *\) *)
(* (\* let reify_get () : reify_STATE nat =  *\) *)
(* (\*   fun n -> n, n *\) *)
(* (\* let reify_put (m:nat) : reify_STATE unit =  *\) *)
(* (\*  fun _ -> (), m *\) *)

(* (\* assume val get : unit -> STATE nat (fun post n -> post n n) *\) *)
(* (\* assume val put : m:nat -> STATE unit (fun post n -> post () m) *\) *)

(* (\* val incr : unit -> STATE unit (fun post n -> post () (n + 1)) *\) *)
(* (\* let incr () =  *\) *)
(* (\*   let n = get () in  *\) *)
(* (\*   put (n + 1) *\) *)

(* (\* val incr2 : unit -> STATE unit (fun post n -> forall m. post () m) *\) *)
(* (\* let incr2 () =  *\) *)
(* (\*   let n = get () in  *\) *)
(* (\*   put (n + 1) *\) *)






(* (\* (\\* let repr_STATE (a:Type) (wp:wp a) =  *\\) *\) *)
(* (\* (\\*   n0:nat -> PURE (a * nat) (fun post -> wp (fun a n -> post (a, n)) n0) *\\) *\) *)

(* (\* (\\* inline let lift_pure_state (a:Type) (wp:pure_wp a) (p:post a) (n:nat) = wp (fun a -> p a n) *\\) *\) *)
(* (\* (\\* sub_effect PURE ~> STATE = lift_pure_state *\\) *\) *)
(* (\* (\\* assume val r : range *\\) *\) *)

(* (\* (\\* val repr_bind: #a:Type -> #b:Type -> #wp1:wp a -> #wp2:(a -> GTot (wp b)) *\\) *\) *)
(* (\* (\\*          -> repr_STATE a wp1 *\\) *\) *)
(* (\* (\\*          -> (x:a -> Tot (repr_STATE b (wp2 x))) *\\) *\) *)
(* (\* (\\*          -> Tot (repr_STATE b (bind_wp nat r a b wp1 wp2)) *\\) *\) *)
(* (\* (\\* #reset-options "--log_queries"            *\\) *\) *)
(* (\* (\\* let repr_bind #a #b #wp1 #wp2 f g =  *\\) *\) *)
(* (\* (\\*   fun n0 -> admit(); //the encoding to SMT isn't sufficiently smart to capture monotonicity *\\) *\) *)
(* (\* (\\*          let x, n1 = f n0 in *\\) *\) *)
(* (\* (\\*          g x n1 *\\) *\) *)



