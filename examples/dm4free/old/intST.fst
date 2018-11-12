module IntST

(* Note: this module implements a very explicit style of defining new monads; in
 * a sense, it's the output of the DMFF-translation done by hand, fed into the
 * existing effect checking code. DMFF performs this step automatically. See
 * FStar.DM4F.IntSt.fst for the easy, lightweight version of this. *)

let pre = int -> Type0
let post (a:Type) = (a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0
assume val r0: range
unfold let return_wp (a:Type) (x:a) (n0:int) (post:post a) =
  forall y. y == (x, n0) ==> post y

//working around #517 by adding an explicit 'val'
unfold val bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:wp a) -> (g:(a -> Tot (wp b))) -> Tot (wp b)
let bind_wp r a b f g =
    fun n0 post -> f n0 (fun x_n1 -> g (fst x_n1) (snd x_n1) post)

unfold let if_then_else  (a:Type) (p:Type)
                            (wp_then:wp a) (wp_else:wp a)
                            (h0:int) (post:post a) =
     l_ITE p
        (wp_then h0 post)
        (wp_else h0 post)
unfold let ite_wp        (a:Type)
                            (wp:wp a)
                            (h0:int) (q:post a) =
     forall (k:post a).
         (forall (x:a) (h:int).{:pattern (guard_free (k (x, h)))} q (x, h) ==> k (x, h))
         ==> wp h0 k
unfold let stronger  (a:Type) (wp1:wp a) (wp2:wp a) =
     (forall (p:post a) (h:int). wp1 h p ==> wp2 h p)

unfold let close_wp      (a:Type) (b:Type)
                            (wp:(b -> GTot (wp a)))
                            (h:int) (p:post a) =
     (forall (b:b). wp b h p)
unfold let assert_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p /\ wp h q
unfold let assume_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p ==> wp h q
unfold let null_wp       (a:Type)
                            (h:int) (p:post a) =
     (forall (x:a) (h:int). p (x,h))
unfold let trivial       (a:Type)
                            (wp:wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
let repr (a:Type) (wp:wp a) =
    n0:int -> PURE (a * int) (wp n0)

unfold val bind: (a:Type) -> (b:Type) -> (wp0:wp a)
                 -> (f:repr a wp0)
		 -> (wp1:(a -> Tot (wp b)))
                 -> (g:(x:a -> Tot (repr b (wp1 x))))
                 -> Tot (repr b (bind_wp r0 a b wp0 wp1))
let bind a b wp0 f wp1 g
  = fun n0 -> admit(); let (x,n1) = f n0 in g x n1
let return (a:Type) (x:a)
  : repr a (return_wp a x)
  = fun n0 -> (x, n0)

// The user may choose to provide definitions for actions in any of these two
// styles, as long as it's properly curried (i.e. the repr type is the return
// type)
let get (u:unit) : repr int (fun n0 post -> post (n0, n0))
  = fun n0 -> n0, n0

let get_unfolded (_: unit): (n0: int -> PURE (int * int) (fun post -> post (n0, n0)))
  = fun n0 -> n0, n0

// Note: the Tot is important, otherwise, this is desugared as an n-ary arrow
// and we're no longer encoding the number of arguments that belong to the action
// vs. the number of arguments that belong to the effect
let get_cps_type = unit -> Tot (repr int (fun n0 post -> post (n0, n0)))
let get_cps_type_unfolded = unit -> Tot (n0: int -> PURE (int * int) (fun post -> post (n0, n0)))

let put (n:int) : repr unit (fun n0 post -> post ((), n))
  = fun x -> (), n

let put_unfolded (n: int): (n0: int -> PURE (unit * int) (fun post -> post ((), n)))
  = fun x -> (), n

let put_cps_type = n:int -> Tot (repr unit (fun n0 post -> post ((), n)))
let put_cps_type_unfolded = n:int -> Tot (n0: int -> PURE (unit * int) (fun post -> post ((), n)))

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
;
    //these are new; both the regular and unfolded versions work
      get  = (fun _ x -> x, x), get_cps_type
    ; put  = (fun x _ -> (), x), put_cps_type
}
unfold let lift_pure_state (a:Type) (wp:pure_wp a) (n:int) (p:post a) = wp (fun a -> p (a, n))
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

reifiable let put' (x: int): ST unit
  (requires (fun n -> True))
  (ensures (fun n0 _ n1 -> n1 = x)) =
    STATE.reflect (put x)
