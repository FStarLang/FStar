module ID3

val m (a : Type u#a) : Type u#a
let m a = a

val m_return (#a : Type) : a -> m a
let m_return x = x

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind v f = f v 

// w is an ordered (w_ord) monad with conjunction (w_conj) and actions from prop (w_act_prop)
val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = w:(w0 a){monotonic w}

val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

val w_ord_trans (#a : Type) (wp1 : w a) (wp2 : w a) (wp3 : w a) : Lemma (requires w_ord wp1 wp2 /\ w_ord wp2 wp3) (ensures w_ord wp1 wp3)
let w_ord_trans wp1 wp2 wp3 = ()

// GM: this is "assume"
val w_act_prop (#a : Type) : Type0 -> w a -> w a
let w_act_prop phi wp = fun p -> phi ==> wp p

val w_conj (#a : Type) : w a -> w a -> w a
let w_conj wp1 wp2 p = wp1 p /\ wp2 p

val w_return (#a : Type) : a -> w a
let w_return x = fun p -> p x

val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
let w_bind wp1 k = fun p -> wp1 (fun x -> k x p)

val w_bind_monotonic (#a #b : Type) (m1 : w a) (m2 : w a) (f1 : a -> w b) (f2 : a -> w b) : Lemma (requires w_ord m1 m2 /\ (forall (a : a).{:pattern f2 a} w_ord (f1 a) (f2 a))) (ensures w_ord (w_bind m1 f1) (w_bind m2 f2))
let w_bind_monotonic m1 m2 f1 f2 = ()

// we can define an "equality" on w a
val w_equiv (#a : Type) : w a -> w a -> Type0
let w_equiv wp1 wp2 = w_ord wp1 wp2 /\ w_ord wp2 wp1

// the monad morphism that connect the two monadic structures
val interp (#a : Type) : m a -> w a

let interp #a (x:m a) = fun p -> p x

val interp_ret (#a : Type) (x : a) : Lemma (interp (m_return x) `w_equiv` w_return x)
let interp_ret x = ()

let dro_w wp2 wp1 = w_ord wp1 wp2

val interp_bind (#a #b : Type) (v : m a) (f : a -> m b) : Lemma (interp (m_bind v f) `w_equiv` w_bind (interp v) (fun a -> interp (f a)))
let interp_bind v f = ()

// In DM4A we would have something like:

// total
// reifiable
// reflectable
// new_effect {
//   DM4A : a:Type -> Effect
//   with
//        repr      = m
//      ; return    = m_return
//      ; bind      = m_bind

//      ; wp_type   = w
//      ; return_wp = w_return
//      ; bind_wp   = w_bind

//      ; interp    = interp
// }

// In layered effects, we instead construct the Dijkstra monad as a
// sigma type (see the paper)

let dm (a : Type) (wp : w a) : Type =
  c:(m a){wp `w_ord` interp c}

let irepr (a : Type) (wp: w a) = dm a wp

let ireturn (a : Type) (x : a) : irepr a (w_return x) =
 interp_ret x;
 m_return x

let ibind (a b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x))) : irepr b (w_bind wp_v wp_f) =
  m_bind v f

let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) : Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

let wp_if_then_else (#a:Type) (wp1 wp2:w a) (p:Type0) : w a=
  w_conj (w_act_prop p wp1) (w_act_prop (~p) wp2)

let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (p : Type0) : Type =
  irepr a (wp_if_then_else wp1 wp2 p)

module T = FStar.Tactics

let lem_if_1 (#a:Type) (wp1 wp2 : w a) (p:Type0) (f : irepr a wp1) (g : irepr a wp2)
  : Lemma (p ==> w_ord (wp_if_then_else wp1 wp2 p) wp1)
          [SMTPat ()]
          by (T.norm [delta])
  = 
  ()
  
let lem_if_2 (#a:Type) (wp1 wp2 : w a) (p:Type0) (f : irepr a wp1) (g : irepr a wp2)
  : Lemma ((~p) ==> w_ord (wp_if_then_else wp1 wp2 p) wp2)
          [SMTPat ()]
          by (T.norm [delta])
  = 
  ()

// requires to prove that
// p  ==> subcomp f (if_then_else p f g)
// ~p ==> subcomp g (if_then_else p f g)
// that's what the hacky SMTPats are for, we don't have a way
// to provide a proof explicitly
total
reifiable
reflectable
layered_effect {
  ID : a:Type -> wp : w a -> Effect
  with repr         = irepr;
       return       = ireturn;
       bind         = ibind;
       subcomp      = isubcomp; 
       if_then_else = i_if_then_else
}

let lift_pure_nd (a:Type) (wp:pure_wp a{monotonic wp}) (f:(unit -> PURE a wp)) :
  Pure (irepr a wp) (requires (wp (fun _ -> True)))
                    (ensures (fun _ -> True))
  = m_return (f ())

sub_effect PURE ~> ID = lift_pure_nd

(* Checking that it's kind of usable *)

val test_f : unit -> ID int (fun p -> p 5 /\ p 3)
let test_f () = 3

(* Need the compute sadly, not sure why *)
let l () : Tot int =
  let o = reify (test_f ()) in
  o

effect Id (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ID a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect IdT (a:Type) = Id a True (fun _ -> True)

#set-options "--debug ID --debug_level SMTQuery"

(* Can't prove termination... why? And uncommenting the `explode`
 * actually makes F* explode :-) *)
[@@expect_failure]
let rec sum (l : list int) : IdT int //by (T.explode ())
 =
  match l with
  | [] -> 0
  | x::xs -> x + sum xs
