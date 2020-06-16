module ND

(* An effect for (demonic) nondeterminism via lists. *)

open FStar.List.Tot
open FStar.Tactics
open FStar.Calc

open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics

// m is a monad
val m (a : Type u#a) : Type u#a
let m a = list a

val m_return (a : Type) : a -> m a
let m_return a x = [x]

val m_bind (a : Type) (b : Type) : m a -> (a -> m b) -> m b
let m_bind _ _ =
  fun l f -> concatMap f l

// w is an ordered (w_ord) monad with conjunction (w_conj) and actions from prop (w_act_prop)
val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0


let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = w:(w0 a){monotonic w}


val w_ord (a : Type) : w a -> w a -> Type0
let w_ord a wp1 wp2 = forall p. wp1 p ==> wp2 p

val w_ord_trans (a : Type) (wp1 : w a) (wp2 : w a) (wp3 : w a) : Lemma (requires w_ord a wp1 wp2 /\ w_ord a wp2 wp3) (ensures w_ord a wp1 wp3)
let w_ord_trans = fun _ _ _ _ -> ()

// GM: this is "assume"
val w_act_prop (a : Type) : Type0 -> w a -> w a
let w_act_prop a phi wp = fun p -> phi ==> wp p


val w_conj (a : Type) : w a -> w a -> w a
let w_conj a wp1 wp2 p = wp1 p /\ wp2 p

val w_return (a : Type) : a -> w a
let w_return a x = fun p -> p x

val w_bind (a : Type) (b : Type) : w a -> (a -> w b) -> w b
let w_bind a b wp1 k =
  fun p -> wp1 (fun x -> k x p)

val w_bind_monotonic (a : Type) (b : Type) (m1 : w a) (m2 : w a) (f1 : a -> w b) (f2 : a -> w b) : Lemma (requires w_ord a m1 m2 /\ (forall (a : a).{:pattern f2 a} w_ord b (f1 a) (f2 a))) (ensures w_ord b (w_bind a b m1 f1) (w_bind a b m2 f2))
let w_bind_monotonic a b m1 m2 f1 f2 = ()

// we can define an "equality" on w a
val w_equiv (a : Type) : w a -> w a -> Type0
let w_equiv a wp1 wp2 = w_ord a wp1 wp2 /\ w_ord a wp2 wp1

// the monad morphism that connect the two monadic structures
val interp (#a : Type) : m a -> w a

let interp #a (l:list a) =
  fun p -> forall x. memP x l ==> p x

val interp_ret (a : Type) (x : a) : Lemma (interp (m_return a x) `w_equiv a` w_return a x)
let interp_ret a x = ()


val concatlemma (#a:Type) (l1 l2 :list a) (x:a) : Lemma (memP x (l1@l2) <==> memP x l1 \/ memP x l2)

let rec concatlemma #a l1 l2 x =
  match l1 with
  | [] -> ()
  | h::t -> concatlemma t l2 x

val concatmaplemma : (#a:Type) -> (#b:Type) -> l:list a -> (f:(a -> list b)) -> x:b ->
                               Lemma (memP x (concatMap f l) <==> (exists a. memP a l /\ memP x (f a)))
                                     [SMTPat (memP x (concatMap f l))]

let rec concatmaplemma #a #b l f x =
  match l with
  | [] -> ()
  | h::t ->
    concatlemma (f h) (concatMap f t) x;
    concatmaplemma t f x


let dro_w a wp2 wp1 = w_ord a wp1 wp2

val interp_bind (a b : Type) (v : m a) (f : a -> m b) : Lemma (interp (m_bind a b v f) `w_equiv _` w_bind a b (interp v) (fun a -> interp (f a)))

// uses pattern above, slightly brittle too
#push-options "--retry 10"
let interp_bind a b v f = ()
#pop-options

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

let dm (a : Type) (wp : w a) : Type = v:m a{w_ord a wp (interp v)}

let irepr (a : Type) (wp: w a) = unit -> dm a wp
let ireturn (a : Type) (x : a) : irepr a (w_return a x) = fun () -> interp_ret a x ; m_return a x

let ibind (a : Type) (b : Type) (wp_v : w a) (wp_f: a ^-> w b) (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x))) : irepr b (w_bind a b wp_v wp_f) =
  fun () ->
  interp_bind a b (v ()) (fun x -> f x ()) ;
  w_bind_monotonic a b wp_v (interp (v ())) wp_f (fun a -> interp (f a ()));
  w_ord_trans b (w_bind a b wp_v wp_f) (w_bind a b (interp (v ())) (fun a -> interp (f a ()))) (interp (m_bind a b (v ()) (fun x -> f x ())));
  m_bind a b (v ()) (fun x -> f x ())
 
let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) : Pure (irepr a wp2) (requires w_ord a wp2 wp1) (ensures fun _ -> True) =
  fun () -> w_ord_trans a wp2 wp1 (interp (f ())) ; f () 

let wp_if_then_else (a:Type) (wp1 wp2:w a) (p:Type0) : w a=
  w_conj a (w_act_prop a p wp1) (w_act_prop a (~p) wp2)

let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (p : Type0) : Type =
  irepr a (wp_if_then_else a wp1 wp2 p)

let lem_if_1 (a:Type) (wp1 wp2 : w a) (p:Type0) (f : irepr a wp1) (g : irepr a wp2)
  : Lemma (p ==> w_ord a (wp_if_then_else a wp1 wp2 p) wp1)
          [SMTPat ()]
  = 
  let aux post : Lemma (requires p /\ wp_if_then_else a wp1 wp2 p post)
                       (ensures wp1 post)
    =
    calc (<==>) {
      wp1 post;
      <==> {}
      p ==> wp1 post;
      <==> {}
      (p ==> wp1 post) /\ ((~p) ==> wp2 post);
      <==> {}
      (w_act_prop a p wp1 post) /\ (w_act_prop a (~p) wp2 post);
      <==> { _ by (compute ()) } // GM: why???
      w_conj a (w_act_prop a p wp1) (w_act_prop a (~p) wp2) post;
      <==> {}
      wp_if_then_else a wp1 wp2 p post;
    }
  in
  Classical.forall_intro (Classical.move_requires aux)
  
let lem_if_2 (a:Type) (wp1 wp2 : w a) (p:Type0) (f : irepr a wp1) (g : irepr a wp2)
  : Lemma ((~p) ==> w_ord a (wp_if_then_else a wp1 wp2 p) wp2)
          [SMTPat ()]
  = 
  let aux post : Lemma (requires (~p) /\ wp_if_then_else a wp1 wp2 p post)
                       (ensures wp2 post)
    =
    calc (<==>) {
      wp2 post;
      <==> {}
      (~p) ==> wp2 post;
      <==> {}
      (p ==> wp1 post) /\ ((~p) ==> wp2 post);
      <==> {}
      (w_act_prop a p wp1 post) /\ (w_act_prop a (~p) wp2 post);
      <==> { _ by (compute ()) } // GM: why???
      w_conj a (w_act_prop a p wp1) (w_act_prop a (~p) wp2) post;
      <==> {}
      wp_if_then_else a wp1 wp2 p post;
    }
  in
  Classical.forall_intro (Classical.move_requires aux)

// requires to prove that
// p ==> subcomp f (if_then_else p f g)

reifiable
reflectable
layered_effect {
  ND : a:Type -> wp : w a -> Effect
  with repr         = irepr;
       return       = ireturn;
       bind         = ibind;
       subcomp      = isubcomp; 
       if_then_else = i_if_then_else
}

assume Mono : forall (a:Type) (wp:pure_wp a). monotonic wp

assume Pure_wp_corr : forall (a:Type) (wp:pure_wp a) (f:(unit -> PURE a wp))
                        (p:pure_post a). wp p ==> p (f ())

let lemgg (a:Type) (wp:pure_wp a) p q (_ : squash p) (_ : monotonic wp) :
    Lemma (requires (wp (fun _ -> p)))
          (ensures (wp (fun x -> q x ==> p))) = ()

let lemhh (a:Type) (wp:pure_wp a) p (_ : squash p) :
    Lemma (requires (wp (fun _ -> True)))
          (ensures (wp (fun _ -> p))) = ()

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(unit -> PURE a wp)) :
  Pure (irepr a wp) (requires (wp (fun _ -> True)))
                    (ensures (fun _ -> True))
  = fun () -> admit (); [f ()] // GM : not sure why this fails

sub_effect PURE ~> ND = lift_pure_nd


assume val test_f : unit -> ND int (fun p -> p 5 /\ p 3)

let l : unit -> (l:list int{forall p. p 5 /\ p 3 ==> interp l p}) = reify (test_f ())

effect Nd (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ND a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

val choose : #a:Type0 -> x:a -> y:a -> ND a (fun p -> p x /\ p y)
let choose #a x y =
    ND?.reflect (fun () -> [x;y])

val fail : #a:Type0 -> unit -> ND a (fun p -> True)
let fail #a () =
    ND?.reflect (fun () -> [])

let flip () : ND bool (fun p -> p true /\ p false) =
    choose true false

let test () : ND int (fun p -> forall (x:int). 0 <= x /\ x < 10 ==> p x)  by (compute ()) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

[@expect_failure]
let test_bad () : ND int (fun p -> forall (x:int). 0 <= x /\ x < 5 ==> p x) by (compute ()) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

let guard (b:bool) : ND unit (fun p -> b ==> p ()) by (compute ()) =
  if b
  then ()
  else fail ()
  
let rec pick_from #a (l : list a) : ND a (fun p -> forall x. memP x l ==> p x) by (compute ()) =
    match l with
    | [] -> fail ()
    | x::xs ->
      if flip ()
      then x
      else pick_from xs

let ( * ) = op_Multiply

let pyths () : ND (int & int & int) (fun p -> forall x y z. x*x + y*y == z*z ==> p (x,y,z)) by (compute ()) =
  let l = [1;2;3;4;5;6;7;8;9;10] in
  let x = pick_from l in
  let y = pick_from l in
  let z = pick_from l in
  guard (x*x + y*y = z*z);
  (x,y,z)

(* Extracted code for pyths:

let (pyths_norm : unit -> (Prims.int * Prims.int * Prims.int) Prims.list) =
  fun uu____1038  ->
    [((Prims.parse_int "3"), (Prims.parse_int "4"), (Prims.parse_int "5"));
    ((Prims.parse_int "4"), (Prims.parse_int "3"), (Prims.parse_int "5"));
    ((Prims.parse_int "6"), (Prims.parse_int "8"), (Prims.parse_int "10"));
    ((Prims.parse_int "8"), (Prims.parse_int "6"), (Prims.parse_int "10"))]
*)
let pyths_norm () = normalize_term (reify (pyths ()) ())
