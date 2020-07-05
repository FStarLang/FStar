module ND

(* An effect for (demonic) nondeterminism via lists. *)

open FStar.List.Tot
open FStar.Tactics
open FStar.Calc

open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics

// m is a monad. In this particular example, lists
val m (a : Type u#a) : Type u#a
let m a = list a

val m_return (#a : Type) : a -> m a
let m_return x = [x]

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind l f = concatMap f l

// w is an ordered (w_ord) monad with conjunction (w_conj) and actions from prop (w_act_prop)
// In this example, good ol' continuations into prop
val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = w:(w0 a)//{monotonic w}

val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

unfold
val w_return (#a : Type) : a -> w a
unfold
let w_return x = fun p -> p x

unfold
val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
unfold
let w_bind wp1 k =
  fun p -> wp1 (fun x -> k x p)

val interp (#a : Type) : m a -> w a
let interp #a (l:list a) = fun p -> forall x. memP x l ==> p x

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

let dm (a : Type) (wp : w a) : Type = 
  p:(a -> Type0) -> squash (wp p) -> l:(m a){forall x. memP x l ==> p x}
  
let irepr (a : Type) (wp: w a) = dm a wp

let ireturn (a : Type) (x : a) : irepr a (w_return x) = fun _ _ -> [x]

let rec pmap #a #b #pre (#post:b->Type0)
  (f : (x:a -> Pure b (requires (pre x)) (ensures post)))
  (l : list a)
  : Pure (list (v:b{post v}))
         (requires (forall x. memP x l ==> pre x))
         (ensures (fun _ -> True))
  = match l with
    | [] -> []
    | x::xs -> f x :: pmap #_ #_ #pre #post f xs

let rec unref #a #p (l : list (v:a{p v})) : l:(list a){forall x. memP x l ==> p x} =
  match l with
  | [] -> []
  | x :: xs -> x :: unref xs

let mem_memP
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma (ensures (mem x l <==> memP x l))
        [SMTPat (memP x l); SMTPat (mem x l)]
= FStar.List.Tot.Properties.mem_memP x l

val append_memP: #t:Type ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (memP a (l1@l2) <==> (memP a l1 \/ memP a l2)))
let rec append_memP #t l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_memP tl l2 a

let rec flatten_mem_lem #a (l : list (list a)) (x:a)
  : Lemma (memP x (flatten l) <==> (exists l0. memP l0 l /\ memP x l0))
          [SMTPat (memP x (flatten l))]
  = match l with
    | [] -> ()
    | l1::ls -> (append_memP l1 (flatten ls) x; flatten_mem_lem ls x)

let ibind (a : Type) (b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x))) : irepr b (w_bind wp_v wp_f) =
  fun p _ -> let l1 = v (fun x -> wp_f x p) () in
          let l2 = pmap #_ #(list b) #(fun x -> wp_f x p) #(fun l -> forall x. memP x l ==> p x) (fun x -> f x p ()) l1 in
          let l2 = unref l2 in
          let l2f = List.Tot.flatten l2 in
          l2f
 
let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) : Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a=
  fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p)

let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
  irepr a (wp_if_then_else wp1 wp2 b)

total
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

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a wp) (requires True)
                    (ensures (fun _ -> True))
  = fun p _ -> let r = Common.elim_pure f p in [r]

sub_effect PURE ~> ND = lift_pure_nd

val test_f : unit -> ND int (fun p -> p 5 /\ p 3)
let test_f () =
  ND?.reflect (fun _ _ -> [3; 5])

//let l () : (l:(list int){forall p. p 5 /\ p 3 ==> interp l p}) = reify (test_f ())
// ^ This one doesn't work... datatype subtyping to blame?

let l () : (l:(list int)) = reify (test_f ()) (fun _ -> True) ()

effect Nd (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        ND a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

val choose : #a:Type0 -> x:a -> y:a -> ND a (fun p -> p x /\ p y)
let choose #a x y =
    ND?.reflect (fun _ _ -> [x;y])

val fail : #a:Type0 -> unit -> ND a (fun p -> True)
let fail #a () =
    ND?.reflect (fun _ _ -> [])

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
let pyths_norm () = normalize_term (reify (pyths ()))

(* ^ Try it in emacs: C-c C-s C-e pyths_norm ():
Reducing ‘pyths_norm ()’…
pyths_norm () ↓βδιζr [3, 4, 5; 4, 3, 5; 6, 8, 10; 8, 6, 10] <: list ((int * int) * int)
*)
