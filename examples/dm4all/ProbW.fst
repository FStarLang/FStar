module ProbW

module List = FStar.List.Tot
open FStar.Mul

let repr (a:Type) = list (a & nat)

let return (a:Type u#a) (x:a) = [(x, 1)]

let bind (a : Type) (b : Type) (l : repr a) (f : a -> repr b) : repr b =
  List.concatMap (fun ((x, w1) : a & nat) -> List.map (fun ((y, w2) : b & nat)-> (y, (w1 * w2 <: nat))) (f x)) l

assume val prop2bool : p:Type0 -> b:bool{b2t b == p}

let rec compute_probs #a acc_t acc_f (l : repr a) (p : pure_post a) : Tot (nat & nat) (decreases l) =
  match l with
  | [] -> (acc_t, acc_f)
  | (x,w)::ps ->
    let t = if prop2bool (p x) then w else 0 in
    let f = if prop2bool (p x) then 0 else w in
    compute_probs (acc_t + t) (acc_f + f) ps p

(* NOT a morphism! So this entire file is pretty useless.
 * Also note the bad example test'_3 *)
let interp (#a:Type) (l : repr a) : pure_wp a =
  fun post -> 
    let (t, f) = compute_probs 0 0 l post in
    t >= f

let l : repr int = [(10, 1); (20, 2)]
let f : int -> repr int = fun x -> [(x, 4); (2 * x , 8)]
let wp1 = interp (bind _ _ l f)
let wp2 = pure_bind_wp range_0 _ _ (interp l) (fun x -> interp (f x))


open FStar.Tactics

let tau () =
  compute (); trefl ()

[@(postprocess_with tau)] let wpn1 = normalize_term wp1
[@(postprocess_with tau)] let wpn2 = normalize_term wp2


total
reifiable
reflectable
new_effect {
  PROB : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = pure_wp
     ; return_wp = pure_return
     ; bind_wp   = pure_bind_wp

     ; interp    = interp
}

let test1 () : PROB int (fun p -> p 5 /\ p 3) = 5
let test2 () : PROB int (fun p -> p 5 /\ p 3) = 3

// Whoa! This used to succeed since the effect is marked as reifiable,
// and Rel compares the representation types on each side for the
// subtyping. and both are just `unit -> list a`. I changed it to check
// the WPs via stronger-than instead of always unfolding.
[@expect_failure]
let test3 () : PROB int (fun p -> p 5 /\ p 3) = 4

effect Prob (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        PROB a (fun (p:pure_post a) -> pre /\ (forall (pure_result:a). post pure_result ==> p pure_result))

effect PROBTot (a:Type) = PROB a (pure_null_wp a)

val choose : #a:Type0 -> x:a -> y:a -> PROB a (fun p -> p x /\ p y)
let choose #a x y =
    PROB?.reflect ([(x, 1); (y, 1)] <: list (a & nat))

open FStar.Tactics

let wchoose (#a:Type0) (wx wy : nat) (x y : a) : PROB a (fun p -> p x /\ p y) =
    PROB?.reflect [(x, wx); (y, wy)]
    
let wchoose' (#a:Type0) (wx : nat) (wy : nat{wy > wx}) (x y : a) : PROB a (fun p -> p y) =
    PROB?.reflect [(x, wx); (y, wy)]

val noise : #a:Type0 -> x:a -> PROB a (fun p -> True) // no need to prove anything, weight is 0
let noise #a x = PROB?.reflect ([(x, 0)] <: list (a & nat))

val noise': #a:Type0 -> x:a -> PROB a (fun p -> True)
[@expect_failure]
let noise' #a x = PROB?.reflect ([(x, 1)] <: list (a & nat))


val fail : #a:Type0 -> unit -> PROB a (fun p -> True)
let fail #a () =
    PROB?.reflect []

let test () : PROB int (fun p -> forall (x:int). 0 <= x /\ x < 10 ==> p x) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

[@expect_failure]
let test_bad () : PROB int (fun p -> forall (x:int). 0 <= x /\ x < 5 ==> p x) =
    let x = choose 0 1 in
    let y = choose 2 3 in
    let z = choose 4 5 in
    x + y + z

let rec pick #a (l : list a) : PROB a (fun p -> forall x. List.memP x l ==> p x) =
    match l with
    | [] -> fail ()
    | x::xs ->
      // choose x (pick xs)
      // ^ this is wrong! it will call `pick xs` before choosing and always
      //   end up returning []
      if choose true false
      then x
      else pick xs

let guard (b:bool) : PROB unit (fun p -> b ==> p ()) =
  if b
  then ()
  else fail ()

let ( * ) = op_Multiply

let test_reify_1 () = assert (reify (test1 ()) ==  [(5, 1)])
let test_reify_2 () = assert (reify (test2 ()) ==  [(3, 1)])
let test_reify_3 () = assert (reify (test1 ()) =!= [(4, 1)])

[@expect_failure]
let _ = assert False

let test'_1 () : PROB int (fun p -> p 5) =
  PROB?.reflect ([(3, 1); (5, 2)] <: list (int & nat))

(* plain wrong, most common values are 11 and 13, not 15 *)
let test'_3 () : PROB int (fun p -> p 15) =
  test'_1 () + test'_1 () + test'_1 ()

let xx = normalize_term (reify (test'_3 ()))
