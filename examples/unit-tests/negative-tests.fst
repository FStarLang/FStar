(* EXPECT 32 FAILURES *)
(* ******************************************************************************** *)
module Neg

assume val g : 'a -> Tot 'b
assume val h : a:Type -> b:Type -> a:'a -> Tot (b:'b{b == g a})
assume val length: list 'a -> Tot int

opaque val x:nat
let x = -1 //should fail reporting 1 error
opaque val y:nat
let y = -1 //should also fail reporting only 1 error

let assert_0_eq_1 () = assert (0=1) //should fail

let hd_int_inexhaustive l = match l with
  | hd::_ -> hd //should fail

val test_label: x:int -> Pure int (requires (x > 0)) (ensures (fun y -> y > 0))
let test_label x = x

val test_precondition_label: x:int -> Tot int
let test_precondition_label x = test_label x //should fail

val test_postcondition_label: x:int -> Pure int (requires True) (ensures (fun y -> y > 0))
let test_postcondition_label x = x //should fail

val bad_projector: option 'a -> 'a
let bad_projector x = Some.v x (* should fail *)

assume type T : (result int -> Type) -> Type
assume TEST: T (fun ri -> b2t (V.v ri = 0))//should fail: not (is_V ri)

assume val f1: (x:int -> Tot unit) -> Tot unit
assume val g1: nat -> Tot unit
let h1 = f1 (fun x -> g1 x) //should fail; x is not nat

(* ******************************************************************************** *)

module NegSet
assume type elt
assume logic val a : elt
assume logic val b : elt
assume logic val c : elt
assume AB_distinct: a=!=b
open FStar.Set

val should_fail1: unit -> Tot unit
let should_fail1 u =
  assert (mem b (singleton a))

val should_fail2: unit -> Tot unit
let should_fail2 u =
  assert (subset (union (singleton a) (singleton b)) (singleton a))

val should_fail3: unit -> Tot unit
let should_fail3 u =
  assert (mem c (union (singleton a) (singleton b)))

(* ******************************************************************************** *)
module NegHeap
open FStar.Set
open FStar.Heap
assume val x : ref int
assume val y : ref int
assume val h : heap
assume DistinctXY: x <> y

let test2 _ = assert (sel (upd (upd h x 0) y 1) y = 0) //should fail
let test10 (x:ref int) (y:ref int) (h0:heap) (h1:heap) (h2:heap) =
  admitP (b2t (h1 = concat h1 (restrict h0 (complement empty))));
  admitP (b2t (h1 = upd h0 x 0));
  admitP (~ (contains h1 y));
  assert false //should fail

(* ******************************************************************************** *)
module NegTermination
val bug15 : m : int -> z : int ->
            Lemma (ensures False)
let rec bug15 m =
  match m with
  | _ -> (fun l -> bug15 m l)

val repeat_diverge : int -> int -> Tot int
let rec repeat_diverge n count =
  match count with
  | 0 -> 0
  | _ -> repeat_diverge n (count-1)


val ackermann_bad: m:int -> n:int -> Tot int
let rec ackermann_bad m n = (* expected failure *)
  if m=0 then n + 1
  else if n = 0 then ackermann_bad (m - 1) 1
  else ackermann_bad (m - 1) (ackermann_bad m (n - 1))

val length_bad: list 'a -> Tot nat
let rec length_bad l = match l with (* expect failure *)
  | [] -> 0
  | _::tl -> 1 + length_bad l

val sumto: i:nat -> f:(x:nat{x <= i} -> Tot nat) -> Tot nat
let rec sumto i f =
  if i = 0
  then f 0
  else f i + sumto (i-1) f

val strangeZeroBad: nat -> Tot nat
let rec strangeZeroBad v = (* expect failure *)
  if v = 0
  then 0
  else sumto v strangeZeroBad

type snat =
  | O : snat
  | S : snat -> snat

val t1 : snat -> Tot bool
let rec t1 n =
  match n with
  | O        -> true
  | S O      -> false
  | S (S n') -> t1 (S (S n')) //termination check should fail

val plus : snat -> snat -> Tot snat
let rec plus n m =
  match n with
    | O -> m
    | S O -> m
    | S (S n') -> plus (S (S n')) m //termination check should fail

val plus' : snat -> snat -> Tot snat
let plus' n m =
  match n with //patterns are incomplete
    | O -> m
    | S O -> m

val minus : snat -> snat -> Tot snat
let rec minus (n : snat) (m : snat) : snat =
  match n, m with
  | O   , _    -> O
  | S n', m' -> minus (S n') m' //termination check should fail

val xxx : snat -> Tot snat
let rec xxx (n : snat) : snat =
  match n, 42 with
  | O, 42   -> O
  | S n', 42 -> xxx (S n')


(* ******************************************************************************** *)
module NegBST

(* The type of a binary tree indexed by its max element *)
type tree: int -> Type =
  | Leaf : n:int -> tree n
  | Node : #l   :int
        -> left :option (tree l)
        -> n    :int
        -> #r   :int
        -> right:option (tree r){l <= n
                                 /\ n <= r
                                 /\ (is_None right <==> n=r)
                                 /\ (is_None left <==> n=l)}
        -> tree r


let test_node_1 () = Node #1 None 1 #1 None
let test_node_2 (l:int) (t:tree l) = Node (Some t) (l + 1) #(l + 1) None
let test_node_3 (l:int) (t1:tree l) (t2:tree (l + 2)) = Node (Some t1) (l + 1) (Some t2)

let bad_node_1 () = Node #0 None 1 #2 None                                              //fails: needs to be Node #1 None 1 #1 None
let bad_node_2 (l:int) (t:tree l) = Node (Some t) l #(l + 1) None                       //fails: needs to be (l + 1) in the middle
let bad_node_3 (l:int) (t1:tree l) (t2:tree (l + 1)) = Node (Some t1) (l + 1) (Some t2) //fails: t2 must be at least tree (l + 2)

module Bug260
type pnat =
  | O : pnat
  | S : pnat -> pnat

type validity : n:pnat -> Type =
  | VSucc : n:pnat -> Tot (validity (S n))
val bad : t:pnat -> Tot (validity (S (S t)))
let bad t = VSucc t


(* Hard to keep this one in the suite since the program fails to even --lax check *)
(* module EscapingVariable *)
(* assume type Good : int -> Type *)
(* assume val enc: plain:int -> c:unit{Good plain} *)
(* assume val repr : int -> int *)

(* let f (text:int) = enc (repr text) //should fail; plain escapes *)

module ShortCircuitingBugs

type Bad : bool -> Type
val bad : x:int -> Tot (b:bool{Bad b})
let rec bad x = true || bad (x-1)

val ff : unit -> Lemma (ensures False)
let ff u = ignore (false && (0 = 1))


module ProofOfFalse (* #284 *)
val foo : f:(unit -> Tot bool){f () = true}
          -> Tot (r:bool {r = f () /\ r = true})
let foo f = f ()
val bar : unit -> Pure bool (requires True) (ensures (fun _ -> False))
let bar () = foo (fun x -> false)
