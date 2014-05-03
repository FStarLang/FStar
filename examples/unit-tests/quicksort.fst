module Quicksort

(* definining a non-strict total order *)
type NSTO (#'a:Type) ('R:'a => 'a => Type) = 
    (forall (x:'a). 'R x x)                                    (* reflexive *)
 /\ (forall (x:'a) (y:'a). 'R x y /\ x<>y  ==> not ('R y x))   (* anti-symmetric *)
 /\ (forall (x:'a) (y:'a) (z:'a). 'R x y /\ 'R y z ==> 'R x z) (* transitive *)

(* sortedRange 'a 'R lo hi l : a list that has elements (x1 'R ... 'R xn) ... where a 'R x1 and xn 'R hi *)
logic val sortedRange: 'a:Type -> 'R:('a => 'a => Type) -> lo:'a -> hi:'a -> bool
let rec sortedRange 'a ('R:'a => 'a => Type) lo hi = function
  | [] -> as_bool ('R lo hi)
  | hd::tl ->  as_bool ('R lo hd) &&
               as_bool ('R hd hi) &&
               sortedRange 'a 'R hd hi tl 
      
type nat = x:int{x>=0}

val occurs : 'a --> list 'a --> nat
let rec occurs x l : $decreases l = match l with
  | [] -> 0
  | y::tl -> if x=y then 1 + occurs x tl else occurs x tl
      
type Permutation (#'a:Type) l m = 
    forall x. occurs x l = occurs x m

type Mem (#'a:Type) x l = 
    occurs 'a x l > 0

type slist 'a 'R n1 n2 = 
    i:list 'a{sortedRange 'a 'R n1 n2 i = true}

val append: 'a:_ -> 'R:_ -> #n1:'a -> #n2:'a -> #n3:'a -> #n4:'a 
         -> i:slist 'a 'R n1 n2
         -> j:slist 'a 'R n3 n4{'R n1 n2 /\ 'R n2 n3 /\ 'R n3 n4 /\ NSTO 'R}
         -> k:slist 'a 'R n1 n4{forall x. occurs x k = occurs x i + occurs x j}
let rec append 'a 'R n1 n2 n3 n4 i j = match i with 
  | [] -> j
  | hd::tl -> 
    let tl : slist 'a 'R hd n2 = tl in 
    hd::append tl j

type decides ('a:Type) ('R:'a => 'a => Type) = 
    cmp:(x:'a -> y:'a -> b:bool{(b=true <==> 'R x y) /\ (b=false <==> (x<>y /\ 'R y x))}){NSTO 'R}

val partition: 'a:_ -> 'R:_ 
            -> cmp:decides 'a 'R
            -> x:'a
            -> l:list 'a
            -> (lo:list 'a
                * hi:list 'a{(forall y. Mem y lo ==> 'R y x /\ Mem y l)
                               /\ (forall y. Mem y hi ==> 'R x y /\ x<>y /\ Mem y l)
                               /\ (forall y. occurs y l = occurs y lo + occurs y hi)})
let rec partition 'a 'R cmp x l = match l with
  | [] -> ([], [])
  | hd::tl ->
    let lo, hi = partition 'a 'R cmp x tl in
    if cmp hd x
    then (hd::lo, hi)
    else (lo, hd::hi)

val quicksort: 'a:_ -> 'R:_
       -> cmp:decides 'a 'R
       -> min:ghost 'a
       -> max:ghost 'a{'R min max}
       -> i:list 'a{forall x. Mem x i ==> ('R (unghost min) x /\ 'R x (unghost max))}
       -> j:slist 'a 'r (unghost min) (unghost max){Permutation i j}
let rec quicksort 'a 'R cmp min max i = match i with
  | [] -> []
  | hd::tl ->
    let lo, hi = partition cmp hd tl in
    let i' = quicksort cmp min hd lo in
    let j' = quicksort cmp hd max hi in
    append i' (hd::j')

(*--------------------------------------------------------------------------------*)
(* A client of quicksort for integers *)
(*--------------------------------------------------------------------------------*)
let rec min = function 
  | [] -> 0
  | [x] -> x
  | hd::tl -> 
    let x = min tl in
    if leq x hd then x else hd

let rec max = function 
  | [] -> 0
  | [x] -> x
  | hd::tl -> 
    let x = max tl in
    if x > hd then x else hd

(*  Would be nice to have such a syntax to introduce lemmas into the context *)
lemma val minmax : l:list 'a --> u:unit{min l <= max l}
let rec minmax l : {decreases l} = match l with 
  | [] -> ()
  | _::tl -> minmax tl

lemma val minmem: x:'a --> l:list 'a{Mem x l} --> u:unit{min l <= x}
let rec minmem x = function  (* function is sugar for match+decreases *)
  | _::tl -> minmem x tl

lemma val maxmem: x:'a --> l:list 'a{Mem x l} --> u:unit{x <= max l}
let rec maxmem x = function
  | _::tl -> maxmem x tl
 
type Sorted = fun m => exists a b. sortedRange int LTE a b m = true

val sort_int : l:list int -> m:list int {Sorted m /\ Permutation l m}
let sort_int l = 
  quicksort int LTE (fun x y -> x <= y) (ghost (min l)) (ghost (max l)) l
