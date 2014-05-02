(*
   Copyright 2008-2014 Nikhil Swamy, Chantal Keller, Microsoft Research and Inria

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Termination


(***** Factorial *****)

(*
  val factorial^x: x:int{x >= 0} -> y:int{y >= 0}

  Terminates thanks to the T-Fix rule:

  t == z:int{z >= 0}
  e == if x = 0 then 1 else x * (factorial (x-1))

   S,G, x:int{x >= 0}; factorial:(y:int{y >= 0 /\ y < x}) --> t |-mu e : t
 --------------------------------------------------------------------------- [T-Fix]
   S;G |-mu fix (factorial^x: x:int{x >= 0} -> t) x = e : t
*)
val factorial: x:int{x >= 0} -> y:int{y >= 0}
let rec factorial x = if x = 0 then 1 else x * (factorial (x-1))












(***** Coq-Club example *****)

(*
  val sumto^i: i:int{i >= 0} -> f:(x:int{0 <= x /\ x <= i} -> y:int{y >= 0}) -> z:int{z >= 0}

  Terminates thanks to the T-Fix rule:

  t == f:(x:int{0 <= x /\ x <= i} -> y:int{y >= 0}) -> z:int{z >= 0}
  e == fun f -> if i = 0 then f 0 else (f i) + (sumto (i-1) f)

   S,G, i:int{i >= 0}; sumto:(j:int{j >= 0 /\ j < i}) --> t |-mu e : t
 ----------------------------------------------------------------------- [T-Fix]
   S;G |-mu fix (sumto^i: i:int{i >= 0} -> t) i = e : t
*)
val sumto: i:int{i >= 0} -> f:(x:int{0 <= x /\ x <= i} -> y:int{y >= 0}) -> z:int{z >= 0}
let rec sumto i f = if i = 0 then f 0 else (f i) + (sumto (i-1) f)


(*
  val strangeZero^v: v:int{v >= 0} -> u:int{u = 0}

  Terminates thanks to the T-Fix rule and the typing given to sumto:

  t == u:int{u = 0}
  e == if v = 0 then 0 else sumto (v-1) strangeZero

   S,G, v:int{v >= 0}; strangeZero:(w:int{w >= 0 /\ w < v}) --> t |-mu e : t
 ----------------------------------------------------------------------------- [T-Fix]
   S;G |-mu fix (strangeZero^v: v:int{v >= 0} -> t) v = e : t

  The premise is true because:

   S;G, v:int{v >= 0}; strangeZero:(w:int{w >= 0 /\ w < v}) --> t |-mu sumto (v-1) strangeZero : z:int{z >= 0}

  since the precondition of the second argument of sumto is verified:
   {0 <= w /\ w <= v-1}
*)
val strangeZero: v:int{v >= 0} -> u:int{u = 0}
let rec strangeZero v = if v = 0 then 0 else sumto (v-1) strangeZero













(***** Map function *****)

(*
  val mapTotal : [d:'a] -> l:list 'a{forall x ∈ l. x < d} -> (y:'a{y < d} -> 'b) -> list 'b
*)
val mapTotal : list 'a -> ('a -> 'b) -> list 'b
let rec mapTotal l f = match l with
  | [] -> []
  | hd::tl -> (f hd)::(mapTotal tl f)



type T 'a =
  | Leaf : 'a -> T 'a
  | Node : list (T 'a) -> T 'a


(*
  val treeMap^v: v:T 'a -> ('a -> 'b) -> T 'b

  Terminates thanks to the T-Fix rule and the typing given to mapTotal:

  t == ('a -> 'b) -> T 'b
  e == fun f -> ...

   S,G, v:T 'a; treeMap:(w:T 'a{w < v}) --> t |-mu e : t
 --------------------------------------------------------- [T-Fix]
   S;G |-mu fix (treeMap^v: v:T 'a -> t) v = e : t

  because:

   S,G, v:T 'a; treeMap:(w:T 'a{w < v}) --> t |-mu mapTotal [v] l (fun u -> treeMap u f) : list (T 'b)

  since:
    l:(list (T 'a)){forall x ∈ l. x < v}            (this is the subterm order on trees)
    S,G, v:T 'a; treeMap:(w:T 'a{w < v}) --> t |-mu fun u -> treeMap u f : y:(T 'a){y < v} -> T 'b
*)
val treeMap : T 'a -> ('a -> 'b) -> T 'b
let rec treeMap v f = match v with
  | Leaf a -> Leaf (f a)
  | Node l -> Node (mapTotal l (fun u -> treeMap u f))



(* TODO:
   - type treeMap like mapTotal
   - rephrase in terms of measures rather than [d:'a] *)
