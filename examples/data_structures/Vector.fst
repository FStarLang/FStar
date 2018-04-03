(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module Vector

type vector 'a : nat -> Type =
  | VNil : vector 'a 0
  | VCons : hd:'a
         -> #n:nat
         -> tl:vector 'a n
         -> vector 'a (n + 1)

val head: #a:Type -> #n:pos -> vector a n -> Tot a
let head #a #n v = match v with
  | VCons x xs -> x

val nth : n:nat -> #m:nat{m > n} -> vector 'a m -> Tot 'a
let rec nth n #m (VCons x #m' xs) =
  if n = 0
  then x
  else nth (n-1) #m' xs

val append: #a:Type -> #n1:nat -> #n2:nat -> l:vector a n1 -> vector a n2 ->  Tot (vector a (n1 + n2)) //implicit n1 decreases
let rec append #a #n1 #n2 v1 v2 =
  match v1 with
    | VNil -> v2
    | VCons hd tl -> VCons hd (append tl v2)

val reverse: #a:Type -> #n:nat -> vector a n -> Tot (vector a n) //the implicitly computed n decreases
let rec reverse #a #n v = match v with
  | VNil -> VNil
  | VCons hd tl -> append (reverse tl) (VCons hd VNil)

val mapT: ('a -> Tot 'b) -> #n:nat -> vector 'a n -> Tot (vector 'b n)
let rec mapT f #n v = match v with
  | VNil -> VNil
  | VCons hd tl -> VCons (f hd) (mapT f tl)

val fold_left: ('b -> 'a -> Tot 'b) -> 'b -> #n:nat -> vector 'a n -> Tot 'b (decreases n)
let rec fold_left f acc #n v = match v with
  | VNil -> acc
  | VCons hd tl -> fold_left f (f acc hd) tl

val fold_right: ('a -> 'b -> Tot 'b) -> #n:nat -> vector 'a n -> 'b -> Tot 'b
let rec fold_right f #n v acc = match v with
  | VNil -> acc
  | VCons hd tl -> f hd (fold_right f tl acc)

val find: f:('a -> Tot bool) -> #n:nat -> vector 'a n -> Tot (option (x:'a{f x}))
let rec find f #n v = match v with
  | VNil -> None
  | VCons hd tl ->
    if f hd
    then Some hd
    else find f tl

val zip': #a:Type -> #b:Type -> #n:nat -> vector a n -> vector b n -> Tot (vector (a * b) n)
let rec zip' #a #b #n v1 v2 = match v1 with
  | VNil -> VNil
  | VCons a tl1 ->
    let VCons b tl2 = v2 in
    VCons (a, b) (zip' tl1 tl2)

(* val zip: #n:nat -> vector 'a n -> vector 'b n -> Tot (vector ('a * 'b) n) *)
(* let rec zip n v1 v2 = match v1, v2 with *)
(*   | VNil, _ -> VNil *)
(*   | VCons a tl1, VCons b tl2 -> VCons (a, b) (zip tl1 tl2) *)
