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
module List

type In : 'a:S => 'a => list 'a => E
type ListUnion : 'a:S => list 'a => list 'a => list 'a => E
assume In_hd: forall 'a (hd:'a) (tl:list 'a). In hd (Cons hd tl)
assume In_tl: forall 'a (hd:'a) (x:'a) (tl:list 'a). In x tl ==> In x (Cons hd tl)
assume NotinNil: forall 'a (x:'a). not (In x Nil)
assume NotinCons: forall 'a (x:'a) (y:'a) (tl:list 'a). not(In x tl) /\ x<>y ==> not(In x (Cons y tl))

val mem: x:'a -> l:list 'a -> b:bool{b=true <==> In x l}
let rec mem x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

val map: ('a -> 'b) -> list 'a -> list 'b
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> fold_right f tl (f hd x)

val iterate: ('a -> unit) -> list 'a -> unit
let rec iterate f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iterate f tl
                                  
val assoc: 'a -> list ('a*'b) -> option 'b
let rec assoc a x = match x with
  | [] -> None
  | (a', b)::tl -> if a=a' then Some b else assoc a tl

val append: x:list 'a -> y:list 'a -> z:list 'a { forall (a:'a). In a z <==> In a x \/ In a y }
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y

val concatMap: ('a -> list 'b) -> list 'a -> list 'b
let rec concatMap f = function
  | [] -> []
  | a::tl -> append (f a) (concatMap f tl)
