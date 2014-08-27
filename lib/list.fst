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

(* type In : #'a:Type => 'a => list 'a => Type *)
(* type ListUnion : #'a:Type => list 'a => list 'a => list 'a => Type *)
(* assume In_hd: forall 'a (hd:'a) (tl:list 'a). In hd (Cons hd tl) *)
(* assume In_tl: forall 'a (hd:'a) (x:'a) (tl:list 'a). In x tl ==> In x (Cons hd tl) *)
(* assume NotinNil: forall 'a (x:'a). ~(In x Nil) *)
(* assume NotinCons: forall 'a (x:'a) (y:'a) (tl:list 'a). ~(In x tl) /\ x=!=y ==> ~(In x (Cons y tl)) *)

(* let foo x = hd x *)

(* (\* val hd: list 'a -> 'a *\) *)
let hd = function
  | hd::tl -> hd
  | _ -> failwith "head of empty list"

(* let tail = function *)
(*   | hd::tl -> tl *)
(*   | _ -> failwith "tail of empty list" *)

(* val mem: 'a -> list 'a -> bool //x:'a -> l:list 'a -> b:bool{b==true <==> In x l} *)
(* let rec mem x = function *)
(*   | [] -> false *)
(*   | hd::tl -> if hd = x then true else mem x tl *)

(* val map: ('a -> 'b) -> list 'a -> list 'b *)
(* let rec map f x = match x with *)
(*   | [] -> [] *)
(*   | a::tl -> f a::map f tl *)

(* val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a *)
(* let rec fold_left f x y = match y with *)
(*   | [] -> x *)
(*   | hd::tl -> fold_left f (f x hd) tl *)

(* val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b *)
(* let rec fold_right f l x = match l with *)
(*   | [] -> x *)
(*   | hd::tl -> fold_right f tl (f hd x) *)

(* val iter: ('a -> unit) -> list 'a -> unit *)
(* let rec iter f x = match x with *)
(*   | [] -> () *)
(*   | a::tl -> let _ = f a in iter f tl *)
                                  
(* val assoc: 'a -> list ('a*'b) -> option 'b *)
(* let rec assoc a x = match x with *)
(*   | [] -> None *)
(*   | (a', b)::tl -> if a=a' then Some b else assoc a tl *)

(* val append: list 'a -> list 'a -> list 'a //x:list 'a -> y:list 'a -> z:list 'a { forall (a:'a). In a z <==> In a x \/ In a y } *)
(* let rec append x y = match x with *)
(*   | [] -> y *)
(*   | a::tl -> a::append tl y *)

(* val concatMap: ('a -> list 'b) -> list 'a -> list 'b *)
(* let rec concatMap f = function *)
(*   | [] -> [] *)
(*   | a::tl -> *)
(*     let fa = f a in *)
(*     let ftl = concatMap f tl in *)
(*     append fa ftl *)

(* assume val forall2: ('a -> 'b -> bool) -> list 'a -> list 'b -> bool *)
(* assume val mapi: (int -> 'a -> 'b) -> list 'a -> list 'b *)
(* assume val map2: ('a -> 'b -> 'c) -> list 'a -> list 'b -> list 'c *)
(* assume val split: list ('a * 'b) -> PURE.Tot (list 'a * list 'b) *)
(* assume val unzip: list ('a * 'b) -> PURE.Tot (list 'a * list 'b) *)
(* assume val unzip3: list ('a * 'b * 'c) -> PURE.Tot (list 'a * list 'b * list 'c) *)
(* assume val zip: list 'a -> list 'b -> PURE.Tot (list ('a * 'b)) *)
(* assume val zip3: list 'a -> list 'b -> list 'c -> PURE.Tot (list ('a * 'b * 'c)) *)
(* assume val map3: ('a -> 'b -> 'c -> 'd) -> list 'a -> list 'b -> list 'c -> list 'd *)
(* assume val rev: list 'a -> PURE.Tot (list 'a) *)
(* assume val collect: ('a -> list 'b) -> list 'a -> list 'b *)
(* assume val tl: list 'a -> list 'a *)
(* assume val length: list 'a -> PURE.Tot int *)
(* assume val tryFind: ('a -> bool) -> list 'a -> option 'b *)
(* assume val concat: list (list 'a) -> PURE.Tot (list 'a) *)
(* assume val sortWith: ('a -> 'a -> int) -> list 'a -> list 'a *)
(* assume val choose: ('a -> option 'b) -> list 'a -> list 'b *)
(* assume val flatten: list (list 'a) -> PURE.Tot (list 'a) *)
(* assume val filter: ('a -> bool) -> list 'a -> list 'a *)
(* assume val partition: ('a -> bool) -> list 'a -> (list 'a * list 'a) *)
(* assume val contains: 'a -> list 'a -> PURE.Tot bool *)
(* assume val fold_left2: ('s -> 'a -> 'b -> 's) -> 's -> list 'a -> list 'b -> 's *)

