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


(** Base operations **)

assume val isEmpty: list 'a -> bool

(* val hd: list 'a -> 'a *)
let hd = function
  | hd::tl -> hd
  | _ -> failwith "head of empty list"

let tail = function
  | hd::tl -> tl
  | _ -> failwith "tail of empty list"
let tl = tail

val length: list 'a -> Tot nat
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl

assume val nth: list 'a -> int -> 'a

val count: 'a -> list 'a -> Tot nat
let rec count x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + (count x tl) else count x tl

assume val rev: list 'a -> Tot (list 'a)

val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y

assume val flatten: list (list 'a) -> Tot (list 'a)
let concat = flatten


(** Iterators **)

val iter: ('a -> unit) -> list 'a -> unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl

val map: ('a -> 'b) -> list 'a -> list 'b
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

assume val mapi: (int -> 'a -> 'b) -> list 'a -> list 'b

val concatMap: ('a -> list 'b) -> list 'a -> list 'b
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    append fa ftl

assume val map2: ('a -> 'b -> 'c) -> list 'a -> list 'b -> list 'c

assume val map3: ('a -> 'b -> 'c -> 'd) -> list 'a -> list 'b -> list 'c -> list 'd

val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

assume val fold_left2: ('s -> 'a -> 'b -> 's) -> 's -> list 'a -> list 'b -> 's

val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> fold_right f tl (f hd x)


(** List searching **)

val mem: 'a -> list 'a -> Tot bool //x:'a -> l:list 'a -> b:bool{b==true <==> In x l}
let rec mem x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl
let contains = mem

val find: a:Type
        -> f:(a -> Tot bool)
        -> list a
        -> Tot (option (x:a{f x}))
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

assume val filter: ('a -> bool) -> list 'a -> list 'a

val filterT: f:('a -> Tot bool) -> list 'a -> Tot (m:list 'a{forall x. mem x m ==> f x})
let rec filterT f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filterT f tl) else filterT f tl

assume val for_all: ('a -> bool) -> list 'a -> bool
assume val forall2: ('a -> 'b -> bool) -> list 'a -> list 'b -> bool

assume val collect: ('a -> list 'b) -> list 'a -> list 'b
assume val tryFind: ('a -> bool) -> list 'a -> option 'a
assume val tryPick: ('a -> option 'b) -> list 'a -> option 'b
assume val choose: ('a -> option 'b) -> list 'a -> list 'b

assume val partition: ('a -> bool) -> list 'a -> (list 'a * list 'a)

val partitionT: f:('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partitionT f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partitionT f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2


(** List of tuples **)

val assoc: 'a -> list ('a*'b) -> option 'b
let rec assoc a x = match x with
  | [] -> None
  | (a', b)::tl -> if a=a' then Some b else assoc a tl

assume val split: list ('a * 'b) -> PURE.Tot (list 'a * list 'b)
assume val unzip: list ('a * 'b) -> PURE.Tot (list 'a * list 'b)
assume val unzip3: list ('a * 'b * 'c) -> PURE.Tot (list 'a * list 'b * list 'c)
assume val zip: list 'a -> list 'b -> PURE.Tot (list ('a * 'b))
assume val zip3: list 'a -> list 'b -> list 'c -> PURE.Tot (list ('a * 'b * 'c))


(** Sorting **)

assume val sortWith: ('a -> 'a -> int) -> list 'a -> list 'a


(** Lemmas **)

val append_mem:  l1:list 'a
              -> l2:list 'a
              -> a:'a
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
                       [SMTPat (mem a (l1@l2))]
let rec append_mem l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

val append_count:  l1:list 'a
              -> l2:list 'a
              -> a:'a
              -> Lemma (requires True)
                       (ensures (count a (l1@l2) = (count a l1 + count a l2)))
                       [SMTPat (count a (l1@l2))]
let rec append_count l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_count tl l2 a
