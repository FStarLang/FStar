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
module FStar.List.Tot

(** Base operations **)

val isEmpty: list 'a -> Tot bool
let isEmpty l = match l with | [] -> true | _ -> false

val hd: l:list 'a{is_Cons l} -> Tot 'a
let hd = function
  | hd::_ -> hd

val tl: l:list 'a {is_Cons l} -> Tot (list 'a)
let tl = function
  | _::tl -> tl

val length: list 'a -> Tot nat
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl

val nth: list 'a -> nat -> Tot (option 'a)
let rec nth l n = match l with
  | []     -> None
  | hd::tl -> if n = 0 then Some hd else nth tl (n - 1)

val count: 'a -> list 'a -> Tot nat
let rec count x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + (count x tl) else count x tl

val rev_acc: list 'a -> list 'a -> Tot (list 'a)
let rec rev_acc l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc)

val rev: list 'a -> Tot (list 'a)
let rev l = rev_acc l []

val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y

val flatten: list (list 'a) -> Tot (list 'a)
let rec flatten l = match l with
    | [] -> []
    | hd::tl -> append hd (flatten tl)

val iter: ('a -> Tot unit) -> list 'a -> Tot unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl

val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val mapi_init: (int -> 'a -> Tot 'b) -> list 'a -> int -> Tot (list 'b)
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

val mapi: (int -> 'a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapi f l = mapi_init f l 0

val concatMap: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    append fa ftl

val fold_left: ('a -> 'b -> Tot 'a) -> 'a -> l:list 'b -> Tot 'a (decreases l)
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_right: ('a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(** List searching **)

val mem: 'a -> list 'a -> Tot bool //x:'a -> l:list 'a -> b:bool{b==true <==> In x l}
let rec mem x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl
let contains = mem

val existsb: #a:Type
       -> f:(a -> Tot bool)
       -> list a
       -> Tot bool
let rec existsb (a:Type) f l = match l with
 | [] -> false
 | hd::tl -> if f hd then true else existsb f tl

val find: #a:Type
        -> f:(a -> Tot bool)
        -> list a
        -> Tot (option (x:a{f x}))
let rec find (a:Type) f l = match l with
  | [] -> None #(x:a{f x}) //These type annotations are only present because it makes bootstrapping go much faster
  | hd::tl -> if f hd then Some #(x:a{f x}) hd else find f tl

val filter: f:('a -> Tot bool) -> list 'a -> Tot (m:list 'a{forall x. mem x m ==> f x})
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::filter f tl else filter f tl

val for_all: ('a -> Tot bool) -> list 'a -> Tot bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

val collect: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

val tryFind: ('a -> Tot bool) -> list 'a -> Tot (option 'a)
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

val tryPick: ('a -> Tot (option 'b)) -> list 'a -> Tot (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

val choose: ('a -> Tot (option 'b)) -> list 'a -> Tot (list 'b)
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

val partition: f:('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** [subset la lb] is true if and only if all the elements from [la]
    are also in [lb]. *)
val subset: #a:Type -> list a -> list a -> Tot bool
let rec subset la lb =
  match la with
  | [] -> true
  | h :: tl ->  mem h lb && subset tl lb

val noRepeats : #a:Type -> list a -> Tot bool
let rec noRepeats la =
  match la with
  | [] -> true
  | h :: tl ->  not(mem h tl) && noRepeats tl


(** List of tuples **)

val assoc: 'a -> list ('a*'b) -> Tot (option 'b)
let rec assoc a x = match x with
  | [] -> None
  | (a', b)::tl -> if a=a' then Some b else assoc a tl

val split: list ('a * 'b) -> Tot (list 'a * list 'b)
let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)
let unzip = split

val unzip3: list ('a * 'b * 'c) -> Tot (list 'a * list 'b * list 'c)
let rec unzip3 l = match l with
    | [] -> ([],[],[])
    | (hd1,hd2,hd3)::tl ->
       let (tl1,tl2,tl3) = unzip3 tl in
       (hd1::tl1,hd2::tl2,hd3::tl3)

(** Sorting (implemented as quicksort) **)
val partition_length: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures (length (fst (partition f l)) + length (snd (partition f l)) = length l))
let rec partition_length f l = match l with
  | [] -> ()
  | hd::tl -> partition_length f tl

val bool_of_compare : ('a -> 'a -> Tot int) -> 'a -> 'a -> Tot bool
let bool_of_compare f x y = f x y >= 0

val sortWith: ('a -> 'a -> Tot int) -> l:list 'a -> Tot (list 'a) (decreases (length l))
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     append (sortWith f lo) (pivot::sortWith f hi)
