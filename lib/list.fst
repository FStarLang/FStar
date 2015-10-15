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
module FStar.List

(** Base operations **)

val isEmpty: list 'a -> Tot bool
let isEmpty l = match l with | [] -> true | _ -> false
let isEmptyT = isEmpty

val hd: list 'a -> 'a
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
let lengthT = length

val nth: list 'a -> int -> 'a
let rec nth l n =
  if n < 0 then
    failwith "nth takes a non-negative integer as input"
  else
    if n = 0 then
      match l with
        | [] -> failwith "not enough elements"
        | hd::_ -> hd
    else
      match l with
        | [] -> failwith "not enough elements"
        | _::tl -> nth tl (n - 1)

val total_nth: list 'a -> nat -> Tot (option 'a)
let rec total_nth l n = match l with
  | []     -> None
  | hd::tl -> if n = 0 then Some hd else total_nth tl (n - 1)

val count: 'a -> list 'a -> Tot nat
let rec count x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + (count x tl) else count x tl
let countT = count

val rev_acc: list 'a -> list 'a -> Tot (list 'a)
let rec rev_acc l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc)

let rev_append = rev_acc

val rev: list 'a -> Tot (list 'a)
let rev l = rev_acc l []
let revT = rev

val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y
let appendT = append

val flatten: list (list 'a) -> Tot (list 'a)
let rec flatten l = match l with
    | [] -> []
    | hd::tl -> append hd (flatten tl)
let flattenT = flatten
let concat = flatten
let concatT = flattenT


(** Iterators **)

val iter: ('a -> unit) -> list 'a -> unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl

val iterT: ('a -> Tot unit) -> list 'a -> Tot unit
let rec iterT f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iterT f tl

val map: ('a -> 'b) -> list 'a -> list 'b
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val mapT: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec mapT f x = match x with
  | [] -> []
  | a::tl -> f a::mapT f tl

val mapi_init: (int -> 'a -> 'b) -> list 'a -> int -> list 'b
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

val mapi_initT: (int -> 'a -> Tot 'b) -> list 'a -> int -> Tot (list 'b)
let rec mapi_initT f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_initT f tl (i+1))

val mapi: (int -> 'a -> 'b) -> list 'a -> list 'b
let mapi f l = mapi_init f l 0

val mapiT: (int -> 'a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapiT f l = mapi_initT f l 0

val concatMap: ('a -> list 'b) -> list 'a -> list 'b
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    append fa ftl

val concatMapT: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec concatMapT f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMapT f tl in
    appendT fa ftl

val map2: ('a -> 'b -> 'c) -> list 'a -> list 'b -> list 'c
let rec map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::(map2 f tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

val map3: ('a -> 'b -> 'c -> 'd) -> list 'a -> list 'b -> list 'c -> list 'd
let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::(map3 f tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"

val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_leftT: ('a -> 'b -> Tot 'a) -> 'a -> l:list 'b -> Tot 'a (decreases l)
let rec fold_leftT f x y = match y with
  | [] -> x
  | hd::tl -> fold_leftT f (f x hd) tl

val fold_left2: ('s -> 'a -> 'b -> 's) -> 's -> list 'a -> list 'b -> 's
let rec fold_left2 f a l1 l2 = match l1, l2 with
    | [], [] -> a
    | hd1::tl1, hd2::tl2 -> fold_left2 f (f a hd1 hd2) tl1 tl2
    | _, _ -> failwith "The lists do not have the same length"

val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

val fold_rightT: ('a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
let rec fold_rightT f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_rightT f tl x)


(** List searching **)

val mem: 'a -> list 'a -> Tot bool //x:'a -> l:list 'a -> b:bool{b==true <==> In x l}
let rec mem x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl
let memT = mem
let contains = mem
let containsT = memT

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
let findT = find

val filter: ('a -> bool) -> list 'a -> list 'a
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

val filterT: f:('a -> Tot bool) -> list 'a -> Tot (m:list 'a{forall x. mem x m ==> f x})
let rec filterT f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filterT f tl) else filterT f tl

val for_all: ('a -> bool) -> list 'a -> bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

val for_allT: ('a -> Tot bool) -> list 'a -> Tot bool
let rec for_allT f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_allT f tl else false

val forall2: ('a -> 'b -> bool) -> list 'a -> list 'b -> bool
let rec forall2 f l1 l2 = match l1,l2 with
    | [], [] -> true
    | hd1::tl1, hd2::tl2 -> if f hd1 hd2 then forall2 f tl1 tl2 else false
    | _, _ -> failwith "The lists do not have the same length"

val collect: ('a -> list 'b) -> list 'a -> list 'b
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

val collectT: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec collectT f l = match l with
    | [] -> []
    | hd::tl -> appendT (f hd) (collectT f tl)

val tryFind: ('a -> bool) -> list 'a -> option 'a
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

val tryFindT: ('a -> Tot bool) -> list 'a -> Tot (option 'a)
let rec tryFindT p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFindT p tl

val tryPick: ('a -> option 'b) -> list 'a -> option 'b
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

val tryPickT: ('a -> Tot (option 'b)) -> list 'a -> Tot (option 'b)
let rec tryPickT f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPickT f tl

val choose: ('a -> option 'b) -> list 'a -> list 'b
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

val chooseT: ('a -> Tot (option 'b)) -> list 'a -> Tot (list 'b)
let rec chooseT f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(chooseT f tl)
         | None -> chooseT f tl

val partition: ('a -> bool) -> list 'a -> (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

val partitionT: f:('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partitionT f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partitionT f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** List of tuples **)

val assoc: 'a -> list ('a*'b) -> Tot (option 'b)
let rec assoc a x = match x with
  | [] -> None
  | (a', b)::tl -> if a=a' then Some b else assoc a tl
let assocT = assoc

val split: list ('a * 'b) -> Tot (list 'a * list 'b)
let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)
let splitT = split
let unzip = split
let unzipT = splitT

val unzip3: list ('a * 'b * 'c) -> Tot (list 'a * list 'b * list 'c)
let rec unzip3 l = match l with
    | [] -> ([],[],[])
    | (hd1,hd2,hd3)::tl ->
       let (tl1,tl2,tl3) = unzip3 tl in
       (hd1::tl1,hd2::tl2,hd3::tl3)
let unzip3T = unzip3

val zip: list 'a -> list 'b -> list ('a * 'b)
let rec zip l1 l2 = match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

val zip3: list 'a -> list 'b -> list 'c -> list ('a * 'b * 'c)
let rec zip3 l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (hd1,hd2,hd3)::(zip3 tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"


(** Sorting (implemented as quicksort) **)

val sortWith: ('a -> 'a -> int) -> list 'a -> list 'a
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (fun x -> f pivot x > 0) tl in
     sortWith f lo@(pivot::sortWith f hi)

val partition_length: f:('a -> Tot bool)
                  -> l:list 'a
                  -> Lemma (requires True)
                           (ensures (length (fst (partitionT f l)) + length (snd (partitionT f l)) = length l))
let rec partition_length f l = match l with
  | [] -> ()
  | hd::tl -> partition_length f tl

val bool_of_compare : ('a -> 'a -> Tot int) -> 'a -> 'a -> Tot bool
let bool_of_compare f x y = f x y >= 0

val sortWithT: ('a -> 'a -> Tot int) -> l:list 'a -> Tot (list 'a) (decreases (length l))
let rec sortWithT f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partitionT (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     sortWithT f lo@(pivot::sortWithT f hi)
