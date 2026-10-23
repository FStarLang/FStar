(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.List

(* The Cherry implementation.  Cherry turns only self tail calls into loops,
   so everything that walks a list builds its result in reverse and reverses
   it, and runs in constant stack as the OCaml implementation (Batteries)
   does.  Functions are applied to the elements from left to right. *)

open FStarC.Effect

(* The partial functions the interface declares total ([hd], [nth], [zip],
   ...) have no case for the inputs they are not defined on: the match is
   incomplete, which F* accepts only because the queries below are admitted,
   as they are when the compiler is built.  Cherry's debug mode reports such
   a call (cherry.md, "Debug mode"); a release build assumes it does not
   happen. *)
#set-options "--admit_smt_queries true"

let isEmpty l = match l with [] -> true | _ -> false

let singleton x = [x]

let hd l = match l with x :: _ -> x

private let rec length_acc (#a:Type) (l:list a) (n:nat) : Tot nat (decreases l) =
  match l with [] -> n | _ :: t -> length_acc t (n + 1)

let length l = length_acc l 0

let rec nth l i =
  match l with
  | x :: t -> if i = 0 then x else nth t (i - 1)

let rec rev_acc l acc = match l with [] -> acc | x :: t -> rev_acc t (x :: acc)

let rev l = rev_acc l []

let append l1 l2 = rev_acc (rev l1) l2

let ( @ ) l1 l2 = append l1 l2

private let rec flatten_acc (#a:Type) (ls:list (list a)) (acc:list a)
  : Tot (list a) (decreases ls) =
  match ls with [] -> rev acc | l :: t -> flatten_acc t (rev_acc l acc)

let flatten ls = flatten_acc ls []

let rec iter f l = match l with [] -> () | x :: t -> f x; iter f t

let rec iter2 f l1 l2 =
  match l1, l2 with
  | [], [] -> ()
  | x :: t1, y :: t2 -> f x y; iter2 f t1 t2
  | _, _ -> failwith "iter2: list lengths differ"

private let rec iteri_from (#a:Type) (f:int -> a -> ML unit) (i:int) (l:list a) : ML unit =
  match l with [] -> () | x :: t -> f i x; iteri_from f (i + 1) t

let iteri f l = iteri_from f 0 l

private let rec map_acc (#a #b:Type) (f:a -> ML b) (l:list a) (acc:list b) : ML (list b) =
  match l with [] -> rev acc | x :: t -> let y = f x in map_acc f t (y :: acc)

let map f l = map_acc f l []

private let rec mapi_acc (#a #b:Type) (f:int -> a -> ML b) (l:list a) (i:int) (acc:list b)
  : ML (list b) =
  match l with [] -> rev acc | x :: t -> let y = f i x in mapi_acc f t (i + 1) (y :: acc)

let mapi_init f l i = mapi_acc f l i []

let mapi f l = mapi_acc f l 0 []

private let rec collect_acc (#a #b:Type) (f:a -> ML (list b)) (l:list a) (acc:list b)
  : ML (list b) =
  match l with [] -> rev acc | x :: t -> let ys = f x in collect_acc f t (rev_acc ys acc)

let concatMap f l = collect_acc f l []

private let rec map2_acc (#a #b #c:Type) (f:a -> b -> ML c) (l1:list a) (l2:list b) (acc:list c)
  : ML (list c) =
  match l1, l2 with
  | [], [] -> rev acc
  | x :: t1, y :: t2 -> let z = f x y in map2_acc f t1 t2 (z :: acc)
  | _, _ -> failwith "map2: list lengths differ"

let map2 f l1 l2 = map2_acc f l1 l2 []

private let rec map3_acc (#a #b #c #d:Type) (f:a -> b -> c -> ML d)
  (l1:list a) (l2:list b) (l3:list c) (acc:list d) : ML (list d) =
  match l1, l2, l3 with
  | [], [], [] -> rev acc
  | x :: t1, y :: t2, z :: t3 -> let w = f x y z in map3_acc f t1 t2 t3 (w :: acc)
  | _, _, _ -> failwith "The lists do not have the same length"

let map3 f l1 l2 l3 = map3_acc f l1 l2 l3 []

let rec fold_left f a l = match l with [] -> a | x :: t -> fold_left f (f a x) t

let rec fold_left2 f s l1 l2 =
  match l1, l2 with
  | [], [] -> s
  | x :: t1, y :: t2 -> fold_left2 f (f s x y) t1 t2
  | _, _ -> failwith "fold_left2: list lengths differ"

let fold_right f l b = fold_left (fun b x -> f x b) b (rev l)

let fold_right2 f l1 l2 c =
  if length l1 <> length l2 then failwith "fold_right2: list lengths differ"
  else fold_left2 (fun c x y -> f x y c) c (rev l1) (rev l2)

let rev_map_onto f l acc = fold_left (fun acc x -> f x :: acc) acc l

let init l =
  match rev l with
  | _ :: t -> rev t

let rec last l =
  match l with
  | [x] -> x
  | _ :: t -> last t

let rec last_opt l =
  match l with
  | [] -> None
  | [x] -> Some x
  | _ :: t -> last_opt t

let rec existsb f l = match l with [] -> false | x :: t -> f x || existsb f t

let existsML f l = existsb f l

let rec find f l = match l with [] -> None | x :: t -> if f x then Some x else find f t

private let rec filter_acc (#a:Type) (f:a -> ML bool) (l:list a) (acc:list a) : ML (list a) =
  match l with [] -> rev acc | x :: t -> if f x then filter_acc f t (x :: acc) else filter_acc f t acc

let filter f l = filter_acc f l []

let rec for_all f l = match l with [] -> true | x :: t -> f x && for_all f t

let rec forall2 f l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | x :: t1, y :: t2 -> f x y && forall2 f t1 t2
  | _, _ -> failwith "forall2: list lengths differ"

let collect f l = collect_acc f l []

let tryFind f l = find f l

let rec tryPick f l =
  match l with
  | [] -> None
  | x :: t -> (match f x with Some y -> Some y | None -> tryPick f t)

private let rec choose_acc (#a #b:Type) (f:a -> ML (option b)) (l:list a) (acc:list b)
  : ML (list b) =
  match l with
  | [] -> rev acc
  | x :: t -> (match f x with Some y -> choose_acc f t (y :: acc) | None -> choose_acc f t acc)

let choose f l = choose_acc f l []

private let rec partition_acc (#a:Type) (f:a -> ML bool) (l:list a) (yes no:list a)
  : ML (list a & list a) =
  match l with
  | [] -> (rev yes, rev no)
  | x :: t -> if f x then partition_acc f t (x :: yes) no else partition_acc f t yes (x :: no)

let partition f l = partition_acc f l [] []

private let rec split_at_acc (#a:Type) (n:int) (l:list a) (acc:list a)
  : Tot (list a & list a) (decreases l) =
  if n = 0 then (rev acc, l)
  else match l with
       | x :: t -> split_at_acc (n - 1) t (x :: acc)

let splitAt n l = split_at_acc n l []

private let rec unzip_acc (#a #b:Type) (l:list (a & b)) (xs:list a) (ys:list b)
  : Tot (list a & list b) (decreases l) =
  match l with
  | [] -> (rev xs, rev ys)
  | (x, y) :: t -> unzip_acc t (x :: xs) (y :: ys)

let split l = unzip_acc l [] []

private let rec unzip3_acc (#a #b #c:Type) (l:list (a & b & c)) (xs:list a) (ys:list b) (zs:list c)
  : Tot (list a & list b & list c) (decreases l) =
  match l with
  | [] -> (rev xs, rev ys, rev zs)
  | (x, y, z) :: t -> unzip3_acc t (x :: xs) (y :: ys) (z :: zs)

let unzip3 l = unzip3_acc l [] [] []

private let rec zip_acc (#a #b:Type) (l1:list a) (l2:list b) (acc:list (a & b))
  : Tot (list (a & b)) (decreases l1) =
  match l1, l2 with
  | [], [] -> rev acc
  | x :: t1, y :: t2 -> zip_acc t1 t2 ((x, y) :: acc)

let zip l1 l2 = zip_acc l1 l2 []

private let rec zip3_acc (#a #b #c:Type) (l1:list a) (l2:list b) (l3:list c) (acc:list (a & b & c))
  : Tot (list (a & b & c)) (decreases l1) =
  match l1, l2, l3 with
  | [], [], [] -> rev acc
  | x :: t1, y :: t2, z :: t3 -> zip3_acc t1 t2 t3 ((x, y, z) :: acc)

let zip3 l1 l2 l3 = zip3_acc l1 l2 l3 []

(* A stable merge sort: of two equal elements, the one first in the input
   comes first, as OCaml's [List.sort] does. *)
private let rec merge_acc (#a:Type) (f:a -> a -> ML int) (l1 l2 acc:list a) : ML (list a) =
  match l1, l2 with
  | [], _ -> rev_acc acc l2
  | _, [] -> rev_acc acc l1
  | x :: t1, y :: t2 ->
    if f x y <= 0 then merge_acc f t1 l2 (x :: acc) else merge_acc f l1 t2 (y :: acc)

private let rec sort_n (#a:Type) (f:a -> a -> ML int) (n:int) (l:list a) : ML (list a) =
  if n <= 1 then l
  else
    let k = n / 2 in
    let (l1, l2) = splitAt k l in
    let l1 = sort_n f k l1 in
    let l2 = sort_n f (n - k) l2 in
    merge_acc f l1 l2 []

let sortWith f l = sort_n f (length l) l

let tail l = match l with _ :: t -> t

let tl l = match l with _ :: t -> t

let rev_append l1 l2 = rev_acc l1 l2

let concat ls = flatten_acc ls []

let unzip l = unzip_acc l [] []

let filter_map f l = choose_acc f l []

private let rec count_acc (#a:eqtype) (x:a) (l:list a) (n:nat) : Tot nat (decreases l) =
  match l with [] -> n | y :: t -> count_acc x t (if x = y then n + 1 else n)

let count x l = count_acc x l 0

let rec mem x l = match l with [] -> false | y :: t -> x = y || mem x t

let rec assoc x l =
  match l with
  | [] -> None
  | (y, v) :: t -> if x = y then Some v else assoc x t

let contains x l = mem x l

(* Of equal elements, the last is kept, as Batteries' [unique] does. *)
private let rec unique_acc (#a:eqtype) (l:list a) (acc:list a) : Tot (list a) (decreases l) =
  match l with
  | [] -> rev acc
  | x :: t -> if mem x t then unique_acc t acc else unique_acc t (x :: acc)

let unique l = unique_acc l []

private let rec index_from (#a:eqtype) (f:a -> bool) (l:list a) (i:int) : Tot int (decreases l) =
  match l with
  | x :: t -> if f x then i else index_from f t (i + 1)

let index f l = index_from f l 0

private let rec span_acc (#a:eqtype) (f:a -> bool) (l:list a) (acc:list a)
  : Tot (list a & list a) (decreases l) =
  match l with
  | x :: t -> if f x then span_acc f t (x :: acc) else (rev acc, l)
  | [] -> (rev acc, [])

let span f l = span_acc f l []

private let rec dedup_acc (#a:Type) (f:a -> a -> ML bool) (l:list a) (acc:list a) : ML (list a) =
  match l with
  | [] -> rev acc
  | x :: t -> if existsb (f x) t then dedup_acc f t acc else dedup_acc f t (x :: acc)

let deduplicate f s = dedup_acc f s []

private let rec fold_left_map_acc (#a #b #c:Type) (f:a -> b -> ML (a & c)) (s:a) (l:list b)
  (acc:list c) : ML (a & list c) =
  match l with
  | [] -> (s, rev acc)
  | x :: t -> let (s, y) = f s x in fold_left_map_acc f s t (y :: acc)

let fold_left_map f s l = fold_left_map_acc f s l []
