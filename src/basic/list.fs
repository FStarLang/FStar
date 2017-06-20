#light "off"
module FStar.List
open FSharp.Compatibility.OCaml
let isEmpty = (fun ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| _5_18 -> begin
false
end))

let hd = (fun ( _5_1  :  'a Prims.list ) -> (match (_5_1) with
| hd::tl -> begin
hd
end
| _5_25 -> begin
(failwith "head of empty list")
end))

let tail = (fun ( _5_2  :  ' _5_1218 Prims.list ) -> (match (_5_2) with
| hd::tl -> begin
tl
end
| _5_31 -> begin
(failwith "tail of empty list")
end))

let tl x = tail x

let rec length = (fun ( _5_3  :  'a Prims.list ) -> (match (_5_3) with
| [] -> begin
Prims.parse_int "0"
end
| _5_37::tl -> begin
(Prims.parse_int "1" + (length tl))
end))

let rec nth = fun ( l  :  'a Prims.list ) ( n  :  Prims.int ) ->
    if n < Prims.parse_int "0"
    then failwith "nth takes a non-negative integer as input"
    else if n= Prims.parse_int "0"then
        match (l) with
        | [] -> failwith "not enough elements"
        | hd::_ -> hd
    else match l with
        | [] ->  failwith "not enough elements"
        | _5_50::tl -> nth tl (n - Prims.parse_int "1")

let rec count = (fun ( x  :  'a ) ( _5_4  :  'a Prims.list ) -> (match (_5_4) with
| [] -> begin
Prims.parse_int "0"
end
| hd::tl -> begin
(match ((x = hd)) with
| true -> begin
(Prims.parse_int "1" + (count x tl))
end
| false -> begin
(count x tl)
end)
end))

let rec rev_acc = (fun ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) -> (match (l) with
| [] -> begin
acc
end
| hd::tl -> begin
(rev_acc tl ((hd)::acc))
end))

let rev_append l a = rev_acc l a

let rev = (fun ( l  :  'a Prims.list ) -> (rev_acc l []))

let append x y = List.append x y

let flatten (l:('a Prims.list) Prims.list) = List.flatten l

let concat (x:('a Prims.list) Prims.list)  = flatten x

let rec iter = (fun ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
()
end
| a::tl -> begin
(let _5_95 = (f a)
in (iter f tl))
end))

let rec iter2 f l m = match l, m with
    | [], [] -> ()
    | x::l, y::m -> f x y; iter2 f l m
    | _ -> failwith "iter2: unequal list lengths"

let map = (fun ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> List.map f x)

let rec mapi_init = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_init f tl (i + Prims.parse_int "1"))
end))

let mapi f l = List.mapi (fun i x -> f (Prims.of_int i) x) l

let concatMap f l = List.collect f l

let collect f l = List.collect f l

let map2 f l1 l2 = List.map2 f l1 l2

let rec map3 = (fun ( f  :  'a  ->  'b  ->  'c  ->  'd ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) ( l3  :  'c Prims.list ) -> (match ((l1, l2, l3)) with
| ([], [], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
((f hd1 hd2 hd3))::(map3 f tl1 tl2 tl3)
end
| (_5_212, _5_214, _5_216) -> begin
(failwith "The lists do not have the same length")
end))

let fold_left f x y = List.fold_left f x y

let fold_left2 f a x y = List.fold_left2 f a x y

let fold_right f x a = List.fold_right f x a

let fold_right2 f x y a = List.fold_right2 f x y a

let mem x l = List.mem x l

let contains x l = mem x l

let existsb f l = List.exists f l
let existsML f l = List.exists f l

let rec find = (fun ( f  :  ' a  ->  Prims.bool ) ( l  :  ' a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
Some (hd)
end
| false -> begin
(find f tl)
end)
end))

let filter f l = List.filter f l

let rec for_all = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
(for_all f tl)
end
| false -> begin
false
end)
end))

let rec forall2 = (fun ( f  :  'a  ->  'b  ->  Prims.bool ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
true
end
| (hd1::tl1, hd2::tl2) -> begin
(match ((f hd1 hd2)) with
| true -> begin
(forall2 f tl1 tl2)
end
| false -> begin
false
end)
end
| (_5_352, _5_354) -> begin
(failwith "The lists do not have the same length")
end))


let rec tryFind = (fun ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((p hd)) with
| true -> begin
Some (hd)
end
| false -> begin
(tryFind p tl)
end)
end))

let rec tryPick = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
Some (x)
end
| None -> begin
(tryPick f tl)
end)
end))

let rec choose = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(x)::(choose f tl)
end
| None -> begin
(choose f tl)
end)
end))

let partition f l = List.partition f l

let rec assoc = fun ( a  :  'a ) ( x  :  ('a * 'b) Prims.list ) ->
 match (x) with
 | [] -> None
 | (a', b)::tl ->
   if (a = a')
   then Some b
   else assoc a tl

let splitAt (n:Prims.int) l = List.splitAt (Prims.parse_int32(Prims.to_string n)) l

let split l = List.split l

let unzip x = split x

let rec unzip3 = (fun ( l  :  ('a * 'b * 'c) Prims.list ) -> (match (l) with
| [] -> begin
([], [], [])
end
| (hd1, hd2, hd3)::tl -> begin
(let _5_487 = (unzip3 tl)
in (match (_5_487) with
| (tl1, tl2, tl3) -> begin
((hd1)::tl1, (hd2)::tl2, (hd3)::tl3)
end))
end))

let zip l1 l2 = List.zip l1 l2

let rec zip3 = (fun ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) ( l3  :  'c Prims.list ) -> (match ((l1, l2, l3)) with
| ([], [], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
((hd1, hd2, hd3))::(zip3 tl1 tl2 tl3)
end
| (_5_528, _5_530, _5_532) -> begin
(failwith "The lists do not have the same length")
end))
 
let sortFunction = (fun  ( f  :  'a  ->  'a  ->  Prims.int ) ( x  :  'a ) ( y  :  'a )  -> Prims.to_int (f x y))
let sortWith f l = List.sortWith (sortFunction f) l

let bool_of_compare = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( x  :  'a ) ( y  :  'a ) -> ((f x y) >= Prims.parse_int "0"))

let rec unique l =
  // this matches the semantics of BatList.unique.
  match l with
  | [] -> []
  | h::t ->
    if mem h t then
      unique t
    else
      h::(unique t)

let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+ Prims.parse_int "1") f tl
let iteri f x = iteri_aux (Prims.parse_int "0") f x

let filter_map f l =
  let rec filter_map acc l =
    match l with
    | [] ->
        rev acc
    | hd :: tl ->
        match f hd with
        | Some hd ->
            filter_map (hd :: acc) tl
        | None ->
            filter_map acc tl
  in
  filter_map [] l

let index f l = Prims.of_int (List.findIndex f l)
