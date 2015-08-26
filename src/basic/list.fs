#light "off"
module FStar.List
let isEmpty = (fun ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| _5_18 -> begin
false
end))

let isEmptyT = isEmpty

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

let tl = tail

let rec length = (fun ( _5_3  :  'a Prims.list ) -> (match (_5_3) with
| [] -> begin
0
end
| _5_37::tl -> begin
(1 + (length tl))
end))

let lengthT x = length x

let rec nth = fun ( l  :  'a Prims.list ) ( n  :  Prims.int ) ->
    if n < 0
    then failwith "nth takes a non-negative integer as input"
    else if n=0 then
        match (l) with
        | [] -> failwith "not enough elements"
        | hd::_ -> hd
    else match l with
        | [] ->  failwith "not enough elements"
        | _5_50::tl -> nth tl (n - 1)

let rec total_nth = (fun ( l  :  'a Prims.list ) ( n  :  Prims.nat ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((n = 0)) with
| true -> begin
Some (hd)
end
| false -> begin
(total_nth tl (n - 1))
end)
end))

let rec count = (fun ( x  :  'a ) ( _5_4  :  'a Prims.list ) -> (match (_5_4) with
| [] -> begin
0
end
| hd::tl -> begin
(match ((x = hd)) with
| true -> begin
(1 + (count x tl))
end
| false -> begin
(count x tl)
end)
end))

let countT x l = count x l

let rec rev_acc = (fun ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) -> (match (l) with
| [] -> begin
acc
end
| hd::tl -> begin
(rev_acc tl ((hd)::acc))
end))

let rev_append l a = rev_acc l a

let rev = (fun ( l  :  'a Prims.list ) -> (rev_acc l []))

let revT x = rev x

let rec append = (fun ( x  :  'a Prims.list ) ( y  :  'a Prims.list ) -> (match (x) with
| [] -> begin
y
end
| a::tl -> begin
(a)::(append tl y)
end))

let appendT x y = append x y

let rec flatten = (fun ( l  :  'a Prims.list Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append hd (flatten tl))
end))

let flattenT x = flatten x

let concat x = flatten x

let concatT x = flattenT x

let rec iter = (fun ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
()
end
| a::tl -> begin
(let _5_95 = (f a)
in (iter f tl))
end))

let rec iterT = (fun ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> ())

let rec map = (fun ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
((f a))::(map f tl)
end))

let rec mapT = (fun ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
((f a))::(mapT f tl)
end))

let rec mapi_init = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_init f tl (i + 1))
end))

let rec mapi_initT = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_initT f tl (i + 1))
end))

let mapi = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) -> (mapi_init f l 0))

let mapiT = (fun ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) -> (mapi_initT f l 0))

let rec concatMap = (fun ( f  :  'a  ->  'b Prims.list ) ( _5_5  :  'a Prims.list ) -> (match (_5_5) with
| [] -> begin
[]
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = (concatMap f tl)
in (append fa ftl)))
end))

let rec concatMapT = (fun ( f  :  'a  ->  'b Prims.list ) ( _5_6  :  'a Prims.list ) -> (match (_5_6) with
| [] -> begin
[]
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = (concatMapT f tl)
in (appendT fa ftl)))
end))

let rec map2 = (fun ( f  :  'a  ->  'b  ->  'c ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2) -> begin
((f hd1 hd2))::(map2 f tl1 tl2)
end
| (_5_185, _5_187) -> begin
(failwith "The lists do not have the same length")
end))

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

let rec fold_left = (fun ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b Prims.list ) -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(fold_left f (f x hd) tl)
end))

let rec fold_leftT = (fun ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b Prims.list ) -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(fold_leftT f (f x hd) tl)
end))

let rec fold_left2 = (fun ( f  :  's  ->  'a  ->  'b  ->  's ) ( a  :  's ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
a
end
| (hd1::tl1, hd2::tl2) -> begin
(fold_left2 f (f a hd1 hd2) tl1 tl2)
end
| (_5_255, _5_257) -> begin
(failwith "The lists do not have the same length")
end))

let rec fold_right = (fun ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a Prims.list ) ( x  :  'b ) -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd (fold_right f tl x))
end))

let rec fold_rightT = (fun ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a Prims.list ) ( x  :  'b ) -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd (fold_rightT f tl x))
end))

let rec mem = (fun ( x  :  'a ) ( _5_7  :  'a Prims.list ) -> (match (_5_7) with
| [] -> begin
false
end
| hd::tl -> begin
(match ((hd = x)) with
| true -> begin
true
end
| false -> begin
(mem x tl)
end)
end))

let memT x l = mem x l

let contains x l = mem x l

let containsT x l = memT x l

let rec existsb = (fun ( f  :  ' a  ->  Prims.bool ) ( l  :  ' a Prims.list ) -> (match (l) with
| [] -> begin
false
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
true
end
| false -> begin
(existsb f tl)
end)
end))

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

let findT f l = find f l

let rec filter = (fun ( f  :  'a  ->  Prims.bool ) ( _5_8  :  'a Prims.list ) -> (match (_5_8) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
(hd)::(filter f tl)
end
| false -> begin
(filter f tl)
end)
end))

let rec filterT = (fun ( f  :  'a  ->  Prims.bool ) ( _5_9  :  'a Prims.list ) -> (match (_5_9) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
(hd)::(filterT f tl)
end
| false -> begin
(filterT f tl)
end)
end))

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

let rec for_allT = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
(for_allT f tl)
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

let rec collect = (fun ( f  :  'a  ->  'b Prims.list ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append (f hd) (collect f tl))
end))

let rec collectT = (fun ( f  :  'a  ->  'b Prims.list ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(appendT (f hd) (collectT f tl))
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

let rec tryFindT = (fun ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((p hd)) with
| true -> begin
Some (hd)
end
| false -> begin
(tryFindT p tl)
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

let rec tryPickT = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
Some (x)
end
| None -> begin
(tryPickT f tl)
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

let rec chooseT = (fun ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(x)::(chooseT f tl)
end
| None -> begin
(chooseT f tl)
end)
end))

let rec partition = (fun ( f  :  'a  ->  Prims.bool ) ( _5_10  :  'a Prims.list ) -> (match (_5_10) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _5_439 = (partition f tl)
in (match (_5_439) with
| (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
((hd)::l1, l2)
end
| false -> begin
(l1, (hd)::l2)
end)
end))
end))

let rec partitionT = (fun ( f  :  'a  ->  Prims.bool ) ( _5_11  :  'a Prims.list ) -> (match (_5_11) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _5_450 = (partitionT f tl)
in (match (_5_450) with
| (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
((hd)::l1, l2)
end
| false -> begin
(l1, (hd)::l2)
end)
end))
end))

let rec assoc = (fun ( a  :  'a ) ( x  :  ('a * 'b) Prims.list ) -> (match (x) with
| [] -> begin
None
end
| (a', b)::tl -> begin
(match ((a = a')) with
| true -> begin
Some (b)
end
| false -> begin
(assoc a tl)
end)
end))

let assocT x l = assoc x l

let rec split = (fun ( l  :  ('a * 'b) Prims.list ) -> (match (l) with
| [] -> begin
([], [])
end
| (hd1, hd2)::tl -> begin
(let _5_472 = (split tl)
in (match (_5_472) with
| (tl1, tl2) -> begin
((hd1)::tl1, (hd2)::tl2)
end))
end))

let splitT x = split x

let unzip x = split x

let unzipT x = splitT x

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

let unzip3T x = unzip3 x

let rec zip = (fun ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match ((l1, l2)) with
| ([], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2) -> begin
((hd1, hd2))::(zip tl1 tl2)
end
| (_5_503, _5_505) -> begin
(failwith "The lists do not have the same length")
end))

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

let rec sortWith = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( _5_12  :  'a Prims.list ) -> (match (_5_12) with
| [] -> begin
[]
end
| pivot::tl -> begin
(let _5_544 = (partition (fun ( x  :  'a ) -> ((f pivot x) >= 0)) tl)
in (match (_5_544) with
| (lo, hi) -> begin
(append (sortWith f lo) ((pivot)::(sortWith f hi)))
end))
end))

let rec partition_length = (fun ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())

let bool_of_compare = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( x  :  'a ) ( y  :  'a ) -> ((f x y) >= 0))

let rec sortWithT = (fun ( f  :  'a  ->  'a  ->  Prims.int ) ( _5_13  :  'a Prims.list ) -> (match (_5_13) with
| [] -> begin
[]
end
| pivot::tl -> begin
(let _5_568 = (partitionT (bool_of_compare f pivot) tl)
in (match (_5_568) with
| (lo, hi) -> begin
(let _5_569 = ()
in (append (sortWithT f lo) ((pivot)::(sortWithT f hi))))
end))
end))




