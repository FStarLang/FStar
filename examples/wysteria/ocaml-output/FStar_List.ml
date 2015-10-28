
open Prims
let isEmpty = (fun l -> (match (l) with
| [] -> begin
true
end
| _8_18 -> begin
false
end))

let isEmptyT = isEmpty

let hd = (fun _8_1 -> (match (_8_1) with
| hd::tl -> begin
hd
end
| _8_25 -> begin
(FStar_All.failwith "head of empty list")
end))

let tail = (fun _8_2 -> (match (_8_2) with
| hd::tl -> begin
tl
end
| _8_31 -> begin
(FStar_All.failwith "tail of empty list")
end))

let tl = tail

let rec length = (fun _8_3 -> (match (_8_3) with
| [] -> begin
0
end
| _8_37::tl -> begin
(1 + (length tl))
end))

let lengthT = length

let rec nth = (fun l n -> if (n < 0) then begin
(FStar_All.failwith "nth takes a non-negative integer as input")
end else begin
if (n = 0) then begin
(match (l) with
| [] -> begin
(FStar_All.failwith "not enough elements")
end
| hd::_8_44 -> begin
hd
end)
end else begin
(match (l) with
| [] -> begin
(FStar_All.failwith "not enough elements")
end
| _8_50::tl -> begin
(nth tl (n - 1))
end)
end
end)

let rec total_nth = (fun l n -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (n = 0) then begin
Some (hd)
end else begin
(total_nth tl (n - 1))
end
end))

let rec count = (fun x _8_4 -> (match (_8_4) with
| [] -> begin
0
end
| hd::tl -> begin
if (x = hd) then begin
(1 + (count x tl))
end else begin
(count x tl)
end
end))

let countT = count

let rec rev_acc = (fun l acc -> (match (l) with
| [] -> begin
acc
end
| hd::tl -> begin
(rev_acc tl ((hd)::acc))
end))

let rev_append = rev_acc

let rev = (fun l -> (rev_acc l []))

let revT = rev

let rec append = (fun x y -> (match (x) with
| [] -> begin
y
end
| a::tl -> begin
(a)::(append tl y)
end))

let appendT = append

let rec flatten = (fun l -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append hd (flatten tl))
end))

let flattenT = flatten

let concat = flatten

let concatT = flattenT

let rec iter = (fun f x -> (match (x) with
| [] -> begin
()
end
| a::tl -> begin
(let _8_95 = (f a)
in (iter f tl))
end))

let rec iterT = (fun f x -> ())

let rec map = (fun f x -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
(let _36_46 = (f a)
in (let _36_45 = (map f tl)
in (_36_46)::_36_45))
end))

let rec mapT = (fun f x -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
((f a))::(mapT f tl)
end))

let rec mapi_init = (fun f l i -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(let _36_62 = (f i hd)
in (let _36_61 = (mapi_init f tl (i + 1))
in (_36_62)::_36_61))
end))

let rec mapi_initT = (fun f l i -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_initT f tl (i + 1))
end))

let mapi = (fun f l -> (mapi_init f l 0))

let mapiT = (fun f l -> (mapi_initT f l 0))

let rec concatMap = (fun f _8_5 -> (match (_8_5) with
| [] -> begin
[]
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = (concatMap f tl)
in (append fa ftl)))
end))

let rec concatMapT = (fun f _8_6 -> (match (_8_6) with
| [] -> begin
[]
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = (concatMapT f tl)
in (appendT fa ftl)))
end))

let rec map2 = (fun f l1 l2 -> (match ((l1, l2)) with
| ([], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2) -> begin
(let _36_108 = (f hd1 hd2)
in (let _36_107 = (map2 f tl1 tl2)
in (_36_108)::_36_107))
end
| (_8_185, _8_187) -> begin
(FStar_All.failwith "The lists do not have the same length")
end))

let rec map3 = (fun f l1 l2 l3 -> (match ((l1, l2, l3)) with
| ([], [], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
(let _36_123 = (f hd1 hd2 hd3)
in (let _36_122 = (map3 f tl1 tl2 tl3)
in (_36_123)::_36_122))
end
| (_8_212, _8_214, _8_216) -> begin
(FStar_All.failwith "The lists do not have the same length")
end))

let rec fold_left = (fun f x y -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(let _36_133 = (f x hd)
in (fold_left f _36_133 tl))
end))

let rec fold_leftT = (fun f x y -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(fold_leftT f (f x hd) tl)
end))

let rec fold_left2 = (fun f a l1 l2 -> (match ((l1, l2)) with
| ([], []) -> begin
a
end
| (hd1::tl1, hd2::tl2) -> begin
(let _36_156 = (f a hd1 hd2)
in (fold_left2 f _36_156 tl1 tl2))
end
| (_8_255, _8_257) -> begin
(FStar_All.failwith "The lists do not have the same length")
end))

let rec fold_right = (fun f l x -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(let _36_166 = (fold_right f tl x)
in (f hd _36_166))
end))

let rec fold_rightT = (fun f l x -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd (fold_rightT f tl x))
end))

let rec mem = (fun x _8_7 -> (match (_8_7) with
| [] -> begin
false
end
| hd::tl -> begin
if (hd = x) then begin
true
end else begin
(mem x tl)
end
end))

let memT = mem

let contains = mem

let containsT = memT

let rec existsb = (fun f l -> (match (l) with
| [] -> begin
false
end
| hd::tl -> begin
if (f hd) then begin
true
end else begin
(existsb f tl)
end
end))

let rec find = (fun f l -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (f hd) then begin
Some (hd)
end else begin
(find f tl)
end
end))

let findT = find

let rec filter = (fun f _8_8 -> (match (_8_8) with
| [] -> begin
[]
end
| hd::tl -> begin
if (f hd) then begin
(let _36_222 = (filter f tl)
in (hd)::_36_222)
end else begin
(filter f tl)
end
end))

let rec filterT = (fun f _8_9 -> (match (_8_9) with
| [] -> begin
[]
end
| hd::tl -> begin
if (f hd) then begin
(hd)::(filterT f tl)
end else begin
(filterT f tl)
end
end))

let rec for_all = (fun f l -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
if (f hd) then begin
(for_all f tl)
end else begin
false
end
end))

let rec for_allT = (fun f l -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
if (f hd) then begin
(for_allT f tl)
end else begin
false
end
end))

let rec forall2 = (fun f l1 l2 -> (match ((l1, l2)) with
| ([], []) -> begin
true
end
| (hd1::tl1, hd2::tl2) -> begin
if (f hd1 hd2) then begin
(forall2 f tl1 tl2)
end else begin
false
end
end
| (_8_352, _8_354) -> begin
(FStar_All.failwith "The lists do not have the same length")
end))

let rec collect = (fun f l -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(let _36_261 = (f hd)
in (let _36_260 = (collect f tl)
in (append _36_261 _36_260)))
end))

let rec collectT = (fun f l -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(appendT (f hd) (collectT f tl))
end))

let rec tryFind = (fun p l -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (p hd) then begin
Some (hd)
end else begin
(tryFind p tl)
end
end))

let rec tryFindT = (fun p l -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (p hd) then begin
Some (hd)
end else begin
(tryFindT p tl)
end
end))

let rec tryPick = (fun f l -> (match (l) with
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

let rec tryPickT = (fun f l -> (match (l) with
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

let rec choose = (fun f l -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(let _36_292 = (choose f tl)
in (x)::_36_292)
end
| None -> begin
(choose f tl)
end)
end))

let rec chooseT = (fun f l -> (match (l) with
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

let rec partition = (fun f _8_10 -> (match (_8_10) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _8_439 = (partition f tl)
in (match (_8_439) with
| (l1, l2) -> begin
if (f hd) then begin
((hd)::l1, l2)
end else begin
(l1, (hd)::l2)
end
end))
end))

let rec partitionT = (fun f _8_11 -> (match (_8_11) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _8_450 = (partitionT f tl)
in (match (_8_450) with
| (l1, l2) -> begin
if (f hd) then begin
((hd)::l1, l2)
end else begin
(l1, (hd)::l2)
end
end))
end))

let rec assoc = (fun a x -> (match (x) with
| [] -> begin
None
end
| (a', b)::tl -> begin
if (a = a') then begin
Some (b)
end else begin
(assoc a tl)
end
end))

let assocT = assoc

let rec split = (fun l -> (match (l) with
| [] -> begin
([], [])
end
| (hd1, hd2)::tl -> begin
(let _8_472 = (split tl)
in (match (_8_472) with
| (tl1, tl2) -> begin
((hd1)::tl1, (hd2)::tl2)
end))
end))

let splitT = split

let unzip = split

let unzipT = splitT

let rec unzip3 = (fun l -> (match (l) with
| [] -> begin
([], [], [])
end
| (hd1, hd2, hd3)::tl -> begin
(let _8_487 = (unzip3 tl)
in (match (_8_487) with
| (tl1, tl2, tl3) -> begin
((hd1)::tl1, (hd2)::tl2, (hd3)::tl3)
end))
end))

let unzip3T = unzip3

let rec zip = (fun l1 l2 -> (match ((l1, l2)) with
| ([], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2) -> begin
(let _36_320 = (zip tl1 tl2)
in ((hd1, hd2))::_36_320)
end
| (_8_503, _8_505) -> begin
(FStar_All.failwith "The lists do not have the same length")
end))

let rec zip3 = (fun l1 l2 l3 -> (match ((l1, l2, l3)) with
| ([], [], []) -> begin
[]
end
| (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
(let _36_324 = (zip3 tl1 tl2 tl3)
in ((hd1, hd2, hd3))::_36_324)
end
| (_8_528, _8_530, _8_532) -> begin
(FStar_All.failwith "The lists do not have the same length")
end))

let rec sortWith = (fun f _8_12 -> (match (_8_12) with
| [] -> begin
[]
end
| pivot::tl -> begin
(let _8_544 = (partition (fun x -> ((f pivot x) > 0)) tl)
in (match (_8_544) with
| (hi, lo) -> begin
(let _36_336 = (sortWith f lo)
in (let _36_335 = (let _36_334 = (sortWith f hi)
in (pivot)::_36_334)
in (append _36_336 _36_335)))
end))
end))

let rec partition_length = (fun f l -> ())

let bool_of_compare = (fun f x y -> ((f x y) >= 0))

let rec sortWithT = (fun f _8_13 -> (match (_8_13) with
| [] -> begin
[]
end
| pivot::tl -> begin
(let _8_568 = (partitionT (bool_of_compare f pivot) tl)
in (match (_8_568) with
| (hi, lo) -> begin
(let _8_569 = ()
in (append (sortWithT f lo) ((pivot)::(sortWithT f hi))))
end))
end))




