
open Prims

let isEmpty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____10 -> begin
false
end))


let hd = (fun uu___11_21 -> (match ((Obj.magic (uu___11_21))) with
| (hd)::uu____25 -> begin
hd
end))


let tl = (fun uu___12_37 -> (match ((Obj.magic (uu___12_37))) with
| (uu____40)::tl -> begin
tl
end))


let rec length = (fun uu___13_51 -> (match ((Obj.magic (uu___13_51))) with
| [] -> begin
(Prims.parse_int "0")
end
| (uu____53)::tl -> begin
((Prims.parse_int "1") + (length tl))
end))


let rec nth = (fun l n -> (match ((Obj.magic (l))) with
| [] -> begin
None
end
| (hd)::tl -> begin
(match ((n = (Prims.parse_int "0"))) with
| true -> begin
Some (hd)
end
| uu____81 -> begin
(nth tl (n - (Prims.parse_int "1")))
end)
end))


let rec count = (fun x uu___14_98 -> (match ((Obj.magic (uu___14_98))) with
| [] -> begin
(Prims.parse_int "0")
end
| (hd)::tl -> begin
(match ((x = hd)) with
| true -> begin
((Prims.parse_int "1") + (count x tl))
end
| uu____105 -> begin
(count x tl)
end)
end))


let rec rev_acc = (fun l acc -> (match ((Obj.magic (l))) with
| [] -> begin
acc
end
| (hd)::tl -> begin
(rev_acc tl ((hd)::acc))
end))


let rev = (fun l -> (rev_acc l []))


let rec append = (fun x y -> (match ((Obj.magic (x))) with
| [] -> begin
y
end
| (a)::tl -> begin
(a)::(append tl y)
end))


let op_At = (fun x y -> (append x y))


let rec flatten = (fun l -> (match ((Obj.magic (l))) with
| [] -> begin
[]
end
| (hd)::tl -> begin
(append hd (flatten tl))
end))


let rec iter = (fun f x -> ())


let rec map = (fun f x -> (match ((Obj.magic (x))) with
| [] -> begin
[]
end
| (a)::tl -> begin
((f a))::(map f tl)
end))


let rec mapi_init = (fun f l i -> (match ((Obj.magic (l))) with
| [] -> begin
[]
end
| (hd)::tl -> begin
((f i hd))::(mapi_init f tl (i + (Prims.parse_int "1")))
end))


let mapi = (fun f l -> (mapi_init f l (Prims.parse_int "0")))


let rec concatMap = (fun f uu___15_322 -> (match ((Obj.magic (uu___15_322))) with
| [] -> begin
[]
end
| (a)::tl -> begin
(

let fa = (f a)
in (

let ftl = (concatMap f tl)
in (append fa ftl)))
end))


let rec fold_left = (fun f x y -> (match ((Obj.magic (y))) with
| [] -> begin
x
end
| (hd)::tl -> begin
(fold_left f (f x hd) tl)
end))


let rec fold_right = (fun f l x -> (match ((Obj.magic (l))) with
| [] -> begin
x
end
| (hd)::tl -> begin
(f hd (fold_right f tl x))
end))


let rec mem = (fun x uu___16_414 -> (match ((Obj.magic (uu___16_414))) with
| [] -> begin
false
end
| (hd)::tl -> begin
(match ((hd = x)) with
| true -> begin
true
end
| uu____419 -> begin
(mem x tl)
end)
end))


let contains = (fun uu____429 -> mem)


let rec existsb = (fun f l -> (match ((Obj.magic (l))) with
| [] -> begin
false
end
| (hd)::tl -> begin
(match ((f hd)) with
| true -> begin
true
end
| uu____452 -> begin
(existsb f tl)
end)
end))


let rec find = (fun f l -> (match ((Obj.magic (l))) with
| [] -> begin
None
end
| (hd)::tl -> begin
(match ((f hd)) with
| true -> begin
Some (hd)
end
| uu____481 -> begin
(find f tl)
end)
end))


let rec filter = (fun f uu___17_500 -> (match ((Obj.magic (uu___17_500))) with
| [] -> begin
[]
end
| (hd)::tl -> begin
(match ((f hd)) with
| true -> begin
(hd)::(filter f tl)
end
| uu____510 -> begin
(filter f tl)
end)
end))


let rec for_all = (fun f l -> (match ((Obj.magic (l))) with
| [] -> begin
true
end
| (hd)::tl -> begin
(match ((f hd)) with
| true -> begin
(for_all f tl)
end
| uu____533 -> begin
false
end)
end))


let rec collect = (fun f l -> (match ((Obj.magic (l))) with
| [] -> begin
[]
end
| (hd)::tl -> begin
(append (f hd) (collect f tl))
end))


let rec tryFind = (fun p l -> (match ((Obj.magic (l))) with
| [] -> begin
None
end
| (hd)::tl -> begin
(match ((p hd)) with
| true -> begin
Some (hd)
end
| uu____585 -> begin
(tryFind p tl)
end)
end))


let rec tryPick = (fun f l -> (match ((Obj.magic (l))) with
| [] -> begin
None
end
| (hd)::tl -> begin
(match ((Obj.magic ((f hd)))) with
| Some (x) -> begin
Some (x)
end
| None -> begin
(tryPick f tl)
end)
end))


let rec choose = (fun f l -> (match ((Obj.magic (l))) with
| [] -> begin
[]
end
| (hd)::tl -> begin
(match ((Obj.magic ((f hd)))) with
| Some (x) -> begin
(x)::(choose f tl)
end
| None -> begin
(choose f tl)
end)
end))


let rec partition = (fun f uu___18_663 -> (match ((Obj.magic (uu___18_663))) with
| [] -> begin
([], [])
end
| (hd)::tl -> begin
(

let uu____672 = (partition f tl)
in (match ((Obj.magic (uu____672))) with
| (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
((hd)::l1, l2)
end
| uu____693 -> begin
(l1, (hd)::l2)
end)
end))
end))


let rec subset = (fun la lb -> (match ((Obj.magic (la))) with
| [] -> begin
true
end
| (h)::tl -> begin
((mem h lb) && (subset tl lb))
end))


let rec noRepeats = (fun la -> (match ((Obj.magic (la))) with
| [] -> begin
true
end
| (h)::tl -> begin
((not ((mem h tl))) && (noRepeats tl))
end))


let rec assoc = (fun x uu___19_744 -> (match ((Obj.magic (uu___19_744))) with
| [] -> begin
None
end
| ((x', y))::tl -> begin
(match ((x = x')) with
| true -> begin
Some (y)
end
| uu____759 -> begin
(assoc x tl)
end)
end))


let rec split = (fun l -> (match ((Obj.magic (l))) with
| [] -> begin
([], [])
end
| ((hd1, hd2))::tl -> begin
(

let uu____791 = (split tl)
in (match ((Obj.magic (uu____791))) with
| (tl1, tl2) -> begin
((hd1)::tl1, (hd2)::tl2)
end))
end))


let unzip = (fun uu____822 -> split)


let rec unzip3 = (fun l -> (match ((Obj.magic (l))) with
| [] -> begin
([], [], [])
end
| ((hd1, hd2, hd3))::tl -> begin
(

let uu____865 = (unzip3 tl)
in (match ((Obj.magic (uu____865))) with
| (tl1, tl2, tl3) -> begin
((hd1)::tl1, (hd2)::tl2, (hd3)::tl3)
end))
end))


let rec partition_length = (fun f l -> ())


let bool_of_compare = (fun f x y -> ((f x y) >= (Prims.parse_int "0")))


let rec sortWith = (fun f uu___20_958 -> (match ((Obj.magic (uu___20_958))) with
| [] -> begin
[]
end
| (pivot)::tl -> begin
(

let uu____967 = (partition (bool_of_compare f pivot) tl)
in (match ((Obj.magic (uu____967))) with
| (hi, lo) -> begin
(append (sortWith f lo) ((pivot)::(sortWith f hi)))
end))
end))




