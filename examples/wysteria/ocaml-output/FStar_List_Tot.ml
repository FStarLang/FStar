
open Prims
let isEmpty = (fun l -> (match (l) with
| [] -> begin
true
end
| _3_14 -> begin
false
end))

let hd = (fun _3_1 -> (match (_3_1) with
| hd::_3_20 -> begin
hd
end))

let tl = (fun _3_2 -> (match (_3_2) with
| _3_29::tl -> begin
tl
end))

let rec length = (fun _3_3 -> (match (_3_3) with
| [] -> begin
0
end
| _3_36::tl -> begin
(1 + (length tl))
end))

let rec nth = (fun l n -> (match (l) with
| [] -> begin
None
end
| hd::tl -> begin
if (n = 0) then begin
Some (hd)
end else begin
(nth tl (n - 1))
end
end))

let rec count = (fun x _3_4 -> (match (_3_4) with
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

let rec rev_acc = (fun l acc -> (match (l) with
| [] -> begin
acc
end
| hd::tl -> begin
(rev_acc tl ((hd)::acc))
end))

let rev = (fun l -> (rev_acc l []))

let rec append = (fun x y -> (match (x) with
| [] -> begin
y
end
| a::tl -> begin
(a)::(append tl y)
end))

let rec flatten = (fun l -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append hd (flatten tl))
end))

let rec iter = (fun f x -> ())

let rec map = (fun f x -> (match (x) with
| [] -> begin
[]
end
| a::tl -> begin
((f a))::(map f tl)
end))

let rec mapi_init = (fun f l i -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
((f i hd))::(mapi_init f tl (i + 1))
end))

let mapi = (fun f l -> (mapi_init f l 0))

let rec concatMap = (fun f _3_5 -> (match (_3_5) with
| [] -> begin
[]
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = (concatMap f tl)
in (append fa ftl)))
end))

let rec fold_left = (fun f x y -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(fold_left f (f x hd) tl)
end))

let rec fold_right = (fun f l x -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd (fold_right f tl x))
end))

let rec mem = (fun x _3_6 -> (match (_3_6) with
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

let contains = mem

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

let rec filter = (fun f _3_7 -> (match (_3_7) with
| [] -> begin
[]
end
| hd::tl -> begin
if (f hd) then begin
(hd)::(filter f tl)
end else begin
(filter f tl)
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

let rec collect = (fun f l -> (match (l) with
| [] -> begin
[]
end
| hd::tl -> begin
(append (f hd) (collect f tl))
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

let rec choose = (fun f l -> (match (l) with
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

let rec partition = (fun f _3_8 -> (match (_3_8) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _3_225 = (partition f tl)
in (match (_3_225) with
| (l1, l2) -> begin
if (f hd) then begin
((hd)::l1, l2)
end else begin
(l1, (hd)::l2)
end
end))
end))

let rec subset = (fun la lb -> (match (la) with
| [] -> begin
true
end
| h::tl -> begin
((mem h lb) && (subset tl lb))
end))

let rec noRepeats = (fun la -> (match (la) with
| [] -> begin
true
end
| h::tl -> begin
((not ((mem h tl))) && (noRepeats tl))
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

let rec split = (fun l -> (match (l) with
| [] -> begin
([], [])
end
| (hd1, hd2)::tl -> begin
(let _3_260 = (split tl)
in (match (_3_260) with
| (tl1, tl2) -> begin
((hd1)::tl1, (hd2)::tl2)
end))
end))

let unzip = split

let rec unzip3 = (fun l -> (match (l) with
| [] -> begin
([], [], [])
end
| (hd1, hd2, hd3)::tl -> begin
(let _3_275 = (unzip3 tl)
in (match (_3_275) with
| (tl1, tl2, tl3) -> begin
((hd1)::tl1, (hd2)::tl2, (hd3)::tl3)
end))
end))

let rec partition_length = (fun f l -> ())

let bool_of_compare = (fun f x y -> ((f x y) >= 0))

let rec sortWith = (fun f _3_9 -> (match (_3_9) with
| [] -> begin
[]
end
| pivot::tl -> begin
(let _3_299 = (partition (bool_of_compare f pivot) tl)
in (match (_3_299) with
| (hi, lo) -> begin
(let _3_300 = ()
in (append (sortWith f lo) ((pivot)::(sortWith f hi))))
end))
end))




