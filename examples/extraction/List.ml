
let isEmpty = (fun ( _1_7758  :  Prims.unit ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
true
end
| _ -> begin
false
end))

let isEmptyT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> isEmpty))

let hd = (fun ( _1_7758  :  Prims.unit ) -> (fun ( _1_1  :  '_1_687 Prims.list ) -> (match (_1_1) with
| Prims.Cons (hd, tl) -> begin
hd
end
| _ -> begin
(Obj.magic (Prims.failwith (Obj.magic "head of empty list")))
end)))

let tail = (fun ( _1_7758  :  Prims.unit ) -> (fun ( _1_2  :  '_1_758 Prims.list ) -> (match (_1_2) with
| Prims.Cons (hd, tl) -> begin
tl
end
| _ -> begin
(Obj.magic (Prims.failwith (Obj.magic "tail of empty list")))
end)))

let tl = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> tail))

let rec length = (fun ( _1_7758  :  Prims.unit ) ( _1_3  :  'a Prims.list ) -> (match (_1_3) with
| Prims.Nil -> begin
(Obj.magic 0)
end
| Prims.Cons (_, tl) -> begin
(Obj.magic (Prims.op_Addition 1 (Obj.magic (length (Obj.magic tl)))))
end))

let lengthT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> length))

let rec nth = (fun ( _1_7758  :  Prims.unit ) ( l  :  'a Prims.list ) ( n  :  Prims.int ) -> (match ((Prims.op_LessThan n 0)) with
| true -> begin
(Obj.magic (Prims.failwith (Obj.magic "nth takes a non-negative integer as input")))
end
| false -> begin
(match ((Prims.op_Equality (Obj.magic n) 0)) with
| true -> begin
(match (l) with
| Prims.Nil -> begin
(Obj.magic (Prims.failwith (Obj.magic "not enough elements")))
end
| Prims.Cons (hd, _) -> begin
hd
end)
end
| false -> begin
(match (l) with
| Prims.Nil -> begin
(Obj.magic (Prims.failwith (Obj.magic "not enough elements")))
end
| Prims.Cons (_, tl) -> begin
(Obj.magic (nth (Obj.magic tl) (Obj.magic n)))
end)
end)
end))

let rec total_nth = (fun ( _1_7758  :  Prims.unit ) ( l  :  'a Prims.list ) ( n  :  Prims.nat ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (hd, tl) -> begin
(match ((Prims.op_Equality (Obj.magic n) 0)) with
| true -> begin
Prims.Some (hd)
end
| false -> begin
(Obj.magic (total_nth (Obj.magic tl) (Obj.magic (Prims.op_Subtraction (Obj.magic n) 1))))
end)
end))

let rec count = (fun ( _1_7758  :  Prims.unit ) ( x  :  'a ) ( _1_4  :  'a Prims.list ) -> (match (_1_4) with
| Prims.Nil -> begin
(Obj.magic 0)
end
| Prims.Cons (hd, tl) -> begin
(match ((Prims.op_Equality (Obj.magic x) hd)) with
| true -> begin
(Obj.magic (Prims.op_Addition 1 (Obj.magic (count (Obj.magic x) (Obj.magic tl)))))
end
| false -> begin
(Obj.magic (count (Obj.magic x) (Obj.magic tl)))
end)
end))

let countT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> count))

let rec rev_acc = (fun ( _1_7758  :  Prims.unit ) ( l  :  'a Prims.list ) ( acc  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
acc
end
| Prims.Cons (hd, tl) -> begin
(Obj.magic (rev_acc (Obj.magic tl) (Prims.Cons (hd, acc))))
end))

let rev_append = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> rev_acc))

let rev = (Obj.magic (fun ( _1_7758  :  Prims.unit ) ( l  :  'a Prims.list ) -> (rev_acc (Obj.magic l) Prims.l__Nil)))

let revT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> rev))

let rec append = (fun ( _1_7758  :  Prims.unit ) ( x  :  'a Prims.list ) ( y  :  'a Prims.list ) -> (match (x) with
| Prims.Nil -> begin
y
end
| Prims.Cons (a, tl) -> begin
Prims.Cons (a, (Obj.magic (append (Obj.magic tl) y)))
end))

let appendT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> append))

let rec flatten = (fun ( _1_7758  :  Prims.unit ) ( l  :  'a Prims.list Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(Obj.magic (append (Obj.magic hd) (Obj.magic (flatten (Obj.magic tl)))))
end))

let flattenT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> flatten))

let concat = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> flatten))

let concatT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> flattenT))

let rec iter = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> (match (x) with
| Prims.Nil -> begin
()
end
| Prims.Cons (a, tl) -> begin
(Obj.magic (let _1_94 = (f a)
in (iter (Obj.magic f) (Obj.magic tl))))
end))

let rec iterT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.unit ) ( x  :  'a Prims.list ) -> ())

let rec map = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> (match (x) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (a, tl) -> begin
(let _1_8818 = (f a)
in (let _1_8817 = (Obj.magic (map (Obj.magic f) (Obj.magic tl)))
in Prims.Cons (_1_8818, _1_8817)))
end))

let rec mapT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b ) ( x  :  'a Prims.list ) -> (match (x) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (a, tl) -> begin
Prims.Cons ((f a), (Obj.magic (mapT (Obj.magic f) (Obj.magic tl))))
end))

let rec mapi_init = (fun ( _1_7758  :  Prims.unit ) ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(let _1_8836 = (f i hd)
in (let _1_8835 = (Obj.magic (mapi_init (Obj.magic f) (Obj.magic tl) (Obj.magic (Prims.op_Addition i 1))))
in Prims.Cons (_1_8836, _1_8835)))
end))

let rec mapi_initT = (fun ( _1_7758  :  Prims.unit ) ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) ( i  :  Prims.int ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
Prims.Cons ((f i hd), (Obj.magic (mapi_initT (Obj.magic f) (Obj.magic tl) (Obj.magic (Prims.op_Addition i 1)))))
end))

let mapi = (Obj.magic (fun ( _1_7758  :  Prims.unit ) ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) -> (mapi_init (Obj.magic f) (Obj.magic l) (Obj.magic 0))))

let mapiT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) ( f  :  Prims.int  ->  'a  ->  'b ) ( l  :  'a Prims.list ) -> (mapi_initT (Obj.magic f) (Obj.magic l) (Obj.magic 0))))

let rec concatMap = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.list ) ( _1_5  :  'a Prims.list ) -> (match (_1_5) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (a, tl) -> begin
(Obj.magic (let fa = (f a)
in (let ftl = (Obj.magic (concatMap (Obj.magic f) (Obj.magic tl)))
in (append (Obj.magic fa) ftl))))
end))

let rec concatMapT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.list ) ( _1_6  :  'a Prims.list ) -> (match (_1_6) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (a, tl) -> begin
(Obj.magic (let fa = (f a)
in (let ftl = (Obj.magic (concatMapT (Obj.magic f) (Obj.magic tl)))
in (appendT (Obj.magic fa) ftl))))
end))

let rec map2 = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  'c ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match (Prims.MkTuple2 (l1, l2)) with
| Prims.MkTuple2 (Prims.Nil, Prims.Nil) -> begin
Prims.l__Nil
end
| Prims.MkTuple2 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2)) -> begin
(let _1_8888 = (f hd1 hd2)
in (let _1_8887 = (Obj.magic (map2 (Obj.magic f) (Obj.magic tl1) (Obj.magic tl2)))
in Prims.Cons (_1_8888, _1_8887)))
end
| Prims.MkTuple2 (_, _) -> begin
(Obj.magic (Prims.failwith (Obj.magic "The lists do not have the same length")))
end))

let rec map3 = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  'c  ->  'd ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) ( l3  :  'c Prims.list ) -> (match (Prims.MkTuple3 (l1, l2, l3)) with
| Prims.MkTuple3 (Prims.Nil, Prims.Nil, Prims.Nil) -> begin
Prims.l__Nil
end
| Prims.MkTuple3 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2), Prims.Cons (hd3, tl3)) -> begin
(let _1_8904 = (f hd1 hd2 hd3)
in (let _1_8903 = (Obj.magic (map3 (Obj.magic f) (Obj.magic tl1) (Obj.magic tl2) (Obj.magic tl3)))
in Prims.Cons (_1_8904, _1_8903)))
end
| Prims.MkTuple3 (_, _, _) -> begin
(Obj.magic (Prims.failwith (Obj.magic "The lists do not have the same length")))
end))

let rec fold_left = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b Prims.list ) -> (match (y) with
| Prims.Nil -> begin
x
end
| Prims.Cons (hd, tl) -> begin
(Obj.magic (let _1_8915 = (Obj.magic (f x hd))
in (fold_left (Obj.magic f) _1_8915 (Obj.magic tl))))
end))

let rec fold_leftT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b Prims.list ) -> (match (y) with
| Prims.Nil -> begin
x
end
| Prims.Cons (hd, tl) -> begin
(Obj.magic (fold_leftT (Obj.magic f) (Obj.magic (f x hd)) (Obj.magic tl)))
end))

let rec fold_left2 = (fun ( _1_7758  :  Prims.unit ) ( f  :  's  ->  'a  ->  'b  ->  's ) ( a  :  's ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match (Prims.MkTuple2 (l1, l2)) with
| Prims.MkTuple2 (Prims.Nil, Prims.Nil) -> begin
a
end
| Prims.MkTuple2 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2)) -> begin
(Obj.magic (let _1_8940 = (Obj.magic (f a hd1 hd2))
in (fold_left2 (Obj.magic f) _1_8940 (Obj.magic tl1) (Obj.magic tl2))))
end
| Prims.MkTuple2 (_, _) -> begin
(Obj.magic (Prims.failwith (Obj.magic "The lists do not have the same length")))
end))

let rec fold_right = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a Prims.list ) ( x  :  'b ) -> (match (l) with
| Prims.Nil -> begin
x
end
| Prims.Cons (hd, tl) -> begin
(let _1_8951 = (Obj.magic (fold_right (Obj.magic f) (Obj.magic tl) (Obj.magic x)))
in (f hd _1_8951))
end))

let rec fold_rightT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a Prims.list ) ( x  :  'b ) -> (match (l) with
| Prims.Nil -> begin
x
end
| Prims.Cons (hd, tl) -> begin
(f hd (Obj.magic (fold_rightT (Obj.magic f) (Obj.magic tl) (Obj.magic x))))
end))

let rec mem = (fun ( _1_7758  :  Prims.unit ) ( x  :  'a ) ( _1_7  :  'a Prims.list ) -> (match (_1_7) with
| Prims.Nil -> begin
false
end
| Prims.Cons (hd, tl) -> begin
(match ((Prims.op_Equality (Obj.magic hd) x)) with
| true -> begin
true
end
| false -> begin
(Obj.magic (mem (Obj.magic x) (Obj.magic tl)))
end)
end))

let memT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> mem))

let contains = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> mem))

let containsT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> memT))

let rec existsb = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
false
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| true -> begin
true
end
| false -> begin
(Obj.magic (existsb (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec find = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| true -> begin
Prims.Some (hd)
end
| false -> begin
(Obj.magic (find (Obj.magic f) (Obj.magic tl)))
end)
end))

let findT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> find))

let rec filter = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( _1_8  :  'a Prims.list ) -> (match (_1_8) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| true -> begin
(let _1_9018 = (Obj.magic (filter (Obj.magic f) (Obj.magic tl)))
in Prims.Cons (hd, _1_9018))
end
| false -> begin
(Obj.magic (filter (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec filterT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( _1_9  :  'a Prims.list ) -> (match (_1_9) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| true -> begin
Prims.Cons (hd, (Obj.magic (filterT (Obj.magic f) (Obj.magic tl))))
end
| false -> begin
(Obj.magic (filterT (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec for_all = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
true
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| true -> begin
(Obj.magic (for_all (Obj.magic f) (Obj.magic tl)))
end
| false -> begin
false
end)
end))

let rec for_allT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
true
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| true -> begin
(Obj.magic (for_allT (Obj.magic f) (Obj.magic tl)))
end
| false -> begin
false
end)
end))

let rec forall2 = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b  ->  Prims.bool ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match (Prims.MkTuple2 (l1, l2)) with
| Prims.MkTuple2 (Prims.Nil, Prims.Nil) -> begin
true
end
| Prims.MkTuple2 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2)) -> begin
(match ((f hd1 hd2)) with
| true -> begin
(Obj.magic (forall2 (Obj.magic f) (Obj.magic tl1) (Obj.magic tl2)))
end
| false -> begin
false
end)
end
| Prims.MkTuple2 (_, _) -> begin
(Obj.magic (Prims.failwith (Obj.magic "The lists do not have the same length")))
end))

let rec collect = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.list ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(Obj.magic (let _1_9062 = (Obj.magic (f hd))
in (let _1_9061 = (Obj.magic (collect (Obj.magic f) (Obj.magic tl)))
in (append _1_9062 _1_9061))))
end))

let rec collectT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.list ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(Obj.magic (appendT (Obj.magic (f hd)) (Obj.magic (collectT (Obj.magic f) (Obj.magic tl)))))
end))

let rec tryFind = (fun ( _1_7758  :  Prims.unit ) ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (hd, tl) -> begin
(match ((p hd)) with
| true -> begin
Prims.Some (hd)
end
| false -> begin
(Obj.magic (tryFind (Obj.magic p) (Obj.magic tl)))
end)
end))

let rec tryFindT = (fun ( _1_7758  :  Prims.unit ) ( p  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (hd, tl) -> begin
(match ((p hd)) with
| true -> begin
Prims.Some (hd)
end
| false -> begin
(Obj.magic (tryFindT (Obj.magic p) (Obj.magic tl)))
end)
end))

let rec tryPick = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| Prims.Some (x) -> begin
Prims.Some (x)
end
| Prims.None -> begin
(Obj.magic (tryPick (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec tryPickT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| Prims.Some (x) -> begin
Prims.Some (x)
end
| Prims.None -> begin
(Obj.magic (tryPickT (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec choose = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| Prims.Some (x) -> begin
(let _1_9099 = (Obj.magic (choose (Obj.magic f) (Obj.magic tl)))
in Prims.Cons (x, _1_9099))
end
| Prims.None -> begin
(Obj.magic (choose (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec chooseT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'b Prims.option ) ( l  :  'a Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (hd, tl) -> begin
(match ((f hd)) with
| Prims.Some (x) -> begin
Prims.Cons (x, (Obj.magic (chooseT (Obj.magic f) (Obj.magic tl))))
end
| Prims.None -> begin
(Obj.magic (chooseT (Obj.magic f) (Obj.magic tl)))
end)
end))

let rec partition = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( _1_10  :  'a Prims.list ) -> (match (_1_10) with
| Prims.Nil -> begin
Prims.MkTuple2 (Prims.l__Nil, Prims.l__Nil)
end
| Prims.Cons (hd, tl) -> begin
(let _1_438 = (Obj.magic (partition (Obj.magic f) (Obj.magic tl)))
in (match (_1_438) with
| Prims.MkTuple2 (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
Prims.MkTuple2 (Prims.Cons (hd, l1), l2)
end
| false -> begin
Prims.MkTuple2 (l1, Prims.Cons (hd, l2))
end)
end))
end))

let rec partitionT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( _1_11  :  'a Prims.list ) -> (match (_1_11) with
| Prims.Nil -> begin
Prims.MkTuple2 (Prims.l__Nil, Prims.l__Nil)
end
| Prims.Cons (hd, tl) -> begin
(let _1_449 = (Obj.magic (partitionT (Obj.magic f) (Obj.magic tl)))
in (match (_1_449) with
| Prims.MkTuple2 (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
Prims.MkTuple2 (Prims.Cons (hd, l1), l2)
end
| false -> begin
Prims.MkTuple2 (l1, Prims.Cons (hd, l2))
end)
end))
end))

let rec assoc = (fun ( _1_7758  :  Prims.unit ) ( a  :  'a ) ( x  :  ('a, 'b) Prims.l__Tuple2 Prims.list ) -> (match (x) with
| Prims.Nil -> begin
Prims.l__None
end
| Prims.Cons (Prims.MkTuple2 (a', b), tl) -> begin
(match ((Prims.op_Equality (Obj.magic a) a')) with
| true -> begin
Prims.Some (b)
end
| false -> begin
(Obj.magic (assoc (Obj.magic a) (Obj.magic tl)))
end)
end))

let assocT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> assoc))

let rec split = (fun ( _1_7758  :  Prims.unit ) ( l  :  ('a, 'b) Prims.l__Tuple2 Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.MkTuple2 (Prims.l__Nil, Prims.l__Nil)
end
| Prims.Cons (Prims.MkTuple2 (hd1, hd2), tl) -> begin
(let _1_471 = (Obj.magic (split (Obj.magic tl)))
in (match (_1_471) with
| Prims.MkTuple2 (tl1, tl2) -> begin
Prims.MkTuple2 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2))
end))
end))

let splitT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> split))

let unzip = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> split))

let unzipT = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> splitT))

let rec unzip3 = (fun ( _1_7758  :  Prims.unit ) ( l  :  ('a, 'b, 'c) Prims.l__Tuple3 Prims.list ) -> (match (l) with
| Prims.Nil -> begin
Prims.MkTuple3 (Prims.l__Nil, Prims.l__Nil, Prims.l__Nil)
end
| Prims.Cons (Prims.MkTuple3 (hd1, hd2, hd3), tl) -> begin
(let _1_486 = (Obj.magic (unzip3 (Obj.magic tl)))
in (match (_1_486) with
| Prims.MkTuple3 (tl1, tl2, tl3) -> begin
Prims.MkTuple3 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2), Prims.Cons (hd3, tl3))
end))
end))

let unzip3T = (Obj.magic (fun ( _1_7758  :  Prims.unit ) -> unzip3))

let rec zip = (fun ( _1_7758  :  Prims.unit ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) -> (match (Prims.MkTuple2 (l1, l2)) with
| Prims.MkTuple2 (Prims.Nil, Prims.Nil) -> begin
Prims.l__Nil
end
| Prims.MkTuple2 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2)) -> begin
(let _1_9139 = (Obj.magic (zip (Obj.magic tl1) (Obj.magic tl2)))
in Prims.Cons (Prims.MkTuple2 (hd1, hd2), _1_9139))
end
| Prims.MkTuple2 (_, _) -> begin
(Obj.magic (Prims.failwith (Obj.magic "The lists do not have the same length")))
end))

let rec zip3 = (fun ( _1_7758  :  Prims.unit ) ( l1  :  'a Prims.list ) ( l2  :  'b Prims.list ) ( l3  :  'c Prims.list ) -> (match (Prims.MkTuple3 (l1, l2, l3)) with
| Prims.MkTuple3 (Prims.Nil, Prims.Nil, Prims.Nil) -> begin
Prims.l__Nil
end
| Prims.MkTuple3 (Prims.Cons (hd1, tl1), Prims.Cons (hd2, tl2), Prims.Cons (hd3, tl3)) -> begin
(let _1_9144 = (Obj.magic (zip3 (Obj.magic tl1) (Obj.magic tl2) (Obj.magic tl3)))
in Prims.Cons (Prims.MkTuple3 (hd1, hd2, hd3), _1_9144))
end
| Prims.MkTuple3 (_, _, _) -> begin
(Obj.magic (Prims.failwith (Obj.magic "The lists do not have the same length")))
end))

let rec sortWith = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'a  ->  Prims.int ) ( _1_12  :  'a Prims.list ) -> (match (_1_12) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (pivot, tl) -> begin
(let _1_543 = (Obj.magic (partition (Obj.magic (fun ( x  :  'a ) -> (let _1_9155 = (f pivot x)
in (Prims.op_GreaterThan _1_9155 0)))) (Obj.magic tl)))
in (match (_1_543) with
| Prims.MkTuple2 (hi, lo) -> begin
(Obj.magic (let _1_9158 = (Obj.magic (sortWith (Obj.magic f) (Obj.magic lo)))
in (let _1_9157 = (let _1_9156 = (Obj.magic (sortWith (Obj.magic f) (Obj.magic hi)))
in Prims.Cons (pivot, _1_9156))
in (append _1_9158 _1_9157))))
end))
end))

let rec partition_length = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  Prims.bool ) ( l  :  'a Prims.list ) -> ())

let bool_of_compare = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'a  ->  Prims.int ) ( x  :  'a ) ( y  :  'a ) -> (Prims.op_GreaterThanOrEqual (f x y) 0))

let rec sortWithT = (fun ( _1_7758  :  Prims.unit ) ( f  :  'a  ->  'a  ->  Prims.int ) ( _1_13  :  'a Prims.list ) -> (match (_1_13) with
| Prims.Nil -> begin
Prims.l__Nil
end
| Prims.Cons (pivot, tl) -> begin
(let _1_567 = (Obj.magic (partitionT (Obj.magic (bool_of_compare (Obj.magic f) (Obj.magic pivot))) (Obj.magic tl)))
in (match (_1_567) with
| Prims.MkTuple2 (hi, lo) -> begin
(Obj.magic (let _1_568 = ()
in (append (Obj.magic (sortWithT (Obj.magic f) (Obj.magic lo))) (Prims.Cons (pivot, (Obj.magic (sortWithT (Obj.magic f) (Obj.magic hi))))))))
end))
end))




