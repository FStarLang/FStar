
let isEmpty = (fun ( _47_392  :  unit ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
true
end
| _ -> begin
false
end))

let isEmptyT = (fun ( _47_392  :  unit ) -> (isEmpty ()))

let hd = (fun ( _47_392  :  unit ) ( _3_1  :  'a list ) -> (match (_3_1) with
| hd::tl -> begin
hd
end
| _ -> begin
((failwith (())) "head of empty list")
end))

let tail = (fun ( _47_392  :  unit ) -> (fun ( _3_2  :  '_3_748 list ) -> (match (_3_2) with
| hd::tl -> begin
tl
end
| _ -> begin
((failwith (())) "tail of empty list")
end)))

let tl = (fun ( _47_392  :  unit ) -> (tail ()))

let rec length = (fun ( _47_392  :  unit ) ( _3_3  :  'a list ) -> (match (_3_3) with
| [] -> begin
0
end
| _::tl -> begin
(1 + ((length ()) tl))
end))

let lengthT = (fun ( _47_392  :  unit ) -> (length ()))

let rec nth = (fun ( _47_392  :  unit ) ( l  :  'a list ) ( n  :  int ) -> (match ((n < 0)) with
| true -> begin
((failwith (())) "nth takes a non-negative integer as input")
end
| false -> begin
(match ((n = 0)) with
| true -> begin
(match (l) with
| [] -> begin
((failwith (())) "not enough elements")
end
| hd::_ -> begin
hd
end)
end
| false -> begin
(match (l) with
| [] -> begin
((failwith (())) "not enough elements")
end
| _::tl -> begin
((nth ()) tl n)
end)
end)
end))

let rec total_nth = (fun ( _47_392  :  unit ) ( l  :  'a list ) ( n  :  Support.Prims.nat ) -> (match (l) with
| [] -> begin
l__None
end
| hd::tl -> begin
(match ((n = 0)) with
| true -> begin
Some (hd)
end
| false -> begin
((total_nth ()) tl (n - 1))
end)
end))

let rec count = (fun ( _47_392  :  unit ) ( x  :  'a ) ( _3_4  :  'a list ) -> (match (_3_4) with
| [] -> begin
0
end
| hd::tl -> begin
(match ((x = hd)) with
| true -> begin
(1 + ((count ()) x tl))
end
| false -> begin
((count ()) x tl)
end)
end))

let countT = (fun ( _47_392  :  unit ) -> (count ()))

let rec rev_acc = (fun ( _47_392  :  unit ) ( l  :  'a list ) ( acc  :  'a list ) -> (match (l) with
| [] -> begin
acc
end
| hd::tl -> begin
((rev_acc ()) tl ((hd)::acc))
end))

let rev_append = (fun ( _47_392  :  unit ) -> (rev_acc ()))

let rev = (fun ( _47_392  :  unit ) ( l  :  'a list ) -> ((rev_acc ()) l Support.Prims.l__Nil))

let revT = (fun ( _47_392  :  unit ) -> (rev ()))

let rec append = (fun ( _47_392  :  unit ) ( x  :  'a list ) ( y  :  'a list ) -> (match (x) with
| [] -> begin
y
end
| a::tl -> begin
(a)::((append ()) tl y)
end))

let appendT = (fun ( _47_392  :  unit ) -> (append ()))

let rec flatten = (fun ( _47_392  :  unit ) ( l  :  'a list list ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
((append ()) hd ((flatten ()) tl))
end))

let flattenT = (fun ( _47_392  :  unit ) -> (flatten ()))

let concat = (fun ( _47_392  :  unit ) -> (flatten ()))

let concatT = (fun ( _47_392  :  unit ) -> (flattenT ()))

let rec iter = (fun ( _47_392  :  unit ) ( f  :  'a  ->  unit ) ( x  :  'a list ) -> (match (x) with
| [] -> begin
()
end
| a::tl -> begin
(let _3_95 = (f a)
in ((iter ()) f tl))
end))

let rec iterT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  unit ) ( x  :  'a list ) -> ())

let rec map = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b ) ( x  :  'a list ) -> (match (x) with
| [] -> begin
Support.Prims.l__Nil
end
| a::tl -> begin
(let _47_1676 = (f a)
in (let _47_1675 = ((map ()) f tl)
in (_47_1676)::_47_1675))
end))

let rec mapT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b ) ( x  :  'a list ) -> (match (x) with
| [] -> begin
Support.Prims.l__Nil
end
| a::tl -> begin
((f a))::((mapT ()) f tl)
end))

let rec mapi_init = (fun ( _47_392  :  unit ) ( f  :  int  ->  'a  ->  'b ) ( l  :  'a list ) ( i  :  int ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
(let _47_1692 = (f i hd)
in (let _47_1691 = ((mapi_init ()) f tl (i + 1))
in (_47_1692)::_47_1691))
end))

let rec mapi_initT = (fun ( _47_392  :  unit ) ( f  :  int  ->  'a  ->  'b ) ( l  :  'a list ) ( i  :  int ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
((f i hd))::((mapi_initT ()) f tl (i + 1))
end))

let mapi = (fun ( _47_392  :  unit ) ( f  :  int  ->  'a  ->  'b ) ( l  :  'a list ) -> ((mapi_init ()) f l 0))

let mapiT = (fun ( _47_392  :  unit ) ( f  :  int  ->  'a  ->  'b ) ( l  :  'a list ) -> ((mapi_initT ()) f l 0))

let rec concatMap = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b list ) ( _3_5  :  'a list ) -> (match (_3_5) with
| [] -> begin
Support.Prims.l__Nil
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = ((concatMap ()) f tl)
in ((append ()) fa ftl)))
end))

let rec concatMapT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b list ) ( _3_6  :  'a list ) -> (match (_3_6) with
| [] -> begin
Support.Prims.l__Nil
end
| a::tl -> begin
(let fa = (f a)
in (let ftl = ((concatMapT ()) f tl)
in ((appendT ()) fa ftl)))
end))

let rec map2 = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  'c ) ( l1  :  'a list ) ( l2  :  'b list ) -> (match (Support.Prims.MkTuple2 (l1, l2)) with
| Support.Prims.MkTuple2 ([], []) -> begin
Support.Prims.l__Nil
end
| Support.Prims.MkTuple2 (hd1::tl1, hd2::tl2) -> begin
(let _47_1738 = (f hd1 hd2)
in (let _47_1737 = ((map2 ()) f tl1 tl2)
in (_47_1738)::_47_1737))
end
| Support.Prims.MkTuple2 (_, _) -> begin
((failwith (())) "The lists do not have the same length")
end))

let rec map3 = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  'c  ->  'd ) ( l1  :  'a list ) ( l2  :  'b list ) ( l3  :  'c list ) -> (match (Support.Prims.MkTuple3 (l1, l2, l3)) with
| Support.Prims.MkTuple3 ([], [], []) -> begin
Support.Prims.l__Nil
end
| Support.Prims.MkTuple3 (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
(let _47_1753 = (f hd1 hd2 hd3)
in (let _47_1752 = ((map3 ()) f tl1 tl2 tl3)
in (_47_1753)::_47_1752))
end
| Support.Prims.MkTuple3 (_, _, _) -> begin
((failwith (())) "The lists do not have the same length")
end))

let rec fold_left = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b list ) -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
(let _47_1763 = (f x hd)
in ((fold_left ()) f _47_1763 tl))
end))

let rec fold_leftT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  'a ) ( x  :  'a ) ( y  :  'b list ) -> (match (y) with
| [] -> begin
x
end
| hd::tl -> begin
((fold_leftT ()) f (f x hd) tl)
end))

let rec fold_left2 = (fun ( _47_392  :  unit ) ( f  :  's  ->  'a  ->  'b  ->  's ) ( a  :  's ) ( l1  :  'a list ) ( l2  :  'b list ) -> (match (Support.Prims.MkTuple2 (l1, l2)) with
| Support.Prims.MkTuple2 ([], []) -> begin
a
end
| Support.Prims.MkTuple2 (hd1::tl1, hd2::tl2) -> begin
(let _47_1786 = (f a hd1 hd2)
in ((fold_left2 ()) f _47_1786 tl1 tl2))
end
| Support.Prims.MkTuple2 (_, _) -> begin
((failwith (())) "The lists do not have the same length")
end))

let rec fold_right = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a list ) ( x  :  'b ) -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(let _47_1796 = ((fold_right ()) f tl x)
in (f hd _47_1796))
end))

let rec fold_rightT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  'b ) ( l  :  'a list ) ( x  :  'b ) -> (match (l) with
| [] -> begin
x
end
| hd::tl -> begin
(f hd ((fold_rightT ()) f tl x))
end))

let rec mem = (fun ( _47_392  :  unit ) ( x  :  'a ) ( _3_7  :  'a list ) -> (match (_3_7) with
| [] -> begin
false
end
| hd::tl -> begin
(match ((hd = x)) with
| true -> begin
true
end
| false -> begin
((mem ()) x tl)
end)
end))

let memT = (fun ( _47_392  :  unit ) -> (mem ()))

let contains = (fun ( _47_392  :  unit ) -> (mem ()))

let containsT = (fun ( _47_392  :  unit ) -> (memT ()))

let rec existsb = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
false
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
true
end
| false -> begin
((existsb ()) f tl)
end)
end))

let rec find = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
l__None
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
Some (hd)
end
| false -> begin
((find ()) f tl)
end)
end))

let findT = (fun ( _47_392  :  unit ) -> (find ()))

let rec filter = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( _3_8  :  'a list ) -> (match (_3_8) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
(let _47_1852 = ((filter ()) f tl)
in (hd)::_47_1852)
end
| false -> begin
((filter ()) f tl)
end)
end))

let rec filterT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( _3_9  :  'a list ) -> (match (_3_9) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
(hd)::((filterT ()) f tl)
end
| false -> begin
((filterT ()) f tl)
end)
end))

let rec for_all = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
((for_all ()) f tl)
end
| false -> begin
false
end)
end))

let rec for_allT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
true
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
((for_allT ()) f tl)
end
| false -> begin
false
end)
end))

let rec forall2 = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b  ->  bool ) ( l1  :  'a list ) ( l2  :  'b list ) -> (match (Support.Prims.MkTuple2 (l1, l2)) with
| Support.Prims.MkTuple2 ([], []) -> begin
true
end
| Support.Prims.MkTuple2 (hd1::tl1, hd2::tl2) -> begin
(match ((f hd1 hd2)) with
| true -> begin
((forall2 ()) f tl1 tl2)
end
| false -> begin
false
end)
end
| Support.Prims.MkTuple2 (_, _) -> begin
((failwith (())) "The lists do not have the same length")
end))

let rec collect = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b list ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
(let _47_1891 = (f hd)
in (let _47_1890 = ((collect ()) f tl)
in ((append ()) _47_1891 _47_1890)))
end))

let rec collectT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b list ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
((appendT ()) (f hd) ((collectT ()) f tl))
end))

let rec tryFind = (fun ( _47_392  :  unit ) ( p  :  'a  ->  bool ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
l__None
end
| hd::tl -> begin
(match ((p hd)) with
| true -> begin
Some (hd)
end
| false -> begin
((tryFind ()) p tl)
end)
end))

let rec tryFindT = (fun ( _47_392  :  unit ) ( p  :  'a  ->  bool ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
l__None
end
| hd::tl -> begin
(match ((p hd)) with
| true -> begin
Some (hd)
end
| false -> begin
((tryFindT ()) p tl)
end)
end))

let rec tryPick = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b option ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
l__None
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
Some (x)
end
| None -> begin
((tryPick ()) f tl)
end)
end))

let rec tryPickT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b option ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
l__None
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
Some (x)
end
| None -> begin
((tryPickT ()) f tl)
end)
end))

let rec choose = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b option ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(let _47_1922 = ((choose ()) f tl)
in (x)::_47_1922)
end
| None -> begin
((choose ()) f tl)
end)
end))

let rec chooseT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'b option ) ( l  :  'a list ) -> (match (l) with
| [] -> begin
Support.Prims.l__Nil
end
| hd::tl -> begin
(match ((f hd)) with
| Some (x) -> begin
(x)::((chooseT ()) f tl)
end
| None -> begin
((chooseT ()) f tl)
end)
end))

let rec partition = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( _3_10  :  'a list ) -> (match (_3_10) with
| [] -> begin
Support.Prims.MkTuple2 (Support.Prims.l__Nil, Support.Prims.l__Nil)
end
| hd::tl -> begin
(let _3_439 = ((partition ()) f tl)
in (match (_3_439) with
| Support.Prims.MkTuple2 (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
Support.Prims.MkTuple2 ((hd)::l1, l2)
end
| false -> begin
Support.Prims.MkTuple2 (l1, (hd)::l2)
end)
end))
end))

let rec partitionT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( _3_11  :  'a list ) -> (match (_3_11) with
| [] -> begin
Support.Prims.MkTuple2 (Support.Prims.l__Nil, Support.Prims.l__Nil)
end
| hd::tl -> begin
(let _3_450 = ((partitionT ()) f tl)
in (match (_3_450) with
| Support.Prims.MkTuple2 (l1, l2) -> begin
(match ((f hd)) with
| true -> begin
Support.Prims.MkTuple2 ((hd)::l1, l2)
end
| false -> begin
Support.Prims.MkTuple2 (l1, (hd)::l2)
end)
end))
end))

let rec assoc = (fun ( _47_392  :  unit ) ( a  :  'a ) ( x  :  ('a, 'b) Support.Prims.l__Tuple2 list ) -> (match (x) with
| [] -> begin
l__None
end
| Support.Prims.MkTuple2 (a', b)::tl -> begin
(match ((a = a')) with
| true -> begin
Some (b)
end
| false -> begin
((assoc ()) a tl)
end)
end))

let assocT = (fun ( _47_392  :  unit ) -> (assoc ()))

let rec split = (fun ( _47_392  :  unit ) ( l  :  ('a, 'b) Support.Prims.l__Tuple2 list ) -> (match (l) with
| [] -> begin
Support.Prims.MkTuple2 (Support.Prims.l__Nil, Support.Prims.l__Nil)
end
| Support.Prims.MkTuple2 (hd1, hd2)::tl -> begin
(let _3_472 = ((split ()) tl)
in (match (_3_472) with
| Support.Prims.MkTuple2 (tl1, tl2) -> begin
Support.Prims.MkTuple2 ((hd1)::tl1, (hd2)::tl2)
end))
end))

let splitT = (fun ( _47_392  :  unit ) -> (split ()))

let unzip = (fun ( _47_392  :  unit ) -> (split ()))

let unzipT = (fun ( _47_392  :  unit ) -> (splitT ()))

let rec unzip3 = (fun ( _47_392  :  unit ) ( l  :  ('a, 'b, 'c) Support.Prims.l__Tuple3 list ) -> (match (l) with
| [] -> begin
Support.Prims.MkTuple3 (Support.Prims.l__Nil, Support.Prims.l__Nil, Support.Prims.l__Nil)
end
| Support.Prims.MkTuple3 (hd1, hd2, hd3)::tl -> begin
(let _3_487 = ((unzip3 ()) tl)
in (match (_3_487) with
| Support.Prims.MkTuple3 (tl1, tl2, tl3) -> begin
Support.Prims.MkTuple3 ((hd1)::tl1, (hd2)::tl2, (hd3)::tl3)
end))
end))

let unzip3T = (fun ( _47_392  :  unit ) -> (unzip3 ()))

let rec zip = (fun ( _47_392  :  unit ) ( l1  :  'a list ) ( l2  :  'b list ) -> (match (Support.Prims.MkTuple2 (l1, l2)) with
| Support.Prims.MkTuple2 ([], []) -> begin
Support.Prims.l__Nil
end
| Support.Prims.MkTuple2 (hd1::tl1, hd2::tl2) -> begin
(let _47_1950 = ((zip ()) tl1 tl2)
in (Support.Prims.MkTuple2 (hd1, hd2))::_47_1950)
end
| Support.Prims.MkTuple2 (_, _) -> begin
((failwith (())) "The lists do not have the same length")
end))

let rec zip3 = (fun ( _47_392  :  unit ) ( l1  :  'a list ) ( l2  :  'b list ) ( l3  :  'c list ) -> (match (Support.Prims.MkTuple3 (l1, l2, l3)) with
| Support.Prims.MkTuple3 ([], [], []) -> begin
Support.Prims.l__Nil
end
| Support.Prims.MkTuple3 (hd1::tl1, hd2::tl2, hd3::tl3) -> begin
(let _47_1954 = ((zip3 ()) tl1 tl2 tl3)
in (Support.Prims.MkTuple3 (hd1, hd2, hd3))::_47_1954)
end
| Support.Prims.MkTuple3 (_, _, _) -> begin
((failwith (())) "The lists do not have the same length")
end))

let rec sortWith = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'a  ->  int ) ( _3_12  :  'a list ) -> (match (_3_12) with
| [] -> begin
Support.Prims.l__Nil
end
| pivot::tl -> begin
(let _3_544 = ((partition ()) (fun ( x  :  'a ) -> (let _47_1964 = (f pivot x)
in (_47_1964 > 0))) tl)
in (match (_3_544) with
| Support.Prims.MkTuple2 (hi, lo) -> begin
(let _47_1967 = ((sortWith ()) f lo)
in (let _47_1966 = (let _47_1965 = ((sortWith ()) f hi)
in (pivot)::_47_1965)
in ((append ()) _47_1967 _47_1966)))
end))
end))

let rec partition_length = (fun ( _47_392  :  unit ) ( f  :  'a  ->  bool ) ( l  :  'a list ) -> ())

let bool_of_compare = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'a  ->  int ) ( x  :  'a ) ( y  :  'a ) -> ((f x y) >= 0))

let rec sortWithT = (fun ( _47_392  :  unit ) ( f  :  'a  ->  'a  ->  int ) ( _3_13  :  'a list ) -> (match (_3_13) with
| [] -> begin
Support.Prims.l__Nil
end
| pivot::tl -> begin
(let _3_568 = ((partitionT ()) ((bool_of_compare ()) f pivot) tl)
in (match (_3_568) with
| Support.Prims.MkTuple2 (hi, lo) -> begin
(let _3_569 = ()
in ((append ()) ((sortWithT ()) f lo) ((pivot)::((sortWithT ()) f hi))))
end))
end))




