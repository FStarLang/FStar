
type ('a, 'b) prod =
| Pair of 'a * 'b

let is_Pair = (fun ( _discr_ ) -> (match (_discr_) with
| Pair (_) -> begin
true
end
| _ -> begin
false
end))

let pfst = (fun ( _proj_ ) -> (match (_proj_) with
| Pair (dummyPat2, dummyPat1) -> begin
pfst
end))

let psnd = (fun ( _proj_ ) -> (match (_proj_) with
| Pair (dummyPat2, dummyPat1) -> begin
psnd
end))

let ffst = Test_Pair.pfst

let idlist = (fun ( x ) -> x)

type nnat =
| O
| S of nnat

let is_O = (fun ( _discr_ ) -> (match (_discr_) with
| O -> begin
true
end
| _ -> begin
false
end))

let is_S = (fun ( _discr_ ) -> (match (_discr_) with
| S (_) -> begin
true
end
| _ -> begin
false
end))

let _0 = (fun ( _proj_ ) -> (match (_proj_) with
| S (dummyPat1) -> begin
_0
end))

let idnat = (fun ( x ) -> x)

let idnat2 = (fun ( x ) -> x)

let id = (fun ( x ) -> x)

let idp = (fun ( x ) -> x)

let idp' = (fun ( x ) -> x)

let add1 = (fun ( a ) -> S (a))

let add2 = (fun ( _2_2684 ) -> S (_2_2684))

let eval_order = (fun ( effectful ) ( f ) -> (let _2_2704 = (effectful "first")
in (f _2_2704 "second")))

let prev = (fun ( _2_1 ) -> (match (_2_1) with
| O -> begin
O
end
| S (n) -> begin
n
end))

let rec add = (fun ( a ) ( b ) -> (match (a) with
| O -> begin
b
end
| S (a') -> begin
S ((add a' b))
end))

let prepend0 = (fun ( tll ) -> (O)::tll)

type ('a, ' b) list2 =
| Nil2
| Cons2 of 'a * ' b * ('a, ' b) list2

let is_Nil2 = (fun ( _discr_ ) -> (match (_discr_) with
| Nil2 -> begin
true
end
| _ -> begin
false
end))

let is_Cons2 = (fun ( _discr_ ) -> (match (_discr_) with
| Cons2 (_) -> begin
true
end
| _ -> begin
false
end))

let hd = (fun ( _proj_ ) -> (match (_proj_) with
| Cons2 (dummyPat3, dummyPat2, dummyPat1) -> begin
hd
end))

let hd2 = (fun ( _proj_ ) -> (match (_proj_) with
| Cons2 (dummyPat3, dummyPat2, dummyPat1) -> begin
hd2
end))

let tl = (fun ( _proj_ ) -> (match (_proj_) with
| Cons2 (dummyPat3, dummyPat2, dummyPat1) -> begin
tl
end))

type any =
| Any of unit * Obj.t

let is_Any = (fun ( _discr_ ) -> (match (_discr_) with
| Any (_) -> begin
true
end
| _ -> begin
false
end))

let _1 = (fun ( _proj_ ) -> (match (_proj_) with
| Any (dummyPat2, dummyPat1) -> begin
_1
end))

type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p
| Cons2p of 'a * ('a, 'a) prod list2p

let is_Nil2p = (fun ( _discr_ ) -> (match (_discr_) with
| Nil2p -> begin
true
end
| _ -> begin
false
end))

let is_Cons2p = (fun ( _discr_ ) -> (match (_discr_) with
| Cons2p (_) -> begin
true
end
| _ -> begin
false
end))

let hd = (fun ( _proj_ ) -> (match (_proj_) with
| Cons2p (dummyPat2, dummyPat1) -> begin
hd
end))

let tl = (fun ( _proj_ ) -> (match (_proj_) with
| Cons2p (dummyPat2, dummyPat1) -> begin
tl
end))

type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t list3

let is_Nil3 = (fun ( _discr_ ) -> (match (_discr_) with
| Nil3 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Cons3 = (fun ( _discr_ ) -> (match (_discr_) with
| Cons3 (_) -> begin
true
end
| _ -> begin
false
end))

let _1 = (fun ( _proj_ ) -> (match (_proj_) with
| Cons3 (dummyPat3, dummyPat2, dummyPat1) -> begin
_1
end))

let _2 = (fun ( _proj_ ) -> (match (_proj_) with
| Cons3 (dummyPat3, dummyPat2, dummyPat1) -> begin
_2
end))

type ' x poly =
| Poly of nnat * ' x

let is_Poly = (fun ( _discr_ ) -> (match (_discr_) with
| Poly (_) -> begin
true
end
| _ -> begin
false
end))

let n = (fun ( _proj_ ) -> (match (_proj_) with
| Poly (dummyPat2, dummyPat1) -> begin
n
end))

let _2 = (fun ( _proj_ ) -> (match (_proj_) with
| Poly (dummyPat2, dummyPat1) -> begin
_2
end))

type ' x poly2 =
| Poly2 of unit * ' x

let is_Poly2 = (fun ( _discr_ ) -> (match (_discr_) with
| Poly2 (_) -> begin
true
end
| _ -> begin
false
end))

let _2 = (fun ( _proj_ ) -> (match (_proj_) with
| Poly2 (dummyPat2, dummyPat1) -> begin
_2
end))

type ' x sch =
' x  ->  ' x

type ' x sch1 =
' x  ->  ' x

type ' x sch3 =
' x  ->  ' x

type ' x sch3param =
' x  ->  ' x

type idt =
unit  ->  Obj.t  ->  Obj.t

type (' a, 'dummyV1) vec =
| Nill
| Conss of nnat * ' a * (' a, unit) vec

let is_Nill = (fun ( _discr_ ) -> (match (_discr_) with
| Nill -> begin
true
end
| _ -> begin
false
end))

let is_Conss = (fun ( _discr_ ) -> (match (_discr_) with
| Conss (_) -> begin
true
end
| _ -> begin
false
end))

let n = (fun ( _proj_ ) -> (match (_proj_) with
| Conss (dummyPat3, dummyPat2, dummyPat1) -> begin
n
end))

let _2 = (fun ( _proj_ ) -> (match (_proj_) with
| Conss (dummyPat3, dummyPat2, dummyPat1) -> begin
_2
end))

let _3 = (fun ( _proj_ ) -> (match (_proj_) with
| Conss (dummyPat3, dummyPat2, dummyPat1) -> begin
_3
end))

type vecn1 =
(nnat, unit) vec

type (' t, ' n) naryTree =
| Leaf
| Node of ((' t, unit) naryTree, unit) vec

let is_Leaf = (fun ( _discr_ ) -> (match (_discr_) with
| Leaf -> begin
true
end
| _ -> begin
false
end))

let is_Node = (fun ( _discr_ ) -> (match (_discr_) with
| Node (_) -> begin
true
end
| _ -> begin
false
end))

let n = (fun ( _proj_ ) -> (match (_proj_) with
| Leaf -> begin
n
end))

let n = (fun ( _proj_ ) -> (match (_proj_) with
| Node (dummyPat1) -> begin
n
end))

let _2 = (fun ( _proj_ ) -> (match (_proj_) with
| Node (dummyPat1) -> begin
_2
end))

type ' t binaryTree =
(' t, unit) naryTree

type polyvec =
(nnat, unit) vec poly

type polylist =
Obj.t list poly2

type 'a listalias =
'a list

type polylistalias =
Obj.t listalias poly2

type ' a evenlist =
| ENil
| ECons of ' a * ' a oddlist 
 and ' a oddlist =
| OCons of ' a * ' a evenlist

let is_ENil = (fun ( _discr_ ) -> (match (_discr_) with
| ENil -> begin
true
end
| _ -> begin
false
end))

let is_ECons = (fun ( _discr_ ) -> (match (_discr_) with
| ECons (_) -> begin
true
end
| _ -> begin
false
end))

let is_OCons = (fun ( _discr_ ) -> (match (_discr_) with
| OCons (_) -> begin
true
end
| _ -> begin
false
end))

let hd = (fun ( _proj_ ) -> (match (_proj_) with
| ECons (dummyPat2, dummyPat1) -> begin
hd
end))

let tl = (fun ( _proj_ ) -> (match (_proj_) with
| ECons (dummyPat2, dummyPat1) -> begin
tl
end))

let hd = (fun ( _proj_ ) -> (match (_proj_) with
| OCons (dummyPat2, dummyPat1) -> begin
hd
end))

let tl = (fun ( _proj_ ) -> (match (_proj_) with
| OCons (dummyPat2, dummyPat1) -> begin
tl
end))

type 'dummyV1 isEven =
| Ev0
| EvSOdd of nnat * unit isOdd 
 and 'dummyV1 isOdd =
| OddSEven of nnat * unit isEven

let is_Ev0 = (fun ( _discr_ ) -> (match (_discr_) with
| Ev0 -> begin
true
end
| _ -> begin
false
end))

let is_EvSOdd = (fun ( _discr_ ) -> (match (_discr_) with
| EvSOdd (_) -> begin
true
end
| _ -> begin
false
end))

let is_OddSEven = (fun ( _discr_ ) -> (match (_discr_) with
| OddSEven (_) -> begin
true
end
| _ -> begin
false
end))

let n = (fun ( _proj_ ) -> (match (_proj_) with
| EvSOdd (dummyPat2, dummyPat1) -> begin
n
end))

let _1 = (fun ( _proj_ ) -> (match (_proj_) with
| EvSOdd (dummyPat2, dummyPat1) -> begin
_1
end))

let n = (fun ( _proj_ ) -> (match (_proj_) with
| OddSEven (dummyPat2, dummyPat1) -> begin
n
end))

let _1 = (fun ( _proj_ ) -> (match (_proj_) with
| OddSEven (dummyPat2, dummyPat1) -> begin
_1
end))

let ev2 = EvSOdd (S (O), OddSEven (O, Ev0))

type someLemmaStatement =
nnat  ->  nnat  ->  unit

type trivialLemmaSatement =
nnat  ->  nnat  ->  unit

let rec add0Comm = (fun ( n ) -> ())

let add0CommUse = (fun ( n ) -> ())

let add0CommUse2 = (fun ( n ) -> (let x = ()
in n))

let unitAsNat = (fun ( u ) -> O)

let add0CommUse3 = (fun ( n ) -> (unitAsNat ()))

let add0CommAlias = add0Comm

let rec mult2 = (fun ( a ) ( b ) -> (match (a) with
| O -> begin
O
end
| S (a') -> begin
(add b (mult2 a' b))
end))




