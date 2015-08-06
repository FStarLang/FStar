
type ('a, 'b) prod =
| Pair of 'a * 'b

let is_Pair = (fun ( _discr_ ) -> (match (_discr_) with
| Pair (_) -> begin
true
end
| _ -> begin
false
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

let idnat = (fun ( x ) -> x)

let idnat2 = (fun ( x ) -> x)

let id = (fun ( x ) -> x)

let idp = (fun ( x ) -> x)

let idp' = (fun ( x ) -> x)

let add1 = (fun ( a ) -> S (a))

let add2 = (fun ( _2_2680 ) -> S (_2_2680))

let eval_order = (fun ( effectful ) ( f ) -> (let _2_2700 = (effectful "first")
in (f _2_2700 "second")))

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

type any =
| Any of unit * Obj.t

let is_Any = (fun ( _discr_ ) -> (match (_discr_) with
| Any (_) -> begin
true
end
| _ -> begin
false
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

type ' x poly =
| Poly of nnat * ' x

let is_Poly = (fun ( _discr_ ) -> (match (_discr_) with
| Poly (_) -> begin
true
end
| _ -> begin
false
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




