let idlist = (fun ( x  :  int list ) -> x)

type nnat =
| O
| S of nnat

let idnat = (fun ( x  :  nnat ) -> x)

let idnat2 = (fun ( x  :  nnat ) -> x)

let id = (fun ( _1_1234  :  unit ) ( x  :  'a ) -> x)

let idp = (fun ( _1_1234  :  unit ) ( x  :  Obj.t ) -> x)

let idp' = (fun ( _1_1234  :  unit ) ( x  :  'a ) -> x)

let add1 = (fun ( a  :  nnat ) -> S (a))

let add2 = (fun ( _1_2167  :  nnat ) -> S (_1_2167))

let eval_order = (fun ( effectful  :  string  ->  string ) ( f  :  string  ->  string  ->  string ) -> (let _1_2187 = (effectful "first")
in (f _1_2187 "second")))

let prev = (fun ( _1_1  :  nnat ) -> (match (_1_1) with
| O -> begin
O
end
| S (n) -> begin
n
end))

let rec add = (fun ( a  :  nnat ) ( b  :  nnat ) -> (match (a) with
| O -> begin
b
end
| S (a') -> begin
S ((add a' b))
end))

type ('a, 'b) prod =
| Pair of unit * unit * Obj.t * Obj.t





type 'a list =
| Nil of unit
| Cons of unit * Obj.t * Obj.t list





let prepend0 = (Obj.magic (fun ( tll  :  nnat list ) -> (fun ( _1_2230  :  Obj.t list ) -> Cons ((Obj.magic O), (Obj.magic tll), _1_2230))))

type ('a, 'b) list2 =
| Nil2 of unit * unit
| Cons2 of unit * unit * Obj.t * Obj.t * (Obj.t, Obj.t) list2









type any =
| Any of unit * Obj.t



type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p of unit
| Cons2p of unit * Obj.t * (Obj.t, Obj.t) prod list2p





type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t list3





type 'x poly =
| Poly of unit * nnat * Obj.t



type 'x poly2 =
| Poly2 of unit * unit * Obj.t





type 'x sch =
'x  ->  'x

type 'x sch1 =
'x  ->  'x

type 'x sch3 =
'x  ->  'x

type 'x sch3param =
'x  ->  'x

type idt =
unit  ->  Obj.t  ->  Obj.t

type ('a, 'dummyV1) vec =
| Nill of unit
| Conss of unit * nnat * Obj.t * (Obj.t, unit) vec





type vecn1 =
(nnat, unit) vec

type ('t, 'n) naryTree =
| Leaf of unit * nnat
| Node of unit * nnat * ((Obj.t, unit) naryTree, unit) vec





type 't binaryTree =
('t, unit) naryTree

type polyvec =
(nnat, unit) vec poly

type polylist =
Obj.t list poly2

type 'a listalias =
'a list

type polylistalias =
Obj.t listalias poly2

type 'a evenlist =
| ENil of unit
| ECons of unit * Obj.t * Obj.t oddlist 
 and 'a oddlist =
| OCons of unit * Obj.t * Obj.t evenlist







type 'dummyV1 isEven =
| Ev0
| EvSOdd of nnat * unit isOdd 
 and 'dummyV1 isOdd =
| OddSEven of nnat * unit isEven

let ev2 = EvSOdd (S (O), OddSEven (O, Ev0))

type someLemmaStatement =
nnat  ->  nnat  ->  unit

type trivialLemmaSatement =
nnat  ->  nnat  ->  unit

let rec add0Comm = (fun ( n  :  nnat ) -> ())




