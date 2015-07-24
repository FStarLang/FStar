
type ('a, 'b) prod =
| Pair of unit * 'a * 'b





(* let ffst = (fun ( _1_1338  :  unit ) -> Test_Pair.pfst) *)

let idlist = (fun ( x  :  int list ) -> x)

type nnat =
| O
| S of nnat

let idnat = (fun ( x  :  nnat ) -> x)

let idnat2 = (fun ( x  :  nnat ) -> x)

let id = (fun ( _1_1338  :  unit ) ( x  :  'a ) -> x)

let idp = (fun ( _1_1338  :  unit ) ( x  :  Obj.t ) -> x)

let idp' = (fun ( _1_1338  :  unit ) ( x  :  'a ) -> x)

let add1 = (fun ( a  :  nnat ) -> S (a))

let add2 = (fun ( _1_2709  :  nnat ) -> S (_1_2709))

let eval_order = (fun ( effectful  :  string  ->  string ) ( f  :  string  ->  string  ->  string ) -> (let _1_2729 = (effectful "first")
in (f _1_2729 "second")))

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

type 'a list =
| Nil of unit
| Cons of unit * 'a * 'a list





let prepend0 = (fun ( tll  :  nnat list ) -> Cons ((), O, tll))

type ('a, 'b) list2 =
| Nil2 of unit
| Cons2 of unit * 'a * 'b * ('a, 'b) list2









type any =
| Any of unit * Obj.t



type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p of unit
| Cons2p of unit * 'a * ('a, 'a) prod list2p





type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t list3





type 'x poly =
| Poly of unit * nnat * 'x



type 'x poly2 =
| Poly2 of unit * unit * 'x





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
| Conss of unit * nnat * 'a * ('a, unit) vec





type vecn1 =
(nnat, unit) vec

type ('t, 'n) naryTree =
| Leaf of unit
| Node of unit * (('t, unit) naryTree, unit) vec





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
| ECons of unit * 'a * 'a oddlist 
 and 'a oddlist =
| OCons of unit * 'a * 'a evenlist







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

let add0CommUse = (fun ( n  :  nnat ) -> ())

let add0CommUse2 = (fun ( n  :  nnat ) -> (let x = ()
in n))

let unitAsNat = (fun ( u  :  unit ) -> O)

let add0CommUse3 = (fun ( n  :  nnat ) -> (unitAsNat ()))

let add0CommAlias = add0Comm

let rec mult2 = (fun ( a  :  nnat ) ( b  :  nnat ) -> (match (a) with
| O -> begin
O
end
| S (a') -> begin
(add b (mult2 a' b))
end))




