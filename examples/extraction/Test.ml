
type nnat =
| O
| S of nnat

let idnat = (fun x -> x)

let idnat2 = (fun x -> x)

let id = (fun _1_916 x -> x)

let idp = (fun _1_916 x -> x)

let add1 = (fun a -> S (a))

let add2 = (fun _1_926 -> S (_1_926))

let eval_order = (fun effectful f -> (let _1_946 = (effectful "first")
in (f _1_946 "second")))

let prev = (fun _1_1 -> (match (_1_1) with
| O -> begin
O
end
| S (n) -> begin
n
end))

type ('a, 'b) prod =
| Pair of 'a * 'b





type 'a list =
| Nil
| Cons of 'a * 'a list





let prepend0 = (fun tll -> Cons (O, tll))

type ('a, 'b) list2 =
| Nil2
| Cons2 of 'a * 'b * ('a, 'b) list2









type any =
| Any of unit * Obj.t



type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p
| Cons2p of 'a * ('a, 'a) prod list2p





type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t list3





type 'x poly =
| Poly of nnat * 'x



type 'x poly2 =
| Poly2 of unit * 'x





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
| Nill
| Conss of nnat * 'a * ('a, unit) vec





type vecn1 =
(nnat, unit) vec

type ('t, 'n) naryTree =
| Leaf
| Node of (('t, unit) naryTree, unit) vec





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
| ENil
| ECons of 'a * 'a oddlist 
 and 'a oddlist =
| OCons of 'a * 'a evenlist










