
let idlist = (fun ( x  :  Prims.int Prims.list ) -> x)

type nnat =
| O
| S of nnat

let idnat = (fun ( x  :  nnat ) -> x)

let idnat2 = (fun ( x  :  nnat ) -> x)

let id = (fun ( _3_95  :  Prims.unit ) ( x  :  'a ) -> x)

let idp = (fun ( _3_95  :  Prims.unit ) ( x  :  Obj.t ) -> x)

let idp' = (fun ( _3_95  :  Prims.unit ) ( x  :  'a ) -> x)

let add1 = (fun ( a  :  nnat ) -> S (a))

let add2 = (fun ( _3_1386  :  nnat ) -> S (_3_1386))

let eval_order = (fun ( effectful  :  Prims.string  ->  Prims.string ) ( f  :  Prims.string  ->  Prims.string  ->  Prims.string ) -> (let _3_1406 = (effectful "first")
in (f _3_1406 "second")))

let prev = (fun ( _2_1  :  nnat ) -> (match (_2_1) with
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
| Pair of 'a * 'b





type 'a list =
| Nil
| Cons of 'a * 'a list





let prepend0 = (fun ( tll  :  nnat list ) -> Cons (O, tll))

type ('a, 'b) list2 =
| Nil2
| Cons2 of 'a * 'b * ('a, 'b) list2









type distr_pair =
(Prims.unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p
| Cons2p of 'a * ('a, 'a) prod list2p





type 'x sch =
'x  ->  'x

type 'x sch3param =
'x  ->  'x

type idt =
Prims.unit  ->  Obj.t  ->  Obj.t

type 'a listalias =
'a list

type 'a evenlist =
| ENil
| ECons of 'a * 'a oddlist 
 and 'a oddlist =
| OCons of 'a * 'a evenlist







type someLemmaStatement =
nnat  ->  nnat  ->  Prims.unit

type trivialLemmaSatement =
nnat  ->  nnat  ->  Prims.unit

let rec add0Comm = (fun ( n  :  nnat ) -> ())

let add0CommUse = (fun ( n  :  nnat ) -> ())

let add0CommUse2 = (fun ( n  :  nnat ) -> (let x = ()
in n))

let unitAsNat = (fun ( u  :  Prims.unit ) -> O)

let add0CommUse3 = (fun ( n  :  nnat ) -> (unitAsNat ()))

let add0CommAlias = add0Comm

let rec mult2 = (fun ( a  :  nnat ) ( b  :  nnat ) -> (match (a) with
| O -> begin
O
end
| S (a') -> begin
(add b (mult2 a' b))
end))




