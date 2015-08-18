
let idlist = (fun ( x  :  int list ) -> x)

type nnat =
| O
| S of nnat

let is_O = (fun ( _discr_ ) -> (match (_discr_) with
| O (_) -> begin
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

let isPositive = is_S

let idnat = (fun ( x  :  nnat ) -> x)

let idnat2 = (fun ( x  :  nnat ) -> x)

let id = (fun ( _1_746  :  unit ) ( x  :  'a ) -> x)

let idp = (fun ( _1_746  :  unit ) ( x  :  Obj.t ) -> x)

let idp' = (fun ( _1_746  :  unit ) ( x  :  'a ) -> x)

let add1 = (fun ( a  :  nnat ) -> S (a))

let add2 = (fun ( _1_2101  :  nnat ) -> S (_1_2101))

let eval_order = (fun ( effectful  :  string  ->  string ) ( f  :  string  ->  string  ->  string ) -> (let _1_2121 = (effectful "first")
in (f _1_2121 "second")))

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
| Pair of unit * 'a * 'b

let is_Pair = (fun ( _discr_ ) -> (match (_discr_) with
| Pair (_) -> begin
true
end
| _ -> begin
false
end))





type 'a list =
| Nil of unit
| Cons of unit * 'a * 'a list

let is_Nil = (fun ( _discr_ ) -> (match (_discr_) with
| Nil (_) -> begin
true
end
| _ -> begin
false
end))

let is_Cons = (fun ( _discr_ ) -> (match (_discr_) with
| Cons (_) -> begin
true
end
| _ -> begin
false
end))





let prepend0 = (fun ( tll  :  nnat list ) -> Cons ((), O, tll))

type ('a, 'b) list2 =
| Nil2 of unit
| Cons2 of unit * 'a * 'b * ('a, 'b) list2

let is_Nil2 = (fun ( _discr_ ) -> (match (_discr_) with
| Nil2 (_) -> begin
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









type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p of unit
| Cons2p of unit * 'a * ('a, 'a) prod list2p

let is_Nil2p = (fun ( _discr_ ) -> (match (_discr_) with
| Nil2p (_) -> begin
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





type 'x sch =
'x  ->  'x

type 'x sch3param =
'x  ->  'x

type idt =
unit  ->  Obj.t  ->  Obj.t

type 'a listalias =
'a list

type 'a evenlist =
| ENil of unit
| ECons of unit * 'a * 'a oddlist 
 and 'a oddlist =
| OCons of unit * 'a * 'a evenlist

let is_ENil = (fun ( _discr_ ) -> (match (_discr_) with
| ENil (_) -> begin
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




