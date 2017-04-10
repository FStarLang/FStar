
type ('a, 'b) prod =
| Pair of 'a * 'b

let uu___is_Pair = (fun ( _discr_ ) -> (match (_discr_) with
| Pair (_) -> begin
true
end
| _ -> begin
false
end))

let ___Pair___pfst = (fun ( projectee ) -> (match (projectee) with
| Pair (_8_7, _8_8) -> begin
_8_7
end))

let ___Pair___psnd = (fun ( projectee ) -> (match (projectee) with
| Pair (_8_10, _8_9) -> begin
_8_9
end))

let ffst = ___Pair___pfst

let idlist = (fun ( x ) -> x)

type nnat =
| O
| S of nnat

let uu___is_O = (fun ( _discr_ ) -> (match (_discr_) with
| O -> begin
true
end
| _ -> begin
false
end))

let uu___is_S = (fun ( _discr_ ) -> (match (_discr_) with
| S (_) -> begin
true
end
| _ -> begin
false
end))

let ___S____0 = (fun ( projectee ) -> (match (projectee) with
| S (_8_14) -> begin
_8_14
end))

let idnat = (fun ( x ) -> x)

let idnat2 = (fun ( x ) -> x)

let id = (fun ( x ) -> x)

let idp = (fun ( x ) -> x)

let idp' = (fun ( x ) -> x)

let add1 = (fun ( a ) -> S (a))

let add2 = (fun ( _17_42 ) -> S (_17_42))

let eval_order = (fun ( effectful ) ( f ) -> (let _17_62 = (effectful "first")
in (f _17_62 "second")))

let prev = (fun ( _8_1 ) -> (match (_8_1) with
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

let uu___is_Nil2 = (fun ( _discr_ ) -> (match (_discr_) with
| Nil2 -> begin
true
end
| _ -> begin
false
end))

let uu___is_Cons2 = (fun ( _discr_ ) -> (match (_discr_) with
| Cons2 (_) -> begin
true
end
| _ -> begin
false
end))

let ___Cons2___hd = (fun ( projectee ) -> (match (projectee) with
| Cons2 (_8_45, _8_46, _8_47) -> begin
_8_45
end))

let ___Cons2___hd2 = (fun ( projectee ) -> (match (projectee) with
| Cons2 (_8_49, _8_48, _8_50) -> begin
_8_48
end))

let ___Cons2___tl = (fun ( projectee ) -> (match (projectee) with
| Cons2 (_8_52, _8_53, _8_51) -> begin
_8_51
end))

type any =
| Any of unit * Obj.t

let uu___is_Any = (fun ( _discr_ ) -> (match (_discr_) with
| Any (_) -> begin
true
end
| _ -> begin
false
end))

let ___Any____1 = (fun ( projectee ) -> (match (projectee) with
| Any (_, _8_56) -> begin
(Obj.magic _8_56)
end))

type distr_pair =
(unit  ->  Obj.t  ->  Obj.t)  ->  (nnat, nnat list) prod

type 'a list2p =
| Nil2p
| Cons2p of 'a * ('a, 'a) prod list2p

let uu___is_Nil2p = (fun ( _discr_ ) -> (match (_discr_) with
| Nil2p -> begin
true
end
| _ -> begin
false
end))

let uu___is_Cons2p = (fun ( _discr_ ) -> (match (_discr_) with
| Cons2p (_) -> begin
true
end
| _ -> begin
false
end))

let ___Cons2p___hd = (fun ( projectee ) -> (match (projectee) with
| Cons2p (_8_66, _8_67) -> begin
_8_66
end))

let ___Cons2p___tl = (fun ( projectee ) -> (match (projectee) with
| Cons2p (_8_69, _8_68) -> begin
_8_68
end))

type 'dummyV1 list3 =
| Nil3 of unit
| Cons3 of unit * Obj.t * Obj.t list3

let uu___is_Nil3 = (fun ( _discr_ ) -> (match (_discr_) with
| Nil3 (_) -> begin
true
end
| _ -> begin
false
end))

let uu___is_Cons3 = (fun ( _discr_ ) -> (match (_discr_) with
| Cons3 (_) -> begin
true
end
| _ -> begin
false
end))

let ___Cons3____1 = (fun ( projectee ) -> (match (projectee) with
| Cons3 (_, _8_76, _8_78) -> begin
(Obj.magic _8_76)
end))

let ___Cons3____2 = (fun ( projectee ) -> (match (projectee) with
| Cons3 (_, _8_81, _8_79) -> begin
(Obj.magic _8_79)
end))

type ' x poly =
| Poly of nnat * ' x

let uu___is_Poly = (fun ( _discr_ ) -> (match (_discr_) with
| Poly (_) -> begin
true
end
| _ -> begin
false
end))

let ___Poly___n = (fun ( projectee ) -> (match (projectee) with
| Poly (_8_85, _8_86) -> begin
_8_85
end))

let ___Poly____2 = (fun ( projectee ) -> (match (projectee) with
| Poly (_8_88, _8_87) -> begin
_8_87
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

let uu___is_Nill = (fun ( _discr_ ) -> (match (_discr_) with
| Nill -> begin
true
end
| _ -> begin
false
end))

let uu___is_Conss = (fun ( _discr_ ) -> (match (_discr_) with
| Conss (_) -> begin
true
end
| _ -> begin
false
end))

let ___Conss___n = (fun ( _1 ) ( projectee ) -> (match (projectee) with
| Conss (_8_100, _8_101, _8_102) -> begin
_8_100
end))

let ___Conss____2 = (fun ( _1 ) ( projectee ) -> (match (projectee) with
| Conss (_8_104, _8_103, _8_105) -> begin
_8_103
end))

let ___Conss____3 = (fun ( _1 ) ( projectee ) -> (match (projectee) with
| Conss (_8_107, _8_108, _8_106) -> begin
_8_106
end))

type vecn1 =
(nnat, unit) vec

type (' t, ' n) naryTree =
| Leaf
| Node of ((' t, unit) naryTree, unit) vec

let uu___is_Leaf = (fun ( _discr_ ) -> (match (_discr_) with
| Leaf -> begin
true
end
| _ -> begin
false
end))

let uu___is_Node = (fun ( _discr_ ) -> (match (_discr_) with
| Node (_) -> begin
true
end
| _ -> begin
false
end))

let ___Leaf___n = (fun ( n ) ( projectee ) -> (match (projectee) with
| Leaf -> begin
()
end))

let ___Node___n = (fun ( n ) ( projectee ) -> (match (projectee) with
| Node (_8_117) -> begin
()
end))

let ___Node____2 = (fun ( n ) ( projectee ) -> (match (projectee) with
| Node (_8_118) -> begin
_8_118
end))

let two = S (S (O))

type ' t binaryTree =
(' t, unit) naryTree

let binLeaf = Leaf

let binNode = Node (Conss (S (O), binLeaf, Conss (O, binLeaf, Nill)))

type polyvec =
(nnat, unit) vec poly

type 'a listalias =
'a list

type ' a evenlist =
| ENil
| ECons of ' a * ' a oddlist 
 and ' a oddlist =
| OCons of ' a * ' a evenlist

let uu___is_ENil = (fun ( _discr_ ) -> (match (_discr_) with
| ENil -> begin
true
end
| _ -> begin
false
end))

let uu___is_ECons = (fun ( _discr_ ) -> (match (_discr_) with
| ECons (_) -> begin
true
end
| _ -> begin
false
end))

let uu___is_OCons = (fun ( _discr_ ) -> (match (_discr_) with
| OCons (_) -> begin
true
end
| _ -> begin
false
end))

let ___ECons___hd = (fun ( projectee ) -> (match (projectee) with
| ECons (_8_132, _8_133) -> begin
_8_132
end))

let ___ECons___tl = (fun ( projectee ) -> (match (projectee) with
| ECons (_8_135, _8_134) -> begin
_8_134
end))

let ___OCons___hd = (fun ( projectee ) -> (match (projectee) with
| OCons (_8_137, _8_138) -> begin
_8_137
end))

let ___OCons___tl = (fun ( projectee ) -> (match (projectee) with
| OCons (_8_140, _8_139) -> begin
_8_139
end))

type 'dummyV1 isEven =
| Ev0
| EvSOdd of nnat * unit isOdd 
 and 'dummyV1 isOdd =
| OddSEven of nnat * unit isEven

let uu___is_Ev0 = (fun ( _discr_ ) -> (match (_discr_) with
| Ev0 -> begin
true
end
| _ -> begin
false
end))

let uu___is_EvSOdd = (fun ( _discr_ ) -> (match (_discr_) with
| EvSOdd (_) -> begin
true
end
| _ -> begin
false
end))

let uu___is_OddSEven = (fun ( _discr_ ) -> (match (_discr_) with
| OddSEven (_) -> begin
true
end
| _ -> begin
false
end))

let ___EvSOdd___n = (fun ( _0 ) ( projectee ) -> (match (projectee) with
| EvSOdd (_8_145, _8_146) -> begin
_8_145
end))

let ___EvSOdd____1 = (fun ( _0 ) ( projectee ) -> (match (projectee) with
| EvSOdd (_8_148, _8_147) -> begin
_8_147
end))

let ___OddSEven___n = (fun ( _0 ) ( projectee ) -> (match (projectee) with
| OddSEven (_8_150, _8_151) -> begin
_8_150
end))

let ___OddSEven____1 = (fun ( _0 ) ( projectee ) -> (match (projectee) with
| OddSEven (_8_153, _8_152) -> begin
_8_152
end))

type node =
{frequency : int; next : node; zero_child : node ref; one_child : node; symbol : int; code : string}

let uu___is_Mknode = (fun ( _ ) -> (failwith "Not yet implemented:is\x5fMknode"))

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





