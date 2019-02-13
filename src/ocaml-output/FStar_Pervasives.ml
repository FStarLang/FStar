
open Prims

type ('Aa, 'Ax) ambient =
unit





let id : 'Aa . 'Aa  ->  'Aa = (fun x -> x)


type 'Aheap st_pre_h =
unit


type ('Aheap, 'Aa, 'Apre) st_post_h' =
unit


type ('Aheap, 'Aa) st_post_h =
unit


type ('Aheap, 'Aa) st_wp_h =
unit


type ('Aheap, 'Aa, 'Ax, 'Ap, 'Auu___6_91) st_return =
'Ap


type ('Aheap, 'Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap, 'Ah0) st_bind_wp =
'Awp1


type ('Aheap, 'Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost, 'Ah0) st_if_then_else =
unit


type ('Aheap, 'Aa, 'Awp, 'Apost, 'Ah0) st_ite_wp =
unit


type ('Aheap, 'Aa, 'Awp1, 'Awp2) st_stronger =
unit


type ('Aheap, 'Aa, 'Ab, 'Awp, 'Ap, 'Ah) st_close_wp =
unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) st_assert_p =
unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) st_assume_p =
unit


type ('Aheap, 'Aa, 'Ap, 'Ah) st_null_wp =
unit


type ('Aheap, 'Aa, 'Awp) st_trivial =
unit

type 'Aa result =
| V of 'Aa
| E of Prims.exn
| Err of Prims.string


let uu___is_V : 'Aa . 'Aa result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| V (v) -> begin
true
end
| uu____424 -> begin
false
end))


let __proj__V__item__v : 'Aa . 'Aa result  ->  'Aa = (fun projectee -> (match (projectee) with
| V (v) -> begin
v
end))


let uu___is_E : 'Aa . 'Aa result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| E (e) -> begin
true
end
| uu____463 -> begin
false
end))


let __proj__E__item__e : 'Aa . 'Aa result  ->  Prims.exn = (fun projectee -> (match (projectee) with
| E (e) -> begin
e
end))


let uu___is_Err : 'Aa . 'Aa result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (msg) -> begin
true
end
| uu____503 -> begin
false
end))


let __proj__Err__item__msg : 'Aa . 'Aa result  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (msg) -> begin
msg
end))


type ex_pre =
unit


type ('Aa, 'Apre) ex_post' =
unit


type 'Aa ex_post =
unit


type 'Aa ex_wp =
unit


type ('Aa, 'Ax, 'Ap) ex_return =
'Ap


type ('Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap) ex_bind_wp =
unit


type ('Aa, 'Awp, 'Apost) ex_ite_wp =
unit


type ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) ex_if_then_else =
unit


type ('Aa, 'Awp1, 'Awp2) ex_stronger =
unit


type ('Aa, 'Ab, 'Awp, 'Ap) ex_close_wp =
unit


type ('Aa, 'Aq, 'Awp, 'Ap) ex_assert_p =
unit


type ('Aa, 'Aq, 'Awp, 'Ap) ex_assume_p =
unit


type ('Aa, 'Ap) ex_null_wp =
unit


type ('Aa, 'Awp) ex_trivial =
'Awp


type ('Aa, 'Awp, 'Ap) lift_div_exn =
'Awp


type 'Ah all_pre_h =
unit


type ('Ah, 'Aa, 'Apre) all_post_h' =
unit


type ('Ah, 'Aa) all_post_h =
unit


type ('Ah, 'Aa) all_wp_h =
unit


type ('Aheap, 'Aa, 'Awp, 'Apost, 'Ah0) all_ite_wp =
unit


type ('Aheap, 'Aa, 'Ax, 'Ap, 'Auu___9_874) all_return =
'Ap


type ('Aheap, 'Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap, 'Ah0) all_bind_wp =
'Awp1


type ('Aheap, 'Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost, 'Ah0) all_if_then_else =
unit


type ('Aheap, 'Aa, 'Awp1, 'Awp2) all_stronger =
unit


type ('Aheap, 'Aa, 'Ab, 'Awp, 'Ap, 'Ah) all_close_wp =
unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) all_assert_p =
unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) all_assume_p =
unit


type ('Aheap, 'Aa, 'Ap, 'Ah0) all_null_wp =
unit


type ('Aheap, 'Aa, 'Awp) all_trivial =
unit


type 'Aa inversion =
unit







type ('a, 'b) either =
| Inl of 'a
| Inr of 'b


let uu___is_Inl : 'a 'b . ('a, 'b) either  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inl (v) -> begin
true
end
| uu____1192 -> begin
false
end))


let __proj__Inl__item__v : 'a 'b . ('a, 'b) either  ->  'a = (fun projectee -> (match (projectee) with
| Inl (v) -> begin
v
end))


let uu___is_Inr : 'a 'b . ('a, 'b) either  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inr (v) -> begin
true
end
| uu____1247 -> begin
false
end))


let __proj__Inr__item__v : 'a 'b . ('a, 'b) either  ->  'b = (fun projectee -> (match (projectee) with
| Inr (v) -> begin
v
end))


let dfst : 'Aa 'Ab . ('Aa, 'Ab) Prims.dtuple2  ->  'Aa = (fun t -> (Prims.__proj__Mkdtuple2__item___1 t))


let dsnd : 'Aa 'Ab . ('Aa, 'Ab) Prims.dtuple2  ->  'Ab = (fun t -> (Prims.__proj__Mkdtuple2__item___2 t))





let rec false_elim : 'Aa . unit  ->  'Aa = (fun u -> (false_elim ()))

type __internal_ocaml_attributes =
| PpxDerivingShow
| PpxDerivingShowConstant of Prims.string
| PpxDerivingYoJson
| CInline
| Substitute
| Gc
| Comment of Prims.string
| CPrologue of Prims.string
| CEpilogue of Prims.string
| CConst of Prims.string
| CCConv of Prims.string
| CAbstractStruct


let uu___is_PpxDerivingShow : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShow -> begin
true
end
| uu____1386 -> begin
false
end))


let uu___is_PpxDerivingShowConstant : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
true
end
| uu____1399 -> begin
false
end))


let __proj__PpxDerivingShowConstant__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
_0
end))


let uu___is_PpxDerivingYoJson : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingYoJson -> begin
true
end
| uu____1421 -> begin
false
end))


let uu___is_CInline : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____1432 -> begin
false
end))


let uu___is_Substitute : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____1443 -> begin
false
end))


let uu___is_Gc : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gc -> begin
true
end
| uu____1454 -> begin
false
end))


let uu___is_Comment : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____1467 -> begin
false
end))


let __proj__Comment__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
_0
end))


let uu___is_CPrologue : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CPrologue (_0) -> begin
true
end
| uu____1491 -> begin
false
end))


let __proj__CPrologue__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| CPrologue (_0) -> begin
_0
end))


let uu___is_CEpilogue : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CEpilogue (_0) -> begin
true
end
| uu____1515 -> begin
false
end))


let __proj__CEpilogue__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| CEpilogue (_0) -> begin
_0
end))


let uu___is_CConst : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CConst (_0) -> begin
true
end
| uu____1539 -> begin
false
end))


let __proj__CConst__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| CConst (_0) -> begin
_0
end))


let uu___is_CCConv : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CCConv (_0) -> begin
true
end
| uu____1563 -> begin
false
end))


let __proj__CCConv__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| CCConv (_0) -> begin
_0
end))


let uu___is_CAbstractStruct : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CAbstractStruct -> begin
true
end
| uu____1585 -> begin
false
end))



































let normalize_term : 'Aa . 'Aa  ->  'Aa = (fun x -> x)


type 'Aa normalize =
'Aa

type norm_step =
| Simpl
| Weak
| HNF
| Primops
| Delta
| Zeta
| Iota
| NBE
| Reify
| UnfoldOnly of Prims.string Prims.list
| UnfoldFully of Prims.string Prims.list
| UnfoldAttr of Prims.string Prims.list


let uu___is_Simpl : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simpl -> begin
true
end
| uu____1650 -> begin
false
end))


let uu___is_Weak : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Weak -> begin
true
end
| uu____1661 -> begin
false
end))


let uu___is_HNF : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____1672 -> begin
false
end))


let uu___is_Primops : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____1683 -> begin
false
end))


let uu___is_Delta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta -> begin
true
end
| uu____1694 -> begin
false
end))


let uu___is_Zeta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____1705 -> begin
false
end))


let uu___is_Iota : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____1716 -> begin
false
end))


let uu___is_NBE : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NBE -> begin
true
end
| uu____1727 -> begin
false
end))


let uu___is_Reify : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____1738 -> begin
false
end))


let uu___is_UnfoldOnly : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____1753 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldFully : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
true
end
| uu____1785 -> begin
false
end))


let __proj__UnfoldFully__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu____1817 -> begin
false
end))


let __proj__UnfoldAttr__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let simplify : norm_step = Simpl


let weak : norm_step = Weak


let hnf : norm_step = HNF


let primops : norm_step = Primops


let delta : norm_step = Delta


let zeta : norm_step = Zeta


let iota : norm_step = Iota


let nbe : norm_step = NBE


let reify_ : norm_step = Reify


let delta_only : Prims.string Prims.list  ->  norm_step = (fun s -> UnfoldOnly (s))


let delta_fully : Prims.string Prims.list  ->  norm_step = (fun s -> UnfoldFully (s))


let delta_attr : Prims.string Prims.list  ->  norm_step = (fun s -> UnfoldAttr (s))


let norm : norm_step Prims.list  ->  unit  ->  Obj.t  ->  Obj.t = (fun s a x -> x)

















let singleton : 'Aa . 'Aa  ->  'Aa = (fun x -> x)


let with_type : 'At . 'At  ->  'At = (fun e -> e)




