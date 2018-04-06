
open Prims

let id : 'Aa . 'Aa  ->  'Aa = (fun x -> x)


type 'Aheap st_pre_h =
'Aheap  ->  Prims.prop


type ('Aheap, 'Aa, 'Apre) st_post_h' =
'Aa  ->  'Aheap  ->  Prims.prop


type ('Aheap, 'Aa) st_post_h =
('Aheap, 'Aa, Prims.unit) st_post_h'


type ('Aheap, 'Aa) st_wp_h =
Prims.unit  ->  'Aheap st_pre_h


type ('Aheap, 'Aa, 'Ax, 'Ap, 'Auu___9_127) st_return =
'Ap


type ('Aheap, 'Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap, 'Ah0) st_bind_wp =
'Awp1


type ('Aheap, 'Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost, 'Ah0) st_if_then_else =
Prims.unit


type ('Aheap, 'Aa, 'Awp, 'Apost, 'Ah0) st_ite_wp =
Prims.unit


type ('Aheap, 'Aa, 'Awp1, 'Awp2) st_stronger =
Prims.unit


type ('Aheap, 'Aa, 'Ab, 'Awp, 'Ap, 'Ah) st_close_wp =
Prims.unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) st_assert_p =
Prims.unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) st_assume_p =
Prims.unit


type ('Aheap, 'Aa, 'Ap, 'Ah) st_null_wp =
Prims.unit


type ('Aheap, 'Aa, 'Awp) st_trivial =
Prims.unit

type 'Aa result =
| V of 'Aa
| E of Prims.exn
| Err of Prims.string


let uu___is_V : 'Aa . 'Aa result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| V (v) -> begin
true
end
| uu____1370 -> begin
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
| uu____1400 -> begin
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
| uu____1430 -> begin
false
end))


let __proj__Err__item__msg : 'Aa . 'Aa result  ->  Prims.string = (fun projectee -> (match (projectee) with
| Err (msg) -> begin
msg
end))


type ex_pre =
Obj.t


type ('Aa, 'Apre) ex_post' =
'Aa result  ->  Prims.prop


type 'Aa ex_post =
('Aa, Prims.unit) ex_post'


type 'Aa ex_wp =
Prims.unit  ->  ex_pre


type ('Aa, 'Ax, 'Ap) ex_return =
'Ap


type ('Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap) ex_bind_wp =
Prims.unit


type ('Aa, 'Awp, 'Apost) ex_ite_wp =
Prims.unit


type ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) ex_if_then_else =
Prims.unit


type ('Aa, 'Awp1, 'Awp2) ex_stronger =
Prims.unit


type ('Aa, 'Ab, 'Awp, 'Ap) ex_close_wp =
Prims.unit


type ('Aa, 'Aq, 'Awp, 'Ap) ex_assert_p =
Prims.unit


type ('Aa, 'Aq, 'Awp, 'Ap) ex_assume_p =
Prims.unit


type ('Aa, 'Ap) ex_null_wp =
Prims.unit


type ('Aa, 'Awp) ex_trivial =
'Awp


type ('Aa, 'Awp, 'Ap) lift_div_exn =
'Awp


type 'Ah all_pre_h =
'Ah  ->  Prims.prop


type ('Ah, 'Aa, 'Apre) all_post_h' =
'Aa result  ->  'Ah  ->  Prims.prop


type ('Ah, 'Aa) all_post_h =
('Ah, 'Aa, Prims.unit) all_post_h'


type ('Ah, 'Aa) all_wp_h =
Prims.unit  ->  'Ah all_pre_h


type ('Aheap, 'Aa, 'Awp, 'Apost, 'Ah0) all_ite_wp =
Prims.unit


type ('Aheap, 'Aa, 'Ax, 'Ap, 'Auu___12_3029) all_return =
'Ap


type ('Aheap, 'Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap, 'Ah0) all_bind_wp =
'Awp1


type ('Aheap, 'Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost, 'Ah0) all_if_then_else =
Prims.unit


type ('Aheap, 'Aa, 'Awp1, 'Awp2) all_stronger =
Prims.unit


type ('Aheap, 'Aa, 'Ab, 'Awp, 'Ap, 'Ah) all_close_wp =
Prims.unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) all_assert_p =
Prims.unit


type ('Aheap, 'Aa, 'Ap, 'Awp, 'Aq, 'Ah) all_assume_p =
Prims.unit


type ('Aheap, 'Aa, 'Ap, 'Ah0) all_null_wp =
Prims.unit


type ('Aheap, 'Aa, 'Awp) all_trivial =
Prims.unit


type 'Aa inversion =
Prims.unit


let allow_inversion : 'Aa . Prims.unit = ()


let invertOption : 'Aa . Prims.unit  ->  Prims.unit = (fun uu____4053 -> ())

type ('a, 'b) either =
| Inl of 'a
| Inr of 'b


let uu___is_Inl : 'a 'b . ('a, 'b) either  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inl (v) -> begin
true
end
| uu____4096 -> begin
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
| uu____4140 -> begin
false
end))


let __proj__Inr__item__v : 'a 'b . ('a, 'b) either  ->  'b = (fun projectee -> (match (projectee) with
| Inr (v) -> begin
v
end))


let dfst : 'Aa 'Ab . ('Aa, 'Ab) Prims.dtuple2  ->  'Aa = (fun t -> (Prims.__proj__Mkdtuple2__item___1 t))


let dsnd : 'Aa 'Ab . ('Aa, 'Ab) Prims.dtuple2  ->  'Ab = (fun t -> (Prims.__proj__Mkdtuple2__item___2 t))

type ('Aa, 'Ab, 'Ac) dtuple3 =
| Mkdtuple3 of 'Aa * 'Ab * 'Ac


let uu___is_Mkdtuple3 : 'Aa 'Ab 'Ac . ('Aa, 'Ab, 'Ac) dtuple3  ->  Prims.bool = (fun projectee -> true)


let __proj__Mkdtuple3__item___1 : 'Aa 'Ab 'Ac . ('Aa, 'Ab, 'Ac) dtuple3  ->  'Aa = (fun projectee -> (match (projectee) with
| Mkdtuple3 (_1, _2, _3) -> begin
_1
end))


let __proj__Mkdtuple3__item___2 : 'Aa 'Ab 'Ac . ('Aa, 'Ab, 'Ac) dtuple3  ->  'Ab = (fun projectee -> (match (projectee) with
| Mkdtuple3 (_1, _2, _3) -> begin
_2
end))


let __proj__Mkdtuple3__item___3 : 'Aa 'Ab 'Ac . ('Aa, 'Ab, 'Ac) dtuple3  ->  'Ac = (fun projectee -> (match (projectee) with
| Mkdtuple3 (_1, _2, _3) -> begin
_3
end))

type ('Aa, 'Ab, 'Ac, 'Ad) dtuple4 =
| Mkdtuple4 of 'Aa * 'Ab * 'Ac * 'Ad


let uu___is_Mkdtuple4 : 'Aa 'Ab 'Ac 'Ad . ('Aa, 'Ab, 'Ac, 'Ad) dtuple4  ->  Prims.bool = (fun projectee -> true)


let __proj__Mkdtuple4__item___1 : 'Aa 'Ab 'Ac 'Ad . ('Aa, 'Ab, 'Ac, 'Ad) dtuple4  ->  'Aa = (fun projectee -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_1
end))


let __proj__Mkdtuple4__item___2 : 'Aa 'Ab 'Ac 'Ad . ('Aa, 'Ab, 'Ac, 'Ad) dtuple4  ->  'Ab = (fun projectee -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_2
end))


let __proj__Mkdtuple4__item___3 : 'Aa 'Ab 'Ac 'Ad . ('Aa, 'Ab, 'Ac, 'Ad) dtuple4  ->  'Ac = (fun projectee -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_3
end))


let __proj__Mkdtuple4__item___4 : 'Aa 'Ab 'Ac 'Ad . ('Aa, 'Ab, 'Ac, 'Ad) dtuple4  ->  'Ad = (fun projectee -> (match (projectee) with
| Mkdtuple4 (_1, _2, _3, _4) -> begin
_4
end))


let ignore : 'Aa . 'Aa  ->  Prims.unit = (fun x -> ())


let rec false_elim : 'Aa . Prims.unit  ->  'Aa = (fun u -> (false_elim ()))

type __internal_ocaml_attributes =
| PpxDerivingShow
| PpxDerivingShowConstant of Prims.string
| CInline
| Substitute
| Gc
| Comment of Prims.string
| CPrologue of Prims.string
| CEpilogue of Prims.string
| CConst of Prims.string


let uu___is_PpxDerivingShow : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShow -> begin
true
end
| uu____4722 -> begin
false
end))


let uu___is_PpxDerivingShowConstant : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
true
end
| uu____4727 -> begin
false
end))


let __proj__PpxDerivingShowConstant__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| PpxDerivingShowConstant (_0) -> begin
_0
end))


let uu___is_CInline : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CInline -> begin
true
end
| uu____4738 -> begin
false
end))


let uu___is_Substitute : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Substitute -> begin
true
end
| uu____4742 -> begin
false
end))


let uu___is_Gc : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gc -> begin
true
end
| uu____4746 -> begin
false
end))


let uu___is_Comment : __internal_ocaml_attributes  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Comment (_0) -> begin
true
end
| uu____4751 -> begin
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
| uu____4763 -> begin
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
| uu____4775 -> begin
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
| uu____4787 -> begin
false
end))


let __proj__CConst__item___0 : __internal_ocaml_attributes  ->  Prims.string = (fun projectee -> (match (projectee) with
| CConst (_0) -> begin
_0
end))


let deprecated : Prims.string  ->  Prims.unit = (fun s -> ())


let inline_let : Prims.unit = ()


let plugin : Prims.unit = ()


let dm4f_bind_range : Prims.unit = ()




