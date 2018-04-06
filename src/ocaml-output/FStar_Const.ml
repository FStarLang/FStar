
open Prims
open FStar_Pervasives
type signedness =
| Unsigned
| Signed


let uu___is_Unsigned : signedness  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unsigned -> begin
true
end
| uu____4 -> begin
false
end))


let uu___is_Signed : signedness  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Signed -> begin
true
end
| uu____8 -> begin
false
end))

type width =
| Int8
| Int16
| Int32
| Int64


let uu___is_Int8 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int8 -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____16 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____24 -> begin
false
end))

type sconst =
| Const_effect
| Const_unit
| Const_bool of Prims.bool
| Const_int of (Prims.string * (signedness * width) FStar_Pervasives_Native.option)
| Const_char of FStar_BaseTypes.char
| Const_float of FStar_BaseTypes.double
| Const_bytearray of (FStar_BaseTypes.byte Prims.array * FStar_Range.range)
| Const_string of (Prims.string * FStar_Range.range)
| Const_range_of
| Const_set_range_of
| Const_range of FStar_Range.range
| Const_reify
| Const_reflect of FStar_Ident.lid


let uu___is_Const_effect : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_effect -> begin
true
end
| uu____80 -> begin
false
end))


let uu___is_Const_unit : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_unit -> begin
true
end
| uu____84 -> begin
false
end))


let uu___is_Const_bool : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_bool (_0) -> begin
true
end
| uu____89 -> begin
false
end))


let __proj__Const_bool__item___0 : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_bool (_0) -> begin
_0
end))


let uu___is_Const_int : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_int (_0) -> begin
true
end
| uu____111 -> begin
false
end))


let __proj__Const_int__item___0 : sconst  ->  (Prims.string * (signedness * width) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Const_int (_0) -> begin
_0
end))


let uu___is_Const_char : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_char (_0) -> begin
true
end
| uu____153 -> begin
false
end))


let __proj__Const_char__item___0 : sconst  ->  FStar_BaseTypes.char = (fun projectee -> (match (projectee) with
| Const_char (_0) -> begin
_0
end))


let uu___is_Const_float : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_float (_0) -> begin
true
end
| uu____165 -> begin
false
end))


let __proj__Const_float__item___0 : sconst  ->  FStar_BaseTypes.double = (fun projectee -> (match (projectee) with
| Const_float (_0) -> begin
_0
end))


let uu___is_Const_bytearray : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_bytearray (_0) -> begin
true
end
| uu____183 -> begin
false
end))


let __proj__Const_bytearray__item___0 : sconst  ->  (FStar_BaseTypes.byte Prims.array * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Const_bytearray (_0) -> begin
_0
end))


let uu___is_Const_string : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_string (_0) -> begin
true
end
| uu____217 -> begin
false
end))


let __proj__Const_string__item___0 : sconst  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Const_string (_0) -> begin
_0
end))


let uu___is_Const_range_of : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_range_of -> begin
true
end
| uu____240 -> begin
false
end))


let uu___is_Const_set_range_of : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_set_range_of -> begin
true
end
| uu____244 -> begin
false
end))


let uu___is_Const_range : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_range (_0) -> begin
true
end
| uu____249 -> begin
false
end))


let __proj__Const_range__item___0 : sconst  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| Const_range (_0) -> begin
_0
end))


let uu___is_Const_reify : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_reify -> begin
true
end
| uu____260 -> begin
false
end))


let uu___is_Const_reflect : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_reflect (_0) -> begin
true
end
| uu____265 -> begin
false
end))


let __proj__Const_reflect__item___0 : sconst  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Const_reflect (_0) -> begin
_0
end))


let eq_const : sconst  ->  sconst  ->  Prims.bool = (fun c1 c2 -> (match (((c1), (c2))) with
| (Const_int (s1, o1), Const_int (s2, o2)) -> begin
((

let uu____311 = (FStar_Util.ensure_decimal s1)
in (

let uu____312 = (FStar_Util.ensure_decimal s2)
in (Prims.op_Equality uu____311 uu____312))) && (Prims.op_Equality o1 o2))
end
| (Const_bytearray (a, uu____320), Const_bytearray (b, uu____322)) -> begin
(Prims.op_Equality a b)
end
| (Const_string (a, uu____334), Const_string (b, uu____336)) -> begin
(Prims.op_Equality a b)
end
| (Const_reflect (l1), Const_reflect (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| uu____339 -> begin
(Prims.op_Equality c1 c2)
end))


let rec pow2 : FStar_BigInt.bigint  ->  FStar_BigInt.bigint = (fun x -> (

let uu____347 = (FStar_BigInt.eq_big_int x FStar_BigInt.zero)
in (match (uu____347) with
| true -> begin
FStar_BigInt.one
end
| uu____348 -> begin
(

let uu____349 = (

let uu____350 = (FStar_BigInt.pred_big_int x)
in (pow2 uu____350))
in (FStar_BigInt.mult_big_int FStar_BigInt.two uu____349))
end)))


let bounds : signedness  ->  width  ->  (FStar_BigInt.bigint * FStar_BigInt.bigint) = (fun signedness width -> (

let n1 = (match (width) with
| Int8 -> begin
(FStar_BigInt.big_int_of_string "8")
end
| Int16 -> begin
(FStar_BigInt.big_int_of_string "16")
end
| Int32 -> begin
(FStar_BigInt.big_int_of_string "32")
end
| Int64 -> begin
(FStar_BigInt.big_int_of_string "64")
end)
in (

let uu____362 = (match (signedness) with
| Unsigned -> begin
(

let uu____371 = (

let uu____372 = (pow2 n1)
in (FStar_BigInt.pred_big_int uu____372))
in ((FStar_BigInt.zero), (uu____371)))
end
| Signed -> begin
(

let upper = (

let uu____374 = (FStar_BigInt.pred_big_int n1)
in (pow2 uu____374))
in (

let uu____375 = (FStar_BigInt.minus_big_int upper)
in (

let uu____376 = (FStar_BigInt.pred_big_int upper)
in ((uu____375), (uu____376)))))
end)
in (match (uu____362) with
| (lower, upper) -> begin
((lower), (upper))
end))))


let within_bounds : Prims.string  ->  signedness  ->  width  ->  Prims.bool = (fun repr signedness width -> (

let uu____392 = (bounds signedness width)
in (match (uu____392) with
| (lower, upper) -> begin
(

let value = (

let uu____400 = (FStar_Util.ensure_decimal repr)
in (FStar_BigInt.big_int_of_string uu____400))
in ((FStar_BigInt.le_big_int lower value) && (FStar_BigInt.le_big_int value upper)))
end)))




