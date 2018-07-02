
open Prims
open FStar_Pervasives
type signedness =
| Unsigned
| Signed


let uu___is_Unsigned : signedness  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unsigned -> begin
true
end
| uu____6 -> begin
false
end))


let uu___is_Signed : signedness  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Signed -> begin
true
end
| uu____12 -> begin
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
| uu____18 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____36 -> begin
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
| uu____104 -> begin
false
end))


let uu___is_Const_unit : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_unit -> begin
true
end
| uu____110 -> begin
false
end))


let uu___is_Const_bool : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_bool (_0) -> begin
true
end
| uu____117 -> begin
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
| uu____141 -> begin
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
| uu____186 -> begin
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
| uu____203 -> begin
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
| uu____224 -> begin
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
| uu____263 -> begin
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
| uu____288 -> begin
false
end))


let uu___is_Const_set_range_of : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_set_range_of -> begin
true
end
| uu____294 -> begin
false
end))


let uu___is_Const_range : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_range (_0) -> begin
true
end
| uu____301 -> begin
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
| uu____314 -> begin
false
end))


let uu___is_Const_reflect : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_reflect (_0) -> begin
true
end
| uu____321 -> begin
false
end))


let __proj__Const_reflect__item___0 : sconst  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Const_reflect (_0) -> begin
_0
end))


let eq_const : sconst  ->  sconst  ->  Prims.bool = (fun c1 c2 -> (match (((c1), (c2))) with
| (Const_int (s1, o1), Const_int (s2, o2)) -> begin
((

let uu____371 = (FStar_Util.ensure_decimal s1)
in (

let uu____372 = (FStar_Util.ensure_decimal s2)
in (Prims.op_Equality uu____371 uu____372))) && (Prims.op_Equality o1 o2))
end
| (Const_bytearray (a, uu____380), Const_bytearray (b, uu____382)) -> begin
(Prims.op_Equality a b)
end
| (Const_string (a, uu____399), Const_string (b, uu____401)) -> begin
(Prims.op_Equality a b)
end
| (Const_reflect (l1), Const_reflect (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| uu____404 -> begin
(Prims.op_Equality c1 c2)
end))


let rec pow2 : FStar_BigInt.bigint  ->  FStar_BigInt.bigint = (fun x -> (

let uu____414 = (FStar_BigInt.eq_big_int x FStar_BigInt.zero)
in (match (uu____414) with
| true -> begin
FStar_BigInt.one
end
| uu____415 -> begin
(

let uu____416 = (

let uu____417 = (FStar_BigInt.pred_big_int x)
in (pow2 uu____417))
in (FStar_BigInt.mult_big_int FStar_BigInt.two uu____416))
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

let uu____433 = (match (signedness) with
| Unsigned -> begin
(

let uu____442 = (

let uu____443 = (pow2 n1)
in (FStar_BigInt.pred_big_int uu____443))
in ((FStar_BigInt.zero), (uu____442)))
end
| Signed -> begin
(

let upper = (

let uu____445 = (FStar_BigInt.pred_big_int n1)
in (pow2 uu____445))
in (

let uu____446 = (FStar_BigInt.minus_big_int upper)
in (

let uu____447 = (FStar_BigInt.pred_big_int upper)
in ((uu____446), (uu____447)))))
end)
in (match (uu____433) with
| (lower, upper) -> begin
((lower), (upper))
end))))


let within_bounds : Prims.string  ->  signedness  ->  width  ->  Prims.bool = (fun repr signedness width -> (

let uu____469 = (bounds signedness width)
in (match (uu____469) with
| (lower, upper) -> begin
(

let value = (

let uu____477 = (FStar_Util.ensure_decimal repr)
in (FStar_BigInt.big_int_of_string uu____477))
in ((FStar_BigInt.le_big_int lower value) && (FStar_BigInt.le_big_int value upper)))
end)))




