
open Prims
open FStar_Pervasives
type signedness =
| Unsigned
| Signed


let uu___is_Unsigned : signedness  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unsigned -> begin
true
end
| uu____5 -> begin
false
end))


let uu___is_Signed : signedness  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Signed -> begin
true
end
| uu____10 -> begin
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
| uu____15 -> begin
false
end))


let uu___is_Int16 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int16 -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Int32 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int32 -> begin
true
end
| uu____25 -> begin
false
end))


let uu___is_Int64 : width  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Int64 -> begin
true
end
| uu____30 -> begin
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
| Const_range of FStar_Range.range
| Const_reify
| Const_reflect of FStar_Ident.lid


let uu___is_Const_effect : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_effect -> begin
true
end
| uu____87 -> begin
false
end))


let uu___is_Const_unit : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_unit -> begin
true
end
| uu____92 -> begin
false
end))


let uu___is_Const_bool : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_bool (_0) -> begin
true
end
| uu____98 -> begin
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
| uu____122 -> begin
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
| uu____166 -> begin
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
| uu____180 -> begin
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
| uu____200 -> begin
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
| uu____236 -> begin
false
end))


let __proj__Const_string__item___0 : sconst  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Const_string (_0) -> begin
_0
end))


let uu___is_Const_range : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_range (_0) -> begin
true
end
| uu____262 -> begin
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
| uu____275 -> begin
false
end))


let uu___is_Const_reflect : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_reflect (_0) -> begin
true
end
| uu____281 -> begin
false
end))


let __proj__Const_reflect__item___0 : sconst  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Const_reflect (_0) -> begin
_0
end))


let eq_const : sconst  ->  sconst  ->  Prims.bool = (fun c1 c2 -> (match (((c1), (c2))) with
| (Const_int (s1, o1), Const_int (s2, o2)) -> begin
((

let uu____330 = (FStar_Util.ensure_decimal s1)
in (

let uu____331 = (FStar_Util.ensure_decimal s2)
in (Prims.op_Equality uu____330 uu____331))) && (Prims.op_Equality o1 o2))
end
| (Const_bytearray (a, uu____339), Const_bytearray (b, uu____341)) -> begin
(Prims.op_Equality a b)
end
| (Const_string (a, uu____353), Const_string (b, uu____355)) -> begin
(Prims.op_Equality a b)
end
| (Const_reflect (l1), Const_reflect (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| uu____358 -> begin
(Prims.op_Equality c1 c2)
end))


let rec pow2 : Prims.int  ->  Prims.int = (fun x -> (match (x) with
| _0_27 when (_0_27 = (Prims.parse_int "0")) -> begin
(Prims.parse_int "1")
end
| uu____367 -> begin
(

let uu____368 = (pow2 (x - (Prims.parse_int "1")))
in ((Prims.parse_int "2") * uu____368))
end))


let bounds : signedness  ->  width  ->  (Prims.int * Prims.int) = (fun signedness width -> (

let n1 = (match (width) with
| Int8 -> begin
(Prims.parse_int "8")
end
| Int16 -> begin
(Prims.parse_int "16")
end
| Int32 -> begin
(Prims.parse_int "32")
end
| Int64 -> begin
(Prims.parse_int "64")
end)
in (

let uu____382 = (match (signedness) with
| Unsigned -> begin
(

let uu____391 = (

let uu____392 = (pow2 n1)
in (uu____392 - (Prims.parse_int "1")))
in (((Prims.parse_int "0")), (uu____391)))
end
| Signed -> begin
(

let upper = (pow2 (n1 - (Prims.parse_int "1")))
in (((~- (upper))), ((upper - (Prims.parse_int "1")))))
end)
in (match (uu____382) with
| (lower, upper) -> begin
((lower), (upper))
end))))




