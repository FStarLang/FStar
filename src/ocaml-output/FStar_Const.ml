
open Prims

type signedness =
| Unsigned
| Signed


let is_Unsigned = (fun _discr_ -> (match (_discr_) with
| Unsigned (_) -> begin
true
end
| _ -> begin
false
end))


let is_Signed = (fun _discr_ -> (match (_discr_) with
| Signed (_) -> begin
true
end
| _ -> begin
false
end))


type width =
| Int8
| Int16
| Int32
| Int64


let is_Int8 = (fun _discr_ -> (match (_discr_) with
| Int8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int16 = (fun _discr_ -> (match (_discr_) with
| Int16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int32 = (fun _discr_ -> (match (_discr_) with
| Int32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int64 = (fun _discr_ -> (match (_discr_) with
| Int64 (_) -> begin
true
end
| _ -> begin
false
end))


type sconst =
| Const_effect
| Const_unit
| Const_bool of Prims.bool
| Const_int of (Prims.string * (signedness * width) Prims.option)
| Const_char of FStar_BaseTypes.char
| Const_float of FStar_BaseTypes.double
| Const_bytearray of (FStar_BaseTypes.byte Prims.array * FStar_Range.range)
| Const_string of (FStar_BaseTypes.byte Prims.array * FStar_Range.range)
| Const_range of FStar_Range.range
| Const_reify
| Const_reflect of FStar_Ident.lid


let is_Const_effect = (fun _discr_ -> (match (_discr_) with
| Const_effect (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_unit = (fun _discr_ -> (match (_discr_) with
| Const_unit (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_bool = (fun _discr_ -> (match (_discr_) with
| Const_bool (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_int = (fun _discr_ -> (match (_discr_) with
| Const_int (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_char = (fun _discr_ -> (match (_discr_) with
| Const_char (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_float = (fun _discr_ -> (match (_discr_) with
| Const_float (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_bytearray = (fun _discr_ -> (match (_discr_) with
| Const_bytearray (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_string = (fun _discr_ -> (match (_discr_) with
| Const_string (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_range = (fun _discr_ -> (match (_discr_) with
| Const_range (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_reify = (fun _discr_ -> (match (_discr_) with
| Const_reify (_) -> begin
true
end
| _ -> begin
false
end))


let is_Const_reflect = (fun _discr_ -> (match (_discr_) with
| Const_reflect (_) -> begin
true
end
| _ -> begin
false
end))


let ___Const_bool____0 = (fun projectee -> (match (projectee) with
| Const_bool (_27_3) -> begin
_27_3
end))


let ___Const_int____0 = (fun projectee -> (match (projectee) with
| Const_int (_27_6) -> begin
_27_6
end))


let ___Const_char____0 = (fun projectee -> (match (projectee) with
| Const_char (_27_9) -> begin
_27_9
end))


let ___Const_float____0 = (fun projectee -> (match (projectee) with
| Const_float (_27_12) -> begin
_27_12
end))


let ___Const_bytearray____0 = (fun projectee -> (match (projectee) with
| Const_bytearray (_27_15) -> begin
_27_15
end))


let ___Const_string____0 = (fun projectee -> (match (projectee) with
| Const_string (_27_18) -> begin
_27_18
end))


let ___Const_range____0 = (fun projectee -> (match (projectee) with
| Const_range (_27_21) -> begin
_27_21
end))


let ___Const_reflect____0 = (fun projectee -> (match (projectee) with
| Const_reflect (_27_24) -> begin
_27_24
end))


let eq_const : sconst  ->  sconst  ->  Prims.bool = (fun c1 c2 -> (match (((c1), (c2))) with
| (Const_int (s1, o1), Const_int (s2, o2)) -> begin
(((FStar_Util.ensure_decimal s1) = (FStar_Util.ensure_decimal s2)) && (o1 = o2))
end
| ((Const_bytearray (a, _), Const_bytearray (b, _))) | ((Const_string (a, _), Const_string (b, _))) -> begin
(a = b)
end
| (Const_reflect (l1), Const_reflect (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| _27_62 -> begin
(c1 = c2)
end))




