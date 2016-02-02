
open Prims
type sconst =
| Const_effect
| Const_unit
| Const_uint8 of Prims.byte
| Const_bool of Prims.bool
| Const_int32 of Prims.int32
| Const_int64 of Prims.int64
| Const_int of Prims.string
| Const_char of Prims.char
| Const_float of Prims.double
| Const_bytearray of (Prims.byte Prims.array * FStar_Range.range)
| Const_string of (Prims.byte Prims.array * FStar_Range.range)

let is_Const_effect = (fun _discr_ -> (match (_discr_) with
| Const_effect -> begin
true
end
| _ -> begin
false
end))

let is_Const_unit = (fun _discr_ -> (match (_discr_) with
| Const_unit -> begin
true
end
| _ -> begin
false
end))

let is_Const_uint8 = (fun _discr_ -> (match (_discr_) with
| Const_uint8 (_) -> begin
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

let is_Const_int32 = (fun _discr_ -> (match (_discr_) with
| Const_int32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int64 = (fun _discr_ -> (match (_discr_) with
| Const_int64 (_) -> begin
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

let ___Const_uint8____0 = (fun projectee -> (match (projectee) with
| Const_uint8 (_23_3) -> begin
_23_3
end))

let ___Const_bool____0 = (fun projectee -> (match (projectee) with
| Const_bool (_23_6) -> begin
_23_6
end))

let ___Const_int32____0 = (fun projectee -> (match (projectee) with
| Const_int32 (_23_9) -> begin
_23_9
end))

let ___Const_int64____0 = (fun projectee -> (match (projectee) with
| Const_int64 (_23_12) -> begin
_23_12
end))

let ___Const_int____0 = (fun projectee -> (match (projectee) with
| Const_int (_23_15) -> begin
_23_15
end))

let ___Const_char____0 = (fun projectee -> (match (projectee) with
| Const_char (_23_18) -> begin
_23_18
end))

let ___Const_float____0 = (fun projectee -> (match (projectee) with
| Const_float (_23_21) -> begin
_23_21
end))

let ___Const_bytearray____0 = (fun projectee -> (match (projectee) with
| Const_bytearray (_23_24) -> begin
_23_24
end))

let ___Const_string____0 = (fun projectee -> (match (projectee) with
| Const_string (_23_27) -> begin
_23_27
end))




