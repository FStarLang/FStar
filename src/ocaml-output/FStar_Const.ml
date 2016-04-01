
open Prims
# 4 "FStar.Const.fst"
type signedness =
| Unsigned
| Signed

# 6 "FStar.Const.fst"
let is_Unsigned = (fun _discr_ -> (match (_discr_) with
| Unsigned (_) -> begin
true
end
| _ -> begin
false
end))

# 6 "FStar.Const.fst"
let is_Signed = (fun _discr_ -> (match (_discr_) with
| Signed (_) -> begin
true
end
| _ -> begin
false
end))

# 6 "FStar.Const.fst"
type width =
| Int8
| Int16
| Int32
| Int64

# 7 "FStar.Const.fst"
let is_Int8 = (fun _discr_ -> (match (_discr_) with
| Int8 (_) -> begin
true
end
| _ -> begin
false
end))

# 7 "FStar.Const.fst"
let is_Int16 = (fun _discr_ -> (match (_discr_) with
| Int16 (_) -> begin
true
end
| _ -> begin
false
end))

# 7 "FStar.Const.fst"
let is_Int32 = (fun _discr_ -> (match (_discr_) with
| Int32 (_) -> begin
true
end
| _ -> begin
false
end))

# 7 "FStar.Const.fst"
let is_Int64 = (fun _discr_ -> (match (_discr_) with
| Int64 (_) -> begin
true
end
| _ -> begin
false
end))

# 7 "FStar.Const.fst"
let string_of_int_qualifier : (signedness * width)  ->  Prims.string = (fun _26_1 -> (match (_26_1) with
| (Unsigned, Int8) -> begin
"FStar.UInt8.uint8"
end
| (Signed, Int8) -> begin
"FStar.Int8.unt8"
end
| (Unsigned, Int16) -> begin
"FStar.UInt16.uint16"
end
| (Signed, Int16) -> begin
"FStar.Int16.int16"
end
| (Unsigned, Int32) -> begin
"FStar.UInt32.uint32"
end
| (Signed, Int32) -> begin
"FStar.Int32.int32"
end
| (Unsigned, Int64) -> begin
"FStar.UInt64.uint64"
end
| (Signed, Int64) -> begin
"FStar.Int64.int64"
end))

# 17 "FStar.Const.fst"
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

# 20 "FStar.Const.fst"
let is_Const_effect = (fun _discr_ -> (match (_discr_) with
| Const_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 21 "FStar.Const.fst"
let is_Const_unit = (fun _discr_ -> (match (_discr_) with
| Const_unit (_) -> begin
true
end
| _ -> begin
false
end))

# 22 "FStar.Const.fst"
let is_Const_bool = (fun _discr_ -> (match (_discr_) with
| Const_bool (_) -> begin
true
end
| _ -> begin
false
end))

# 23 "FStar.Const.fst"
let is_Const_int = (fun _discr_ -> (match (_discr_) with
| Const_int (_) -> begin
true
end
| _ -> begin
false
end))

# 24 "FStar.Const.fst"
let is_Const_char = (fun _discr_ -> (match (_discr_) with
| Const_char (_) -> begin
true
end
| _ -> begin
false
end))

# 25 "FStar.Const.fst"
let is_Const_float = (fun _discr_ -> (match (_discr_) with
| Const_float (_) -> begin
true
end
| _ -> begin
false
end))

# 26 "FStar.Const.fst"
let is_Const_bytearray = (fun _discr_ -> (match (_discr_) with
| Const_bytearray (_) -> begin
true
end
| _ -> begin
false
end))

# 27 "FStar.Const.fst"
let is_Const_string = (fun _discr_ -> (match (_discr_) with
| Const_string (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.Const.fst"
let is_Const_range = (fun _discr_ -> (match (_discr_) with
| Const_range (_) -> begin
true
end
| _ -> begin
false
end))

# 22 "FStar.Const.fst"
let ___Const_bool____0 = (fun projectee -> (match (projectee) with
| Const_bool (_26_29) -> begin
_26_29
end))

# 23 "FStar.Const.fst"
let ___Const_int____0 = (fun projectee -> (match (projectee) with
| Const_int (_26_32) -> begin
_26_32
end))

# 24 "FStar.Const.fst"
let ___Const_char____0 = (fun projectee -> (match (projectee) with
| Const_char (_26_35) -> begin
_26_35
end))

# 25 "FStar.Const.fst"
let ___Const_float____0 = (fun projectee -> (match (projectee) with
| Const_float (_26_38) -> begin
_26_38
end))

# 26 "FStar.Const.fst"
let ___Const_bytearray____0 = (fun projectee -> (match (projectee) with
| Const_bytearray (_26_41) -> begin
_26_41
end))

# 27 "FStar.Const.fst"
let ___Const_string____0 = (fun projectee -> (match (projectee) with
| Const_string (_26_44) -> begin
_26_44
end))

# 28 "FStar.Const.fst"
let ___Const_range____0 = (fun projectee -> (match (projectee) with
| Const_range (_26_47) -> begin
_26_47
end))




