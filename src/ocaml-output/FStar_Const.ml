
open Prims
# 6 "FStar.Const.fst"
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

# 7 "FStar.Const.fst"
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

# 9 "FStar.Const.fst"
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

# 10 "FStar.Const.fst"
let is_Const_effect = (fun _discr_ -> (match (_discr_) with
| Const_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 11 "FStar.Const.fst"
let is_Const_unit = (fun _discr_ -> (match (_discr_) with
| Const_unit (_) -> begin
true
end
| _ -> begin
false
end))

# 12 "FStar.Const.fst"
let is_Const_bool = (fun _discr_ -> (match (_discr_) with
| Const_bool (_) -> begin
true
end
| _ -> begin
false
end))

# 13 "FStar.Const.fst"
let is_Const_int = (fun _discr_ -> (match (_discr_) with
| Const_int (_) -> begin
true
end
| _ -> begin
false
end))

# 14 "FStar.Const.fst"
let is_Const_char = (fun _discr_ -> (match (_discr_) with
| Const_char (_) -> begin
true
end
| _ -> begin
false
end))

# 15 "FStar.Const.fst"
let is_Const_float = (fun _discr_ -> (match (_discr_) with
| Const_float (_) -> begin
true
end
| _ -> begin
false
end))

# 16 "FStar.Const.fst"
let is_Const_bytearray = (fun _discr_ -> (match (_discr_) with
| Const_bytearray (_) -> begin
true
end
| _ -> begin
false
end))

# 17 "FStar.Const.fst"
let is_Const_string = (fun _discr_ -> (match (_discr_) with
| Const_string (_) -> begin
true
end
| _ -> begin
false
end))

# 18 "FStar.Const.fst"
let is_Const_range = (fun _discr_ -> (match (_discr_) with
| Const_range (_) -> begin
true
end
| _ -> begin
false
end))

# 19 "FStar.Const.fst"
let is_Const_reify = (fun _discr_ -> (match (_discr_) with
| Const_reify (_) -> begin
true
end
| _ -> begin
false
end))

# 20 "FStar.Const.fst"
let is_Const_reflect = (fun _discr_ -> (match (_discr_) with
| Const_reflect (_) -> begin
true
end
| _ -> begin
false
end))

# 12 "FStar.Const.fst"
let ___Const_bool____0 = (fun projectee -> (match (projectee) with
| Const_bool (_26_3) -> begin
_26_3
end))

# 13 "FStar.Const.fst"
let ___Const_int____0 = (fun projectee -> (match (projectee) with
| Const_int (_26_6) -> begin
_26_6
end))

# 14 "FStar.Const.fst"
let ___Const_char____0 = (fun projectee -> (match (projectee) with
| Const_char (_26_9) -> begin
_26_9
end))

# 15 "FStar.Const.fst"
let ___Const_float____0 = (fun projectee -> (match (projectee) with
| Const_float (_26_12) -> begin
_26_12
end))

# 16 "FStar.Const.fst"
let ___Const_bytearray____0 = (fun projectee -> (match (projectee) with
| Const_bytearray (_26_15) -> begin
_26_15
end))

# 17 "FStar.Const.fst"
let ___Const_string____0 = (fun projectee -> (match (projectee) with
| Const_string (_26_18) -> begin
_26_18
end))

# 18 "FStar.Const.fst"
let ___Const_range____0 = (fun projectee -> (match (projectee) with
| Const_range (_26_21) -> begin
_26_21
end))

# 20 "FStar.Const.fst"
let ___Const_reflect____0 = (fun projectee -> (match (projectee) with
| Const_reflect (_26_24) -> begin
_26_24
end))




