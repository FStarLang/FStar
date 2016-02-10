
open Prims
# 1 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

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

# 4 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_effect = (fun _discr_ -> (match (_discr_) with
| Const_effect (_) -> begin
true
end
| _ -> begin
false
end))

# 5 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_unit = (fun _discr_ -> (match (_discr_) with
| Const_unit (_) -> begin
true
end
| _ -> begin
false
end))

# 6 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_uint8 = (fun _discr_ -> (match (_discr_) with
| Const_uint8 (_) -> begin
true
end
| _ -> begin
false
end))

# 7 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_bool = (fun _discr_ -> (match (_discr_) with
| Const_bool (_) -> begin
true
end
| _ -> begin
false
end))

# 8 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_int32 = (fun _discr_ -> (match (_discr_) with
| Const_int32 (_) -> begin
true
end
| _ -> begin
false
end))

# 9 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_int64 = (fun _discr_ -> (match (_discr_) with
| Const_int64 (_) -> begin
true
end
| _ -> begin
false
end))

# 10 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_int = (fun _discr_ -> (match (_discr_) with
| Const_int (_) -> begin
true
end
| _ -> begin
false
end))

# 11 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_char = (fun _discr_ -> (match (_discr_) with
| Const_char (_) -> begin
true
end
| _ -> begin
false
end))

# 12 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_float = (fun _discr_ -> (match (_discr_) with
| Const_float (_) -> begin
true
end
| _ -> begin
false
end))

# 13 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_bytearray = (fun _discr_ -> (match (_discr_) with
| Const_bytearray (_) -> begin
true
end
| _ -> begin
false
end))

# 14 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let is_Const_string = (fun _discr_ -> (match (_discr_) with
| Const_string (_) -> begin
true
end
| _ -> begin
false
end))

# 6 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_uint8____0 : sconst  ->  Prims.byte = (fun projectee -> (match (projectee) with
| Const_uint8 (_22_3) -> begin
_22_3
end))

# 7 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_bool____0 : sconst  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Const_bool (_22_6) -> begin
_22_6
end))

# 8 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_int32____0 : sconst  ->  Prims.int32 = (fun projectee -> (match (projectee) with
| Const_int32 (_22_9) -> begin
_22_9
end))

# 9 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_int64____0 : sconst  ->  Prims.int64 = (fun projectee -> (match (projectee) with
| Const_int64 (_22_12) -> begin
_22_12
end))

# 10 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_int____0 : sconst  ->  Prims.string = (fun projectee -> (match (projectee) with
| Const_int (_22_15) -> begin
_22_15
end))

# 11 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_char____0 : sconst  ->  Prims.char = (fun projectee -> (match (projectee) with
| Const_char (_22_18) -> begin
_22_18
end))

# 12 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_float____0 : sconst  ->  Prims.double = (fun projectee -> (match (projectee) with
| Const_float (_22_21) -> begin
_22_21
end))

# 13 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_bytearray____0 : sconst  ->  (Prims.byte Prims.array * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Const_bytearray (_22_24) -> begin
_22_24
end))

# 14 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\basic\\const.fs"

let ___Const_string____0 : sconst  ->  (Prims.byte Prims.array * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Const_string (_22_27) -> begin
_22_27
end))




