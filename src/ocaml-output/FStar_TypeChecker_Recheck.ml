
open Prims
# 35 "recheck.fs"
let tconst : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (let _189_5 = (let _189_4 = (let _189_3 = (FStar_Ident.set_lid_range l FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _189_3 None))
in FStar_Syntax_Syntax.Tm_fvar (_189_4))
in (FStar_Syntax_Syntax.mk _189_5 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))

# 36 "recheck.fs"
let t_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.unit_lid)

# 37 "recheck.fs"
let t_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.bool_lid)

# 38 "recheck.fs"
let t_uint8 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.uint8_lid)

# 39 "recheck.fs"
let t_int : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int_lid)

# 40 "recheck.fs"
let t_int32 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int32_lid)

# 41 "recheck.fs"
let t_int64 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int64_lid)

# 42 "recheck.fs"
let t_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.string_lid)

# 43 "recheck.fs"
let t_float : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.float_lid)

# 44 "recheck.fs"
let t_char : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.char_lid)

# 46 "recheck.fs"
let typing_const : FStar_Range.range  ->  FStar_Const.sconst  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun r s -> (match (s) with
| FStar_Const.Const_unit -> begin
t_unit
end
| FStar_Const.Const_bool (_87_6) -> begin
t_bool
end
| FStar_Const.Const_int (_87_9) -> begin
t_int
end
| FStar_Const.Const_int32 (_87_12) -> begin
t_int32
end
| FStar_Const.Const_int64 (_87_15) -> begin
t_int64
end
| FStar_Const.Const_string (_87_18) -> begin
t_string
end
| FStar_Const.Const_float (_87_21) -> begin
t_float
end
| FStar_Const.Const_char (_87_24) -> begin
t_char
end
| FStar_Const.Const_uint8 (_87_27) -> begin
t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| _87_31 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))

# 61 "recheck.fs"
let rec check : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 62 "recheck.fs"
let recompute = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_87_36) -> begin
(let _189_17 = (FStar_Syntax_Subst.compress t)
in (check _189_17))
end
| (FStar_Syntax_Syntax.Tm_bvar (a)) | (FStar_Syntax_Syntax.Tm_name (a)) -> begin
a.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _87_43) -> begin
fv.FStar_Syntax_Syntax.ty
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(check t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_constant (s) -> begin
(typing_const t.FStar_Syntax_Syntax.pos s)
end
| FStar_Syntax_Syntax.Tm_arrow (_87_55) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_refine (_87_58) -> begin
FStar_Syntax_Util.ktype0
end
| (FStar_Syntax_Syntax.Tm_ascribed (_, k, _)) | (FStar_Syntax_Syntax.Tm_uvar (_, k)) -> begin
k
end
| FStar_Syntax_Syntax.Tm_meta (t, _87_73) -> begin
(check t)
end
| FStar_Syntax_Syntax.Tm_let (_87_77, e) -> begin
(check e)
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, _87_84) -> begin
(let _189_19 = (let _189_18 = (check body)
in (FStar_Syntax_Syntax.mk_Total _189_18))
in (FStar_Syntax_Util.arrow binders _189_19))
end
| FStar_Syntax_Syntax.Tm_app (_87_88) -> begin
(let _189_21 = (let _189_20 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Refusing to recheck app node: %s" _189_20))
in (FStar_All.failwith _189_21))
end
| FStar_Syntax_Syntax.Tm_match (_87_91) -> begin
(FStar_All.failwith "Expect match nodes to be annotated already")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t
end))
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.tk)) with
| Some (k) -> begin
(FStar_Syntax_Syntax.mk k None t.FStar_Syntax_Syntax.pos)
end
| None -> begin
(
# 82 "recheck.fs"
let k = (recompute t)
in (
# 82 "recheck.fs"
let _87_98 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.tk (Some (k.FStar_Syntax_Syntax.n)))
in k))
end)))




