
open Prims
# 46 "FStar.TypeChecker.Recheck.fst"
let tconst : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (let _149_5 = (let _149_4 = (let _149_3 = (FStar_Ident.set_lid_range l FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _149_3 None))
in FStar_Syntax_Syntax.Tm_fvar (_149_4))
in (FStar_Syntax_Syntax.mk _149_5 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))

# 47 "FStar.TypeChecker.Recheck.fst"
let t_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.unit_lid)

# 48 "FStar.TypeChecker.Recheck.fst"
let t_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.bool_lid)

# 49 "FStar.TypeChecker.Recheck.fst"
let t_uint8 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.uint8_lid)

# 50 "FStar.TypeChecker.Recheck.fst"
let t_int : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int_lid)

# 51 "FStar.TypeChecker.Recheck.fst"
let t_int32 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int32_lid)

# 52 "FStar.TypeChecker.Recheck.fst"
let t_int64 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int64_lid)

# 53 "FStar.TypeChecker.Recheck.fst"
let t_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.string_lid)

# 54 "FStar.TypeChecker.Recheck.fst"
let t_float : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.float_lid)

# 55 "FStar.TypeChecker.Recheck.fst"
let t_char : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.char_lid)

# 57 "FStar.TypeChecker.Recheck.fst"
let typing_const : FStar_Range.range  ->  FStar_Const.sconst  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun r s -> (match (s) with
| FStar_Const.Const_unit -> begin
t_unit
end
| FStar_Const.Const_bool (_67_6) -> begin
t_bool
end
| FStar_Const.Const_int (_67_9) -> begin
t_int
end
| FStar_Const.Const_int32 (_67_12) -> begin
t_int32
end
| FStar_Const.Const_int64 (_67_15) -> begin
t_int64
end
| FStar_Const.Const_string (_67_18) -> begin
t_string
end
| FStar_Const.Const_float (_67_21) -> begin
t_float
end
| FStar_Const.Const_char (_67_24) -> begin
t_char
end
| FStar_Const.Const_uint8 (_67_27) -> begin
t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| _67_31 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))

# 72 "FStar.TypeChecker.Recheck.fst"
let rec check : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ = (fun t -> (
# 73 "FStar.TypeChecker.Recheck.fst"
let recompute = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_67_36) -> begin
(let _149_17 = (FStar_Syntax_Subst.compress t)
in (check _149_17))
end
| (FStar_Syntax_Syntax.Tm_bvar (a)) | (FStar_Syntax_Syntax.Tm_name (a)) -> begin
a.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _67_43) -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (_67_55) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_refine (_67_58) -> begin
FStar_Syntax_Util.ktype0
end
| (FStar_Syntax_Syntax.Tm_ascribed (_, k, _)) | (FStar_Syntax_Syntax.Tm_uvar (_, k)) -> begin
k
end
| FStar_Syntax_Syntax.Tm_meta (t, _67_73) -> begin
(check t)
end
| FStar_Syntax_Syntax.Tm_let (_67_77, e) -> begin
(check e)
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, _67_84) -> begin
(let _149_19 = (let _149_18 = (check body)
in (FStar_Syntax_Syntax.mk_Total _149_18))
in (FStar_Syntax_Util.arrow binders _149_19))
end
| FStar_Syntax_Syntax.Tm_app (_67_88) -> begin
(let _149_21 = (let _149_20 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Refusing to recheck app node: %s" _149_20))
in (FStar_All.failwith _149_21))
end
| FStar_Syntax_Syntax.Tm_match (_67_91) -> begin
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
# 93 "FStar.TypeChecker.Recheck.fst"
let k = (recompute t)
in (
# 93 "FStar.TypeChecker.Recheck.fst"
let _67_98 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.tk (Some (k.FStar_Syntax_Syntax.n)))
in k))
end)))




