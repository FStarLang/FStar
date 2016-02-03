
open Prims
let tconst = (fun l -> (let _174_5 = (let _174_4 = (let _174_3 = (FStar_Ident.set_lid_range l FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _174_3 None))
in FStar_Syntax_Syntax.Tm_fvar (_174_4))
in (FStar_Syntax_Syntax.mk _174_5 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))

let t_unit = (tconst FStar_Syntax_Const.unit_lid)

let t_bool = (tconst FStar_Syntax_Const.bool_lid)

let t_uint8 = (tconst FStar_Syntax_Const.uint8_lid)

let t_int = (tconst FStar_Syntax_Const.int_lid)

let t_int32 = (tconst FStar_Syntax_Const.int32_lid)

let t_int64 = (tconst FStar_Syntax_Const.int64_lid)

let t_string = (tconst FStar_Syntax_Const.string_lid)

let t_float = (tconst FStar_Syntax_Const.float_lid)

let t_char = (tconst FStar_Syntax_Const.char_lid)

let typing_const = (fun r s -> (match (s) with
| FStar_Const.Const_unit -> begin
t_unit
end
| FStar_Const.Const_bool (_83_6) -> begin
t_bool
end
| FStar_Const.Const_int (_83_9) -> begin
t_int
end
| FStar_Const.Const_int32 (_83_12) -> begin
t_int32
end
| FStar_Const.Const_int64 (_83_15) -> begin
t_int64
end
| FStar_Const.Const_string (_83_18) -> begin
t_string
end
| FStar_Const.Const_float (_83_21) -> begin
t_float
end
| FStar_Const.Const_char (_83_24) -> begin
t_char
end
| FStar_Const.Const_uint8 (_83_27) -> begin
t_uint8
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| _83_31 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))

let rec check = (fun t -> (let recompute = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_83_36) -> begin
(let _174_17 = (FStar_Syntax_Subst.compress t)
in (check _174_17))
end
| (FStar_Syntax_Syntax.Tm_bvar (a)) | (FStar_Syntax_Syntax.Tm_name (a)) -> begin
a.FStar_Syntax_Syntax.sort
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _83_43) -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (_83_55) -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Syntax_Syntax.Tm_refine (_83_58) -> begin
FStar_Syntax_Util.ktype0
end
| (FStar_Syntax_Syntax.Tm_ascribed (_, k, _)) | (FStar_Syntax_Syntax.Tm_uvar (_, k)) -> begin
k
end
| FStar_Syntax_Syntax.Tm_meta (t, _83_73) -> begin
(check t)
end
| FStar_Syntax_Syntax.Tm_let (_83_77, e) -> begin
(check e)
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, _83_84) -> begin
(let _174_19 = (let _174_18 = (check body)
in (FStar_Syntax_Syntax.mk_Total _174_18))
in (FStar_Syntax_Util.arrow binders _174_19))
end
| FStar_Syntax_Syntax.Tm_app (_83_88) -> begin
(let _174_21 = (let _174_20 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Refusing to recheck app node: %s" _174_20))
in (FStar_All.failwith _174_21))
end
| FStar_Syntax_Syntax.Tm_match (_83_91) -> begin
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
(let k = (recompute t)
in (let _83_98 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.tk (Some (k.FStar_Syntax_Syntax.n)))
in k))
end)))




