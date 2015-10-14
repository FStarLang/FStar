
open Prims
let oktype = Some (FStar_Absyn_Syntax.ktype)

let t_unit = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.unit_lid FStar_Absyn_Syntax.ktype)))

let t_bool = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)))

let t_uint8 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.uint8_lid FStar_Absyn_Syntax.ktype)))

let t_int = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.int_lid FStar_Absyn_Syntax.ktype)))

let t_int32 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.int32_lid FStar_Absyn_Syntax.ktype)))

let t_int64 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.int64_lid FStar_Absyn_Syntax.ktype)))

let t_string = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.string_lid FStar_Absyn_Syntax.ktype)))

let t_float = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.float_lid FStar_Absyn_Syntax.ktype)))

let t_char = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn FStar_Absyn_Syntax.dummyRange oktype) (FStar_Absyn_Syntax.mk_Typ_const (FStar_Absyn_Util.withsort FStar_Absyn_Const.char_lid FStar_Absyn_Syntax.ktype)))

let typing_const = (fun r s -> (match (s) with
| FStar_Absyn_Syntax.Const_unit -> begin
t_unit
end
| FStar_Absyn_Syntax.Const_bool (_31_5) -> begin
t_bool
end
| FStar_Absyn_Syntax.Const_int (_31_8) -> begin
t_int
end
| FStar_Absyn_Syntax.Const_int32 (_31_11) -> begin
t_int32
end
| FStar_Absyn_Syntax.Const_int64 (_31_14) -> begin
t_int64
end
| FStar_Absyn_Syntax.Const_string (_31_17) -> begin
t_string
end
| FStar_Absyn_Syntax.Const_float (_31_20) -> begin
t_float
end
| FStar_Absyn_Syntax.Const_char (_31_23) -> begin
t_char
end
| FStar_Absyn_Syntax.Const_uint8 (_31_26) -> begin
t_uint8
end
| _31_29 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unsupported constant", r))))
end))

let rec recompute_kind = (fun t -> (let recompute = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_31_34) -> begin
(let _96_30 = (FStar_Absyn_Util.compress_typ t)
in (recompute_kind _96_30))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
a.FStar_Absyn_Syntax.sort
end
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
tc.FStar_Absyn_Syntax.sort
end
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) -> begin
FStar_Absyn_Syntax.ktype
end
| (FStar_Absyn_Syntax.Typ_ascribed (_, k)) | (FStar_Absyn_Syntax.Typ_uvar (_, k)) -> begin
k
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (_))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (_))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (_))) -> begin
FStar_Absyn_Syntax.ktype
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _31_69)) -> begin
(recompute_kind t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _31_75, _31_77)) -> begin
(recompute_kind t)
end
| FStar_Absyn_Syntax.Typ_lam (binders, body) -> begin
(let _96_32 = (let _96_31 = (recompute_kind body)
in (binders, _96_31))
in (FStar_Absyn_Syntax.mk_Kind_arrow _96_32 t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_app (t1, args) -> begin
(match (t1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((((FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.forall_lid) || (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.exists_lid)) || (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid)) || (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
FStar_Absyn_Syntax.ktype
end
| _31_92 -> begin
(let k1 = (recompute_kind t1)
in (let _31_96 = (FStar_Absyn_Util.kind_formals k1)
in (match (_31_96) with
| (bs, k) -> begin
(let rec aux = (fun subst bs args -> (match ((bs, args)) with
| ([], []) -> begin
(FStar_Absyn_Util.subst_kind subst k)
end
| (_31_105, []) -> begin
(let _96_39 = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) t.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _96_39 (FStar_Absyn_Util.subst_kind subst)))
end
| (b::bs, a::args) -> begin
(let subst = (let _96_40 = (FStar_Absyn_Util.subst_formal b a)
in (_96_40)::subst)
in (aux subst bs args))
end
| _31_117 -> begin
(let _96_45 = (let _96_44 = (FStar_Absyn_Print.kind_to_string k1)
in (let _96_43 = (FStar_Absyn_Print.tag_of_typ t)
in (let _96_42 = (FStar_Absyn_Print.kind_to_string k)
in (let _96_41 = (FStar_All.pipe_right (FStar_List.length args) FStar_Util.string_of_int)
in (FStar_Util.format4 "Head kind is %s\nToo many arguments in type %s; result kind is %s\nwith %s remaining args\n" _96_44 _96_43 _96_42 _96_41)))))
in (FStar_All.failwith _96_45))
end))
in (aux [] bs args))
end)))
end)
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
FStar_Absyn_Syntax.kun
end))
in (match ((FStar_ST.read t.FStar_Absyn_Syntax.tk)) with
| Some (k) -> begin
k
end
| None -> begin
(let k = (recompute t)
in (let _31_123 = (FStar_ST.op_Colon_Equals t.FStar_Absyn_Syntax.tk (Some (k)))
in k))
end)))

let rec recompute_typ = (fun e -> (let recompute = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_31_129) -> begin
(let _96_50 = (FStar_Absyn_Util.compress_exp e)
in (recompute_typ _96_50))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
x.FStar_Absyn_Syntax.sort
end
| FStar_Absyn_Syntax.Exp_fvar (f, _31_135) -> begin
f.FStar_Absyn_Syntax.sort
end
| FStar_Absyn_Syntax.Exp_constant (s) -> begin
(typing_const e.FStar_Absyn_Syntax.pos s)
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let _96_53 = (let _96_52 = (let _96_51 = (recompute_typ body)
in (FStar_Absyn_Syntax.mk_Total _96_51))
in (bs, _96_52))
in (FStar_Absyn_Syntax.mk_Typ_fun _96_53 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let t1 = (recompute_typ head)
in (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
FStar_Absyn_Syntax.tun
end
| Some (bs, c) -> begin
(let rec aux = (fun subst bs args -> (match ((bs, args)) with
| ([], []) -> begin
(FStar_Absyn_Util.subst_typ subst (FStar_Absyn_Util.comp_result c))
end
| (_31_162, []) -> begin
(let _96_60 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None e.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _96_60 (FStar_Absyn_Util.subst_typ subst)))
end
| (b::bs, a::args) -> begin
(let subst = (let _96_61 = (FStar_Absyn_Util.subst_formal b a)
in (_96_61)::subst)
in (aux subst bs args))
end
| _31_174 -> begin
(FStar_All.failwith "Too many arguments")
end))
in (aux [] bs args))
end))
end
| FStar_Absyn_Syntax.Exp_match (_31_176) -> begin
(FStar_All.failwith "Expect match nodes to be annotated already")
end
| FStar_Absyn_Syntax.Exp_ascribed (_31_179, t, _31_182) -> begin
t
end
| FStar_Absyn_Syntax.Exp_let (_31_186, e) -> begin
(recompute_typ e)
end
| FStar_Absyn_Syntax.Exp_uvar (_31_191, t) -> begin
t
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_197)) -> begin
(recompute_typ e)
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| Some (t) -> begin
t
end
| None -> begin
(let t = (recompute e)
in (let _31_205 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in t))
end)))
