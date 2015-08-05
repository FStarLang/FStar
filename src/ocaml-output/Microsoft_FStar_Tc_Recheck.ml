
let oktype = Some (Microsoft_FStar_Absyn_Syntax.ktype)

let t_unit = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.unit_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_bool = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_uint8 = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.uint8_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int32 = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int32_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int64 = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int64_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_string = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.string_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_float = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.float_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_char = (Support.Prims.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.char_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let typing_const = (fun ( r ) ( s ) -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
t_unit
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (_28_5) -> begin
t_bool
end
| Microsoft_FStar_Absyn_Syntax.Const_int (_28_8) -> begin
t_int
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (_28_11) -> begin
t_int32
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_28_14) -> begin
t_int64
end
| Microsoft_FStar_Absyn_Syntax.Const_string (_28_17) -> begin
t_string
end
| Microsoft_FStar_Absyn_Syntax.Const_float (_28_20) -> begin
t_float
end
| Microsoft_FStar_Absyn_Syntax.Const_char (_28_23) -> begin
t_char
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_28_26) -> begin
t_uint8
end
| _28_29 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unsupported constant", r))))
end))

let rec recompute_kind = (fun ( t ) -> (let recompute = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_28_34) -> begin
(let _68_12044 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (recompute_kind _68_12044))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
a.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
tc.Microsoft_FStar_Absyn_Syntax.sort
end
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((_, k))) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar ((_, k))) -> begin
k
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_))) -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _28_69))) -> begin
(recompute_kind t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _28_75, _28_77))) -> begin
(recompute_kind t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, body)) -> begin
(let _68_12046 = (let _68_12045 = (recompute_kind body)
in (binders, _68_12045))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_12046 t.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t1, args)) -> begin
(match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| _28_92 -> begin
(let k1 = (recompute_kind t1)
in (let _28_96 = (Microsoft_FStar_Absyn_Util.kind_formals k1)
in (match (_28_96) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) ( args ) -> (match ((bs, args)) with
| ([], []) -> begin
(Microsoft_FStar_Absyn_Util.subst_kind subst k)
end
| (_28_105, []) -> begin
(let _68_12053 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _68_12053 (Microsoft_FStar_Absyn_Util.subst_kind subst)))
end
| (b::bs, a::args) -> begin
(let subst = (let _68_12054 = (Microsoft_FStar_Absyn_Util.subst_formal b a)
in (_68_12054)::subst)
in (aux subst bs args))
end
| _28_117 -> begin
(let _68_12059 = (let _68_12058 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _68_12057 = (Microsoft_FStar_Absyn_Print.tag_of_typ t)
in (let _68_12056 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _68_12055 = (Support.Prims.pipe_right (Support.List.length args) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format4 "Head kind is %s\nToo many arguments in type %s; result kind is %s\nwith %s remaining args\n" _68_12058 _68_12057 _68_12056 _68_12055)))))
in (failwith (_68_12059)))
end))
in (aux [] bs args))
end)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
Microsoft_FStar_Absyn_Syntax.kun
end))
in (match ((Support.ST.read t.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some (k) -> begin
k
end
| None -> begin
(let k = (recompute t)
in (let _28_123 = (Support.ST.op_Colon_Equals t.Microsoft_FStar_Absyn_Syntax.tk (Some (k)))
in k))
end)))

let rec recompute_typ = (fun ( e ) -> (let recompute = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_28_129) -> begin
(let _68_12064 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (recompute_typ _68_12064))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
x.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _28_135)) -> begin
f.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (s) -> begin
(typing_const e.Microsoft_FStar_Absyn_Syntax.pos s)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _68_12067 = (let _68_12066 = (let _68_12065 = (recompute_typ body)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _68_12065))
in (bs, _68_12066))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_12067 None e.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let t1 = (recompute_typ head)
in (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.tun
end
| Some ((bs, c)) -> begin
(let rec aux = (fun ( subst ) ( bs ) ( args ) -> (match ((bs, args)) with
| ([], []) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
end
| (_28_162, []) -> begin
(let _68_12074 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _68_12074 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
end
| (b::bs, a::args) -> begin
(let subst = (let _68_12075 = (Microsoft_FStar_Absyn_Util.subst_formal b a)
in (_68_12075)::subst)
in (aux subst bs args))
end
| _28_174 -> begin
(failwith ("Too many arguments"))
end))
in (aux [] bs args))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_28_176) -> begin
(failwith ("Expect match nodes to be annotated already"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((_28_179, t, _28_182)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((_28_186, e)) -> begin
(recompute_typ e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_28_191, t)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _28_197))) -> begin
(recompute_typ e)
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some (t) -> begin
t
end
| None -> begin
(let t = (recompute e)
in (let _28_205 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in t))
end)))




