
let oktype = Some (Microsoft_FStar_Absyn_Syntax.ktype)

let t_unit = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.unit_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_bool = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_uint8 = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.uint8_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int32 = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int32_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int64 = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int64_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_string = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.string_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_float = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.float_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_char = (Support.All.pipe_left (Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.char_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let typing_const = (fun ( r ) ( s ) -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
t_unit
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (_30_5) -> begin
t_bool
end
| Microsoft_FStar_Absyn_Syntax.Const_int (_30_8) -> begin
t_int
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (_30_11) -> begin
t_int32
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_30_14) -> begin
t_int64
end
| Microsoft_FStar_Absyn_Syntax.Const_string (_30_17) -> begin
t_string
end
| Microsoft_FStar_Absyn_Syntax.Const_float (_30_20) -> begin
t_float
end
| Microsoft_FStar_Absyn_Syntax.Const_char (_30_23) -> begin
t_char
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_30_26) -> begin
t_uint8
end
| _30_29 -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unsupported constant", r))))
end))

let rec recompute_kind = (fun ( t ) -> (let recompute = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_30_34) -> begin
(let _70_12166 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (recompute_kind _70_12166))
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
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _30_69))) -> begin
(recompute_kind t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _30_75, _30_77))) -> begin
(recompute_kind t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, body)) -> begin
(let _70_12168 = (let _70_12167 = (recompute_kind body)
in (binders, _70_12167))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _70_12168 t.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t1, args)) -> begin
(match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| _30_92 -> begin
(let k1 = (recompute_kind t1)
in (let _30_96 = (Microsoft_FStar_Absyn_Util.kind_formals k1)
in (match (_30_96) with
| (bs, k) -> begin
(let rec aux = (fun ( subst ) ( bs ) ( args ) -> (match ((bs, args)) with
| ([], []) -> begin
(Microsoft_FStar_Absyn_Util.subst_kind subst k)
end
| (_30_105, []) -> begin
(let _70_12175 = (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_12175 (Microsoft_FStar_Absyn_Util.subst_kind subst)))
end
| (b::bs, a::args) -> begin
(let subst = (let _70_12176 = (Microsoft_FStar_Absyn_Util.subst_formal b a)
in (_70_12176)::subst)
in (aux subst bs args))
end
| _30_117 -> begin
(let _70_12181 = (let _70_12180 = (Microsoft_FStar_Absyn_Print.kind_to_string k1)
in (let _70_12179 = (Microsoft_FStar_Absyn_Print.tag_of_typ t)
in (let _70_12178 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _70_12177 = (Support.All.pipe_right (Support.List.length args) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.format4 "Head kind is %s\nToo many arguments in type %s; result kind is %s\nwith %s remaining args\n" _70_12180 _70_12179 _70_12178 _70_12177)))))
in (Support.All.failwith _70_12181))
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
in (let _30_123 = (Support.ST.op_Colon_Equals t.Microsoft_FStar_Absyn_Syntax.tk (Some (k)))
in k))
end)))

let rec recompute_typ = (fun ( e ) -> (let recompute = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_30_129) -> begin
(let _70_12186 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (recompute_typ _70_12186))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
x.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _30_135)) -> begin
f.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (s) -> begin
(typing_const e.Microsoft_FStar_Absyn_Syntax.pos s)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let _70_12189 = (let _70_12188 = (let _70_12187 = (recompute_typ body)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _70_12187))
in (bs, _70_12188))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _70_12189 None e.Microsoft_FStar_Absyn_Syntax.pos))
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
| (_30_162, []) -> begin
(let _70_12196 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None e.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_12196 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
end
| (b::bs, a::args) -> begin
(let subst = (let _70_12197 = (Microsoft_FStar_Absyn_Util.subst_formal b a)
in (_70_12197)::subst)
in (aux subst bs args))
end
| _30_174 -> begin
(Support.All.failwith "Too many arguments")
end))
in (aux [] bs args))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_30_176) -> begin
(Support.All.failwith "Expect match nodes to be annotated already")
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((_30_179, t, _30_182)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((_30_186, e)) -> begin
(recompute_typ e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_30_191, t)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _30_197))) -> begin
(recompute_typ e)
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| Some (t) -> begin
t
end
| None -> begin
(let t = (recompute e)
in (let _30_205 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in t))
end)))




