
let oktype = Some (Microsoft_FStar_Absyn_Syntax.ktype)

let t_unit = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.unit_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_bool = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_uint8 = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.uint8_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int32 = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int32_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_int64 = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.int64_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_string = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.string_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_float = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.float_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let t_char = ((Microsoft_FStar_Absyn_Syntax.syn Microsoft_FStar_Absyn_Syntax.dummyRange oktype) (Microsoft_FStar_Absyn_Syntax.mk_Typ_const (Microsoft_FStar_Absyn_Util.withsort Microsoft_FStar_Absyn_Const.char_lid Microsoft_FStar_Absyn_Syntax.ktype)))

let typing_const = (fun r s -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
t_unit
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (_) -> begin
t_bool
end
| Microsoft_FStar_Absyn_Syntax.Const_int (_) -> begin
t_int
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (_) -> begin
t_int32
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_) -> begin
t_int64
end
| Microsoft_FStar_Absyn_Syntax.Const_string (_) -> begin
t_string
end
| Microsoft_FStar_Absyn_Syntax.Const_float (_) -> begin
t_float
end
| Microsoft_FStar_Absyn_Syntax.Const_char (_) -> begin
t_char
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_) -> begin
t_uint8
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (("Unsupported constant", r))))
end))

let rec recompute_kind = (fun t -> (let recompute = (fun t -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_) -> begin
(recompute_kind (Microsoft_FStar_Absyn_Util.compress_typ t))
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
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _))) -> begin
(recompute_kind t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _))) -> begin
(recompute_kind t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, body)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (binders, (recompute_kind body)) t.Microsoft_FStar_Absyn_Syntax.pos)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t1, args)) -> begin
(match (t1.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exists_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.allTyp_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.exTyp_lid)) -> begin
Microsoft_FStar_Absyn_Syntax.ktype
end
| _ -> begin
(let k1 = (recompute_kind t1)
in (let _23_96 = (Microsoft_FStar_Absyn_Util.kind_formals k1)
in (match (_23_96) with
| (bs, k) -> begin
(let rec aux = (fun subst bs args -> (match ((bs, args)) with
| ([], []) -> begin
(Microsoft_FStar_Absyn_Util.subst_kind subst k)
end
| (_, []) -> begin
((Microsoft_FStar_Absyn_Util.subst_kind subst) (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) t.Microsoft_FStar_Absyn_Syntax.pos))
end
| (b::bs, a::args) -> begin
(let subst = ((Microsoft_FStar_Absyn_Util.subst_formal b a))::subst
in (aux subst bs args))
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format4 "Head kind is %s\nToo many arguments in type %s; result kind is %s\nwith %s remaining args\n" (Microsoft_FStar_Absyn_Print.kind_to_string k1) (Microsoft_FStar_Absyn_Print.tag_of_typ t) (Microsoft_FStar_Absyn_Print.kind_to_string k) (Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))))
end))
in (aux [] bs args))
end)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
Microsoft_FStar_Absyn_Syntax.kun
end))
in (match ((! (t.Microsoft_FStar_Absyn_Syntax.tk))) with
| Some (k) -> begin
k
end
| None -> begin
(let k = (recompute t)
in (let _23_123 = (Support.ST.op_Colon_Equals t.Microsoft_FStar_Absyn_Syntax.tk (Some (k)))
in k))
end)))

let rec recompute_typ = (fun e -> (let recompute = (fun e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(recompute_typ (Microsoft_FStar_Absyn_Util.compress_exp e))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
x.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((f, _)) -> begin
f.Microsoft_FStar_Absyn_Syntax.sort
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (s) -> begin
(typing_const e.Microsoft_FStar_Absyn_Syntax.pos s)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, (Microsoft_FStar_Absyn_Syntax.mk_Total (recompute_typ body))) None e.Microsoft_FStar_Absyn_Syntax.pos)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(let t1 = (recompute_typ head)
in (match ((Microsoft_FStar_Absyn_Util.function_formals t1)) with
| None -> begin
Microsoft_FStar_Absyn_Syntax.tun
end
| Some ((bs, c)) -> begin
(let rec aux = (fun subst bs args -> (match ((bs, args)) with
| ([], []) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ subst (Microsoft_FStar_Absyn_Util.comp_result c))
end
| (_, []) -> begin
((Microsoft_FStar_Absyn_Util.subst_typ subst) (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None e.Microsoft_FStar_Absyn_Syntax.pos))
end
| (b::bs, a::args) -> begin
(let subst = ((Microsoft_FStar_Absyn_Util.subst_formal b a))::subst
in (aux subst bs args))
end
| _ -> begin
(failwith "Too many arguments")
end))
in (aux [] bs args))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_) -> begin
(failwith "Expect match nodes to be annotated already")
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((_, t)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((_, e)) -> begin
(recompute_typ e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((_, t)) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(recompute_typ e)
end))
in (match ((! (e.Microsoft_FStar_Absyn_Syntax.tk))) with
| Some (t) -> begin
t
end
| None -> begin
(let t = (recompute e)
in (let _23_203 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in t))
end)))




