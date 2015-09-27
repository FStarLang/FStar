
let print_pre = false

let print_post = false

let print_tag = false

let print_typ = false

let print_let_bindings = false

let print_ascribed = false

type project =
| LeftPro
| RightPro
| NoPro

let is_LeftPro = (fun _discr_ -> (match (_discr_) with
| LeftPro -> begin
true
end
| _ -> begin
false
end))

let is_RightPro = (fun _discr_ -> (match (_discr_) with
| RightPro -> begin
true
end
| _ -> begin
false
end))

let is_NoPro = (fun _discr_ -> (match (_discr_) with
| NoPro -> begin
true
end
| _ -> begin
false
end))

let inline_exp = (fun g e -> (match ((let _135_8 = (FStar_Absyn_Util.compress_exp e)
in _135_8.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (f, _66_5) -> begin
(let id = (FStar_Absyn_Print.exp_to_string e)
in (let nsstr = f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.nsstr
in (let mods = g.FStar_Tc_Env.modules
in (let modl = (let _135_10 = (FStar_Projection_Util.list_find (fun m -> (m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str = nsstr)) mods)
in (FStar_Option.get _135_10))
in (let decs = modl.FStar_Absyn_Syntax.declarations
in (let dec = (let _135_13 = (FStar_Projection_Util.list_find (fun d -> (match (d) with
| FStar_Absyn_Syntax.Sig_let (lbs, _66_17, _66_19, _66_21) -> begin
(FStar_Projection_Util.list_exists (fun lb -> ((FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname) = id)) (Prims.snd lbs))
end
| _66_26 -> begin
false
end)) decs)
in (FStar_Option.get _135_13))
in (let lbs = (match (dec) with
| FStar_Absyn_Syntax.Sig_let (lbs', _66_30, _66_32, _66_34) -> begin
lbs'
end
| _66_38 -> begin
(FStar_All.failwith "Impossible!")
end)
in (let lb = (let _135_15 = (FStar_Projection_Util.list_find (fun lb -> ((FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname) = id)) (Prims.snd lbs))
in (FStar_Option.get _135_15))
in lb.FStar_Absyn_Syntax.lbdef))))))))
end
| _66_43 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("iNLINE can only be applied to variables", e.FStar_Absyn_Syntax.pos))))
end))

let rec project_pat = (fun pa p -> (match ((p = NoPro)) with
| true -> begin
pa
end
| false -> begin
(match (pa.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (f, q, args) -> begin
(match (((f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "R") && (p <> NoPro))) with
| true -> begin
(match (((FStar_List.length args) <> 4)) with
| true -> begin
(FStar_All.failwith "List does not have 4 arguments")
end
| false -> begin
(let arg0 = (match ((p = LeftPro)) with
| true -> begin
(FStar_List.nth args 2)
end
| false -> begin
(FStar_List.nth args 3)
end)
in (Prims.fst arg0))
end)
end
| false -> begin
(let args' = (FStar_List.map (fun a -> (match ((Prims.snd a)) with
| true -> begin
a
end
| false -> begin
(let _135_21 = (project_pat (Prims.fst a) p)
in (_135_21, (Prims.snd a)))
end)) args)
in (let pa' = FStar_Absyn_Syntax.Pat_cons ((f, q, args'))
in (let _66_55 = pa
in {FStar_Absyn_Syntax.v = pa'; FStar_Absyn_Syntax.sort = _66_55.FStar_Absyn_Syntax.sort; FStar_Absyn_Syntax.p = _66_55.FStar_Absyn_Syntax.p})))
end)
end
| _66_58 -> begin
pa
end)
end))

let rec is_relational_typ = (fun ty -> (match ((let _135_24 = (FStar_Absyn_Util.compress_typ ty)
in _135_24.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(((f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "rel") || (f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "double")) || (f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText = "shared"))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
((is_relational_typ head) || false)
end
| FStar_Absyn_Syntax.Typ_lam (binders, body) -> begin
(is_relational_typ body)
end
| FStar_Absyn_Syntax.Typ_btvar (b) -> begin
false
end
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(match (comp.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(is_relational_typ t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(is_relational_typ ct.FStar_Absyn_Syntax.result_typ)
end)
end
| _66_81 -> begin
true
end))

let rec project_type = (fun m g ty p -> (match ((p = NoPro)) with
| true -> begin
ty
end
| false -> begin
(match ((let _135_37 = (FStar_Absyn_Util.compress_typ ty)
in _135_37.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match (f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText) with
| "rel" -> begin
(match (p) with
| LeftPro -> begin
(let _135_39 = (let _135_38 = (FStar_List.nth args 1)
in (Prims.fst _135_38))
in (FStar_Util.left _135_39))
end
| RightPro -> begin
(let _135_41 = (let _135_40 = (FStar_List.nth args 0)
in (Prims.fst _135_40))
in (FStar_Util.left _135_41))
end
| NoPro -> begin
(FStar_All.failwith "Impossible")
end)
end
| "double" -> begin
(let _135_43 = (let _135_42 = (FStar_List.hd args)
in (Prims.fst _135_42))
in (FStar_Util.left _135_43))
end
| _66_98 -> begin
(let args' = (FStar_List.map (fun t -> (match ((FStar_Absyn_Print.is_inr (Prims.fst t))) with
| true -> begin
(let _135_47 = (let _135_46 = (let _135_45 = (FStar_Util.right (Prims.fst t))
in (project_p m g _135_45 p))
in FStar_Util.Inr (_135_46))
in (_135_47, None))
end
| false -> begin
(let _135_50 = (let _135_49 = (let _135_48 = (FStar_Util.left (Prims.fst t))
in (project_type m g _135_48 p))
in FStar_Util.Inl (_135_49))
in (_135_50, None))
end)) args)
in (let _135_51 = (FStar_ST.read ty.FStar_Absyn_Syntax.tk)
in (FStar_Absyn_Syntax.mk_Typ_app (head, args') _135_51 ty.FStar_Absyn_Syntax.pos)))
end)
end
| _66_102 -> begin
ty
end)
end
| _66_104 -> begin
ty
end)
end))
and project_p = (fun m g e p -> (let _66_111 = (match (print_tag) with
| true -> begin
(let _66_109 = (let _135_56 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print_string _135_56))
in (FStar_Util.print_string "\n"))
end
| false -> begin
()
end)
in (let _66_115 = (match ((print_pre && (p <> NoPro))) with
| true -> begin
(let _66_113 = (let _135_57 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print_string _135_57))
in (FStar_Util.print_string "\n\n"))
end
| false -> begin
()
end)
in (let _66_121 = (match (print_pre) with
| true -> begin
(let t = (let _135_59 = (let _135_58 = (FStar_Absyn_Util.compress_exp e)
in _135_58.FStar_Absyn_Syntax.tk)
in (FStar_ST.read _135_59))
in (match ((FStar_Util.is_some t)) with
| true -> begin
(let t' = (FStar_Option.get t)
in (let _66_119 = (let _135_60 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print_string _135_60))
in (FStar_Util.print_string "\n")))
end
| false -> begin
()
end))
end
| false -> begin
()
end)
in (let e' = (match ((let _135_61 = (FStar_Absyn_Util.compress_exp e)
in _135_61.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let head = (FStar_Absyn_Util.compress_exp head)
in (let _66_165 = (match ((let _135_62 = (FStar_Absyn_Util.compress_exp head)
in _135_62.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_fvar (f, _66_130) -> begin
(match (f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText) with
| "R" -> begin
(match ((p <> NoPro)) with
| true -> begin
(match (((FStar_List.length args) <> 4)) with
| true -> begin
(FStar_All.failwith "List does not have 4 arguments")
end
| false -> begin
(let arg0 = (match ((p = LeftPro)) with
| true -> begin
(FStar_List.nth args 2)
end
| false -> begin
(FStar_List.nth args 3)
end)
in (let _135_63 = (FStar_Util.right (Prims.fst arg0))
in (_135_63, p, true, false)))
end)
end
| false -> begin
(e, p, false, true)
end)
end
| "compose2" -> begin
(match ((p <> NoPro)) with
| true -> begin
(match (((FStar_List.length args) <> 11)) with
| true -> begin
(FStar_All.failwith "List does not have 11 arguments")
end
| false -> begin
(let arg0 = (let _135_65 = (let _135_64 = (match ((p = LeftPro)) with
| true -> begin
(FStar_List.nth args 8)
end
| false -> begin
(FStar_List.nth args 9)
end)
in (Prims.fst _135_64))
in (FStar_Util.right _135_65))
in (let arg1 = (let _135_68 = (let _135_67 = (let _135_66 = (FStar_List.nth args 10)
in (Prims.fst _135_66))
in (FStar_Util.right _135_67))
in (project_p m g _135_68 p))
in (let _135_69 = (FStar_Absyn_Syntax.mk_Exp_app (arg0, ((FStar_Util.Inr (arg1), None))::[]) None e.FStar_Absyn_Syntax.pos)
in (_135_69, p, true, false))))
end)
end
| false -> begin
(e, p, false, true)
end)
end
| "iNLINE" -> begin
(match (((FStar_List.length args) <> 2)) with
| true -> begin
(FStar_All.failwith "List does not have 2 arguments")
end
| false -> begin
(let arg0 = (FStar_List.nth args 1)
in (let inline_e = (FStar_Util.right (Prims.fst arg0))
in (let _135_70 = (inline_exp g inline_e)
in (_135_70, p, true, true))))
end)
end
| "l_PROJECT" -> begin
(match ((p <> NoPro)) with
| true -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Illegal nested projection!", e.FStar_Absyn_Syntax.pos))))
end
| false -> begin
(match (((FStar_List.length args) <> 3)) with
| true -> begin
(FStar_All.failwith "List does not have 3 arguments")
end
| false -> begin
(let arg0 = (FStar_List.nth args 2)
in (let _135_71 = (FStar_Util.right (Prims.fst arg0))
in (_135_71, LeftPro, true, true)))
end)
end)
end
| "r_PROJECT" -> begin
(match ((p <> NoPro)) with
| true -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Illegal nested projection!", e.FStar_Absyn_Syntax.pos))))
end
| false -> begin
(match (((FStar_List.length args) <> 3)) with
| true -> begin
(FStar_All.failwith "List does not have 3 arguments")
end
| false -> begin
(let arg0 = (FStar_List.nth args 2)
in (let _135_72 = (FStar_Util.right (Prims.fst arg0))
in (_135_72, RightPro, true, true)))
end)
end)
end
| ("rel_map1") | ("rel_map2") | ("rel_map3") | ("twice") | ("compose2_self") | ("pair_rel") | ("cons_rel") | ("tl_rel") | ("fst_rel") | ("snd_rel") | ("sel_rel") -> begin
(match ((p <> NoPro)) with
| true -> begin
(let head' = (inline_exp g head)
in (let _135_73 = (FStar_Absyn_Syntax.mk_Exp_app (head', args) None e.FStar_Absyn_Syntax.pos)
in (_135_73, p, true, true)))
end
| false -> begin
(e, p, false, true)
end)
end
| _66_158 -> begin
(e, p, false, true)
end)
end
| _66_160 -> begin
(e, p, false, true)
end)
in (match (_66_165) with
| (e'', p', modf, cont) -> begin
(match ((not (cont))) with
| true -> begin
e''
end
| false -> begin
(match ((not (modf))) with
| true -> begin
(match ((let _135_74 = (FStar_Absyn_Util.compress_exp e'')
in _135_74.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let head' = (project_p m g head p')
in (let args' = (FStar_List.map (fun _66_173 -> (match (_66_173) with
| (a, q) -> begin
(match ((FStar_Absyn_Print.is_inr a)) with
| true -> begin
(let _135_78 = (let _135_77 = (let _135_76 = (FStar_Util.right a)
in (project_p m g _135_76 p'))
in FStar_Util.Inr (_135_77))
in (_135_78, q))
end
| false -> begin
(a, q)
end)
end)) args)
in (FStar_Absyn_Syntax.mk_Exp_app (head', args') None e.FStar_Absyn_Syntax.pos)))
end
| _66_176 -> begin
(FStar_All.failwith "IMPOSSIBLE!")
end)
end
| false -> begin
(project_p m g e'' p')
end)
end)
end)))
end
| FStar_Absyn_Syntax.Exp_abs (binders, e') -> begin
(let e'' = (project_p m g e' p)
in (let _135_79 = (FStar_ST.read e.FStar_Absyn_Syntax.tk)
in (FStar_Absyn_Syntax.mk_Exp_abs (binders, e'') _135_79 e.FStar_Absyn_Syntax.pos)))
end
| FStar_Absyn_Syntax.Exp_ascribed (e', t, eff) -> begin
(let _66_189 = (match (print_ascribed) with
| true -> begin
(let _66_187 = (let _135_80 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print_string _135_80))
in (FStar_Util.print_string "\n"))
end
| false -> begin
()
end)
in (let e'' = (project_p m g e' p)
in (let t' = (project_type m g t p)
in (let e = (let _135_81 = (FStar_ST.read e.FStar_Absyn_Syntax.tk)
in (FStar_Absyn_Syntax.mk_Exp_ascribed (e'', t', eff) _135_81 e.FStar_Absyn_Syntax.pos))
in (let _66_196 = (match (print_ascribed) with
| true -> begin
(let _66_194 = (let _135_82 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print_string _135_82))
in (FStar_Util.print_string "\n"))
end
| false -> begin
()
end)
in e)))))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _66_200) -> begin
(let t = f.FStar_Absyn_Syntax.sort
in (match (((is_relational_typ t) && (p <> NoPro))) with
| true -> begin
(let ident = {FStar_Absyn_Syntax.idText = (Prims.strcat f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText (match ((p = LeftPro)) with
| true -> begin
"_l"
end
| false -> begin
"_r"
end)); FStar_Absyn_Syntax.idRange = f.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idRange}
in (let lident = {FStar_Absyn_Syntax.ns = []; FStar_Absyn_Syntax.ident = ident; FStar_Absyn_Syntax.nsstr = m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str; FStar_Absyn_Syntax.str = (Prims.strcat (Prims.strcat m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str ".") ident.FStar_Absyn_Syntax.idText)}
in (let new_v = {FStar_Absyn_Syntax.v = lident; FStar_Absyn_Syntax.sort = FStar_Absyn_Syntax.mk_Typ_unknown; FStar_Absyn_Syntax.p = e.FStar_Absyn_Syntax.pos}
in (FStar_Absyn_Syntax.mk_Exp_fvar (new_v, None) None e.FStar_Absyn_Syntax.pos))))
end
| false -> begin
e
end))
end
| FStar_Absyn_Syntax.Exp_let (lbs, e') -> begin
(let _66_217 = (match (print_let_bindings) with
| true -> begin
(let _66_211 = (FStar_Util.print_string "\n")
in (let _66_213 = (FStar_Util.print_string "Found let expression: ")
in (let _66_215 = (let _135_85 = (let _135_84 = (let _135_83 = (FStar_List.hd (Prims.snd lbs))
in _135_83.FStar_Absyn_Syntax.lbname)
in (FStar_Absyn_Print.lbname_to_string _135_84))
in (FStar_Util.print_string _135_85))
in (FStar_Util.print_string "\n"))))
end
| false -> begin
()
end)
in (let lbs' = (let _135_87 = (FStar_List.map (fun lb -> (let lb_new = (match (((is_relational_typ lb.FStar_Absyn_Syntax.lbtyp) || (p = NoPro))) with
| true -> begin
(project_p m g lb.FStar_Absyn_Syntax.lbdef p)
end
| false -> begin
(FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None lb.FStar_Absyn_Syntax.lbdef.FStar_Absyn_Syntax.pos)
end)
in (let _66_221 = lb
in {FStar_Absyn_Syntax.lbname = _66_221.FStar_Absyn_Syntax.lbname; FStar_Absyn_Syntax.lbtyp = _66_221.FStar_Absyn_Syntax.lbtyp; FStar_Absyn_Syntax.lbeff = _66_221.FStar_Absyn_Syntax.lbeff; FStar_Absyn_Syntax.lbdef = lb_new}))) (Prims.snd lbs))
in ((Prims.fst lbs), _135_87))
in (let e'' = (project_p m g e' p)
in (let _135_88 = (FStar_ST.read e.FStar_Absyn_Syntax.tk)
in (FStar_Absyn_Syntax.mk_Exp_let (lbs', e'') _135_88 e.FStar_Absyn_Syntax.pos)))))
end
| FStar_Absyn_Syntax.Exp_match (e', pats) -> begin
(let e'' = (project_p m g e' p)
in (let pats' = (FStar_List.map (fun _66_233 -> (match (_66_233) with
| (pat, t, pe) -> begin
(let _135_91 = (project_pat pat p)
in (let _135_90 = (project_p m g pe p)
in (_135_91, t, _135_90)))
end)) pats)
in (let _135_92 = (FStar_ST.read e.FStar_Absyn_Syntax.tk)
in (FStar_Absyn_Syntax.mk_Exp_match (e'', pats') _135_92 e.FStar_Absyn_Syntax.pos))))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _66_237)) -> begin
(project_p m g e p)
end
| FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
e
end
| _66_244 -> begin
e
end)
in (let _66_248 = (match ((print_post && (p <> NoPro))) with
| true -> begin
(let _66_246 = (let _135_93 = (FStar_Absyn_Print.exp_to_string e')
in (FStar_Util.print_string _135_93))
in (FStar_Util.print_string "\n \n"))
end
| false -> begin
()
end)
in e'))))))

let project_exp = (fun m g e -> (let r = (project_p m g e NoPro)
in (let r = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::(FStar_Tc_Normalize.Unmeta)::[]) g r)
in r)))




