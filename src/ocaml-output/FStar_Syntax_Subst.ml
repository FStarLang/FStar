
open Prims
let rec force_uvar = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _34_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _34_17 -> begin
t
end)
end
| _34_19 -> begin
t
end))

let rec force_delayed_thunk = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(let t' = (let _87_8 = (c ())
in (force_delayed_thunk _87_8))
in (let _34_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _34_32 -> begin
t
end)
end
| Some (t') -> begin
(let t' = (force_delayed_thunk t')
in (let _34_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _34_39 -> begin
t
end))

let rec compress_univ = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _34_46 -> begin
u
end)
end
| _34_48 -> begin
u
end))

let subst_to_string = (fun s -> (let _87_15 = (FStar_All.pipe_right s (FStar_List.map (fun _34_53 -> (match (_34_53) with
| (b, _34_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _87_15 (FStar_String.concat ", "))))

let subst_bv = (fun a s -> (FStar_Util.find_map s (fun _34_1 -> (match (_34_1) with
| FStar_Syntax_Syntax.DB (i, t) when (i = a.FStar_Syntax_Syntax.index) -> begin
Some (t)
end
| _34_62 -> begin
None
end))))

let subst_nm = (fun a s -> (FStar_Util.find_map s (fun _34_2 -> (match (_34_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _87_26 = (FStar_Syntax_Syntax.bv_to_tm (let _34_70 = x
in {FStar_Syntax_Syntax.ppname = _34_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _34_70.FStar_Syntax_Syntax.sort}))
in Some (_87_26))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _34_77 -> begin
None
end))))

let subst_univ_bv = (fun x s -> (FStar_Util.find_map s (fun _34_3 -> (match (_34_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _34_86 -> begin
None
end))))

let subst_univ_nm = (fun x s -> (FStar_Util.find_map s (fun _34_4 -> (match (_34_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _34_95 -> begin
None
end))))

let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| s0::rest -> begin
(Obj.magic ((match ((f s0)) with
| None -> begin
(Obj.repr apply_until_some)
end
| Some (st) -> begin
(Obj.repr (Some ((rest, st))))
end)))
end))

let map_some_curry = (fun f x _34_5 -> (match (_34_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

let apply_until_some_then_map = (fun f s g t -> (let _87_64 = (apply_until_some f s)
in (FStar_All.pipe_right _87_64 (map_some_curry g t))))

let rec subst_univ = (fun s u -> (let u = (compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(apply_until_some_then_map (subst_univ_bv x) s subst_univ u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(apply_until_some_then_map (subst_univ_nm x) s subst_univ u)
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_unif (_)) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _87_69 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_87_69))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _87_70 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_87_70))
end)))

let rec subst' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _34_139 -> begin
(let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t', (FStar_List.append s' s)))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_34_158), _34_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _87_86 = (let _87_85 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_87_85))
in (FStar_Syntax_Syntax.mk _87_86 None t0.FStar_Syntax_Syntax.pos))
end
| _34_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _34_6 -> (match (_34_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _87_91 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_87_91))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _34_184 -> begin
(let _34_185 = t
in (let _87_98 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _87_97 = (FStar_List.map (fun _34_189 -> (match (_34_189) with
| (t, imp) -> begin
(let _87_95 = (subst' s t)
in (_87_95, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _87_96 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _34_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _87_98; FStar_Syntax_Syntax.effect_args = _87_97; FStar_Syntax_Syntax.flags = _87_96}))))
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _34_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _87_101 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _87_101))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _87_102 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _87_102))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _87_103 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _87_103))
end)
end))
and compose_subst = (fun s1 s2 -> (FStar_List.append s1 s2))

let shift = (fun n s -> (match (s) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
FStar_Syntax_Syntax.DB (((i + n), t))
end
| FStar_Syntax_Syntax.UN (i, t) -> begin
FStar_Syntax_Syntax.UN (((i + n), t))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
FStar_Syntax_Syntax.NM ((x, (i + n)))
end
| FStar_Syntax_Syntax.UD (x, i) -> begin
FStar_Syntax_Syntax.UD ((x, (i + n)))
end
| FStar_Syntax_Syntax.NT (_34_224) -> begin
s
end))

let shift_subst = (fun n s -> (FStar_List.map (shift n) s))

let shift_subst' = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

let subst_binder' = (fun s _34_233 -> (match (_34_233) with
| (x, imp) -> begin
(let _87_121 = (let _34_234 = x
in (let _87_120 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_120}))
in (_87_121, imp))
end))

let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _87_126 = (shift_subst' i s)
in (subst_binder' _87_126 b))
end))))

let subst_arg' = (fun s _34_243 -> (match (_34_243) with
| (t, imp) -> begin
(let _87_129 = (subst' s t)
in (_87_129, imp))
end))

let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

let subst_pat' = (fun s p -> (let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_34_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _34_261 = (aux n p)
in (match (_34_261) with
| (p, m) -> begin
(let ps = (FStar_List.map (fun p -> (let _87_142 = (aux n p)
in (Prims.fst _87_142))) ps)
in ((let _34_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.sort = _34_264.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _34_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _34_272 _34_275 -> (match ((_34_272, _34_275)) with
| ((pats, n), (p, imp)) -> begin
(let _34_278 = (aux n p)
in (match (_34_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_34_281) with
| (pats, n) -> begin
((let _34_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.sort = _34_282.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_282.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let s = (shift_subst' n s)
in (let x = (let _34_287 = x
in (let _87_145 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_145}))
in ((let _34_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.sort = _34_290.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let s = (shift_subst' n s)
in (let x = (let _34_295 = x
in (let _87_146 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_146}))
in ((let _34_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.sort = _34_298.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let s = (shift_subst' n s)
in (let x = (let _34_305 = x
in (let _87_147 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_147}))
in (let t0 = (subst' s t0)
in ((let _34_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.sort = _34_309.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _87_155 = (let _34_316 = l
in (let _87_154 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _34_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _87_154; FStar_Syntax_Syntax.cflags = _34_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _34_318 -> (match (()) with
| () -> begin
(let _87_153 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _87_153))
end))}))
in Some (_87_155))
end))

let push_subst = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_34_322) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _87_166 = (let _87_165 = (let _87_164 = (subst' s t0)
in (let _87_163 = (subst_args' s args)
in (_87_164, _87_163)))
in FStar_Syntax_Syntax.Tm_app (_87_165))
in (FStar_Syntax_Syntax.mk _87_166 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _87_170 = (let _87_169 = (let _87_168 = (subst' s t0)
in (let _87_167 = (subst' s t1)
in (_87_168, _87_167, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_87_169))
in (FStar_Syntax_Syntax.mk _87_170 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let n = (FStar_List.length bs)
in (let s' = (shift_subst' n s)
in (let _87_175 = (let _87_174 = (let _87_173 = (subst_binders' s bs)
in (let _87_172 = (subst' s' body)
in (let _87_171 = (push_subst_lcomp s' lopt)
in (_87_173, _87_172, _87_171))))
in FStar_Syntax_Syntax.Tm_abs (_87_174))
in (FStar_Syntax_Syntax.mk _87_175 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(let n = (FStar_List.length bs)
in (let _87_180 = (let _87_179 = (let _87_178 = (subst_binders' s bs)
in (let _87_177 = (let _87_176 = (shift_subst' n s)
in (subst_comp' _87_176 comp))
in (_87_178, _87_177)))
in FStar_Syntax_Syntax.Tm_arrow (_87_179))
in (FStar_Syntax_Syntax.mk _87_180 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let x = (let _34_373 = x
in (let _87_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_181}))
in (let phi = (let _87_182 = (shift_subst' 1 s)
in (subst' _87_182 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(let t0 = (subst' s t0)
in (let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _34_385 -> (match (_34_385) with
| (pat, wopt, branch) -> begin
(let _34_388 = (subst_pat' s pat)
in (match (_34_388) with
| (pat, n) -> begin
(let s = (shift_subst' n s)
in (let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _87_184 = (subst' s w)
in Some (_87_184))
end)
in (let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(let n = (FStar_List.length lbs)
in (let sn = (shift_subst' n s)
in (let body = (subst' sn body)
in (let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (let _34_408 = lb
in {FStar_Syntax_Syntax.lbname = _34_408.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _34_408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _34_408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd}))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _87_190 = (let _87_189 = (let _87_188 = (subst' s t0)
in (let _87_187 = (let _87_186 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_87_186))
in (_87_188, _87_187)))
in FStar_Syntax_Syntax.Tm_meta (_87_189))
in (FStar_Syntax_Syntax.mk _87_190 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _87_193 = (let _87_192 = (let _87_191 = (subst' s t)
in (_87_191, m))
in FStar_Syntax_Syntax.Tm_meta (_87_192))
in (FStar_Syntax_Syntax.mk _87_193 None t.FStar_Syntax_Syntax.pos))
end))

let rec compress = (fun t -> (let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(let t' = (let _87_196 = (push_subst s t)
in (compress _87_196))
in (let _34_430 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _34_433 -> begin
(force_uvar t)
end)))

let subst = (fun s t -> (subst' ((s)::[]) t))

let subst_comp = (fun s t -> (subst_comp' ((s)::[]) t))

let closing_subst = (fun bs -> (let _87_208 = (FStar_List.fold_right (fun _34_442 _34_445 -> (match ((_34_442, _34_445)) with
| ((x, _34_441), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _87_208 Prims.fst)))

let open_binders' = (fun bs -> (let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(let x' = (let _34_456 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _87_214 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_214}))
in (let o = (let _87_218 = (let _87_216 = (let _87_215 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _87_215))
in FStar_Syntax_Syntax.DB (_87_216))
in (let _87_217 = (shift_subst 1 o)
in (_87_218)::_87_217))
in (let _34_462 = (aux bs' o)
in (match (_34_462) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

let open_binders = (fun bs -> (let _87_221 = (open_binders' bs)
in (Prims.fst _87_221)))

let open_term' = (fun bs t -> (let _34_468 = (open_binders' bs)
in (match (_34_468) with
| (bs', opening) -> begin
(let _87_226 = (subst opening t)
in (bs', _87_226, opening))
end)))

let open_term = (fun bs t -> (let _34_475 = (open_term' bs t)
in (match (_34_475) with
| (b, t, _34_474) -> begin
(b, t)
end)))

let open_comp = (fun bs t -> (let _34_480 = (open_binders' bs)
in (match (_34_480) with
| (bs', opening) -> begin
(let _87_235 = (subst_comp opening t)
in (bs', _87_235))
end)))

let open_pat = (fun p -> (let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_34_488) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _34_496 = (aux sub p)
in (match (_34_496) with
| (p, sub) -> begin
(let ps = (FStar_List.map (fun p -> (let _87_243 = (aux sub p)
in (Prims.fst _87_243))) ps)
in ((let _34_499 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.sort = _34_499.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_499.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _34_516 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _34_507 _34_510 -> (match ((_34_507, _34_510)) with
| ((pats, sub), (p, imp)) -> begin
(let _34_513 = (aux sub p)
in (match (_34_513) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_34_516) with
| (pats, sub) -> begin
((let _34_517 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.sort = _34_517.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_517.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let x' = (let _34_521 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _87_246 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_246}))
in (let sub = (let _87_250 = (let _87_248 = (let _87_247 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _87_247))
in FStar_Syntax_Syntax.DB (_87_248))
in (let _87_249 = (shift_subst 1 sub)
in (_87_250)::_87_249))
in ((let _34_525 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.sort = _34_525.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_525.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let x' = (let _34_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _87_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_251}))
in (let sub = (let _87_255 = (let _87_253 = (let _87_252 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _87_252))
in FStar_Syntax_Syntax.DB (_87_253))
in (let _87_254 = (shift_subst 1 sub)
in (_87_255)::_87_254))
in ((let _34_533 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.sort = _34_533.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_533.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let x = (let _34_539 = x
in (let _87_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_539.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_539.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_256}))
in (let t0 = (subst sub t0)
in ((let _34_543 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.sort = _34_543.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_543.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

let open_branch = (fun _34_548 -> (match (_34_548) with
| (p, wopt, e) -> begin
(let _34_551 = (open_pat p)
in (match (_34_551) with
| (p, opening) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _87_259 = (subst opening w)
in Some (_87_259))
end)
in (let e = (subst opening e)
in (p, wopt, e)))
end))
end))

let close = (fun bs t -> (let _87_264 = (closing_subst bs)
in (subst _87_264 t)))

let close_comp = (fun bs c -> (let _87_269 = (closing_subst bs)
in (subst_comp _87_269 c)))

let close_binders = (fun bs -> (let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(let x = (let _34_571 = x
in (let _87_276 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_276}))
in (let s' = (let _87_277 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_87_277)
in (let _87_278 = (aux s' tl)
in ((x, imp))::_87_278)))
end))
in (aux [] bs)))

let close_lcomp = (fun bs lc -> (let s = (closing_subst bs)
in (let _34_578 = lc
in (let _87_285 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _34_578.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _87_285; FStar_Syntax_Syntax.cflags = _34_578.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _34_580 -> (match (()) with
| () -> begin
(let _87_284 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _87_284))
end))}))))

let close_pat = (fun p -> (let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_34_588) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _34_596 = (aux sub p)
in (match (_34_596) with
| (p, sub) -> begin
(let ps = (FStar_List.map (fun p -> (let _87_293 = (aux sub p)
in (Prims.fst _87_293))) ps)
in ((let _34_599 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.sort = _34_599.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_599.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _34_616 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _34_607 _34_610 -> (match ((_34_607, _34_610)) with
| ((pats, sub), (p, imp)) -> begin
(let _34_613 = (aux sub p)
in (match (_34_613) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_34_616) with
| (pats, sub) -> begin
((let _34_617 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.sort = _34_617.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_617.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let x = (let _34_621 = x
in (let _87_296 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_296}))
in (let sub = (let _87_297 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_87_297)
in ((let _34_625 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.sort = _34_625.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_625.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let x = (let _34_629 = x
in (let _87_298 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_629.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_629.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_298}))
in (let sub = (let _87_299 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_87_299)
in ((let _34_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.sort = _34_633.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_633.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let x = (let _34_639 = x
in (let _87_300 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _34_639.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _34_639.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _87_300}))
in (let t0 = (subst sub t0)
in ((let _34_643 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.sort = _34_643.FStar_Syntax_Syntax.sort; FStar_Syntax_Syntax.p = _34_643.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

let close_branch = (fun _34_648 -> (match (_34_648) with
| (p, wopt, e) -> begin
(let _34_651 = (close_pat p)
in (match (_34_651) with
| (p, closing) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _87_303 = (subst closing w)
in Some (_87_303))
end)
in (let e = (subst closing e)
in (p, wopt, e)))
end))
end))

let univ_var_opening = (fun us -> (let n = ((FStar_List.length us) - 1)
in (let _34_664 = (let _87_308 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _87_308 FStar_List.unzip))
in (match (_34_664) with
| (s, us') -> begin
(s, us')
end))))

let open_univ_vars = (fun us t -> (let _34_669 = (univ_var_opening us)
in (match (_34_669) with
| (s, us') -> begin
(let t = (subst s t)
in (us', t))
end)))

let open_univ_vars_comp = (fun us c -> (let _34_675 = (univ_var_opening us)
in (match (_34_675) with
| (s, us') -> begin
(let _87_317 = (subst_comp s c)
in (us', _87_317))
end)))

let close_univ_vars = (fun us t -> (let n = ((FStar_List.length us) - 1)
in (let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

let close_univ_vars_comp = (fun us c -> (let n = ((FStar_List.length us) - 1)
in (let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

let is_top_level = (fun _34_7 -> (match (_34_7) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_34_700); FStar_Syntax_Syntax.lbunivs = _34_698; FStar_Syntax_Syntax.lbtyp = _34_696; FStar_Syntax_Syntax.lbeff = _34_694; FStar_Syntax_Syntax.lbdef = _34_692}::_34_690 -> begin
true
end
| _34_705 -> begin
false
end))

let open_let_rec = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: open_let_rec")
end)

let close_let_rec = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: close_let_rec")
end)

let mk_subst_binders = (fun args -> (let _34_718 = (FStar_List.fold_right (fun a _34_714 -> (match (_34_714) with
| (s, i) -> begin
((FStar_Syntax_Syntax.DB ((i, (Prims.fst a))))::s, (i + 1))
end)) args ([], 0))
in (match (_34_718) with
| (s, _34_717) -> begin
s
end)))

let subst_binders = (fun bs args t -> (let _87_349 = (mk_subst_binders args)
in (subst _87_349 t)))

let subst_binders_comp = (fun bs args t -> (let _87_356 = (mk_subst_binders args)
in (subst_comp _87_356 t)))

let close_tscheme = (fun binders _34_728 -> (match (_34_728) with
| (us, t) -> begin
(let n = ((FStar_List.length binders) - 1)
in (let k = (FStar_List.length us)
in (let s = (FStar_List.mapi (fun i _34_735 -> (match (_34_735) with
| (x, _34_734) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (let t = (subst s t)
in (us, t)))))
end))

let close_univ_vars_tscheme = (fun us _34_741 -> (match (_34_741) with
| (us', t) -> begin
(let n = ((FStar_List.length us) - 1)
in (let k = (FStar_List.length us')
in (let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _87_369 = (subst s t)
in (us', _87_369)))))
end))

let opening_of_binders = (fun bs -> (let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _34_753 -> (match (_34_753) with
| (x, _34_752) -> begin
(let _87_375 = (let _87_374 = (FStar_Syntax_Syntax.bv_to_name x)
in ((n - i), _87_374))
in FStar_Syntax_Syntax.DB (_87_375))
end))))))




