
open Prims
let rec force_uvar = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _36_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _36_17 -> begin
t
end)
end
| _36_19 -> begin
t
end))

let rec force_delayed_thunk = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(let t' = (let _127_8 = (c ())
in (force_delayed_thunk _127_8))
in (let _36_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _36_32 -> begin
t
end)
end
| Some (t') -> begin
(let t' = (force_delayed_thunk t')
in (let _36_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _36_39 -> begin
t
end))

let rec compress_univ = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _36_46 -> begin
u
end)
end
| _36_48 -> begin
u
end))

let subst_to_string = (fun s -> (let _127_15 = (FStar_All.pipe_right s (FStar_List.map (fun _36_53 -> (match (_36_53) with
| (b, _36_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _127_15 (FStar_String.concat ", "))))

let subst_bv = (fun a s -> (FStar_Util.find_map s (fun _36_1 -> (match (_36_1) with
| FStar_Syntax_Syntax.DB (i, t) when (i = a.FStar_Syntax_Syntax.index) -> begin
Some (t)
end
| _36_62 -> begin
None
end))))

let subst_nm = (fun a s -> (FStar_Util.find_map s (fun _36_2 -> (match (_36_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _127_26 = (FStar_Syntax_Syntax.bv_to_tm (let _36_70 = x
in {FStar_Syntax_Syntax.ppname = _36_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _36_70.FStar_Syntax_Syntax.sort}))
in Some (_127_26))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _36_77 -> begin
None
end))))

let subst_univ_bv = (fun x s -> (FStar_Util.find_map s (fun _36_3 -> (match (_36_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _36_86 -> begin
None
end))))

let subst_univ_nm = (fun x s -> (FStar_Util.find_map s (fun _36_4 -> (match (_36_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _36_95 -> begin
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

let map_some_curry = (fun f x _36_5 -> (match (_36_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

let apply_until_some_then_map = (fun f s g t -> (let _127_64 = (apply_until_some f s)
in (FStar_All.pipe_right _127_64 (map_some_curry g t))))

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
(let _127_69 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_127_69))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _127_70 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_127_70))
end)))

let rec subst' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _36_139 -> begin
(let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t', (FStar_List.append s' s)))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_36_158), _36_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _127_86 = (let _127_85 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_127_85))
in (FStar_Syntax_Syntax.mk _127_86 None t0.FStar_Syntax_Syntax.pos))
end
| _36_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _36_6 -> (match (_36_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _127_91 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_127_91))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _36_184 -> begin
(let _36_185 = t
in (let _127_98 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _127_97 = (FStar_List.map (fun _36_189 -> (match (_36_189) with
| (t, imp) -> begin
(let _127_95 = (subst' s t)
in (_127_95, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _127_96 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _36_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _127_98; FStar_Syntax_Syntax.effect_args = _127_97; FStar_Syntax_Syntax.flags = _127_96}))))
end))
and subst_comp' = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _36_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _127_101 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _127_101))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _127_102 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _127_102))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _127_103 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _127_103))
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
| FStar_Syntax_Syntax.NT (_36_224) -> begin
s
end))

let shift_subst = (fun n s -> (FStar_List.map (shift n) s))

let shift_subst' = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

let subst_binder' = (fun s _36_233 -> (match (_36_233) with
| (x, imp) -> begin
(let _127_121 = (let _36_234 = x
in (let _127_120 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_120}))
in (_127_121, imp))
end))

let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _127_126 = (shift_subst' i s)
in (subst_binder' _127_126 b))
end))))

let subst_arg' = (fun s _36_243 -> (match (_36_243) with
| (t, imp) -> begin
(let _127_129 = (subst' s t)
in (_127_129, imp))
end))

let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

let subst_pat' = (fun s p -> (let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_36_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _36_261 = (aux n p)
in (match (_36_261) with
| (p, m) -> begin
(let ps = (FStar_List.map (fun p -> (let _127_142 = (aux n p)
in (Prims.fst _127_142))) ps)
in ((let _36_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _36_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _36_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _36_272 _36_275 -> (match ((_36_272, _36_275)) with
| ((pats, n), (p, imp)) -> begin
(let _36_278 = (aux n p)
in (match (_36_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_36_281) with
| (pats, n) -> begin
((let _36_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _36_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_282.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let s = (shift_subst' n s)
in (let x = (let _36_287 = x
in (let _127_145 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_145}))
in ((let _36_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _36_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let s = (shift_subst' n s)
in (let x = (let _36_295 = x
in (let _127_146 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_146}))
in ((let _36_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _36_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let s = (shift_subst' n s)
in (let x = (let _36_305 = x
in (let _127_147 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_147}))
in (let t0 = (subst' s t0)
in ((let _36_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _36_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _127_155 = (let _36_316 = l
in (let _127_154 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _36_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _127_154; FStar_Syntax_Syntax.cflags = _36_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _36_318 -> (match (()) with
| () -> begin
(let _127_153 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _127_153))
end))}))
in Some (_127_155))
end))

let push_subst = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_322) -> begin
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
(let _127_166 = (let _127_165 = (let _127_164 = (subst' s t0)
in (let _127_163 = (subst_args' s args)
in (_127_164, _127_163)))
in FStar_Syntax_Syntax.Tm_app (_127_165))
in (FStar_Syntax_Syntax.mk _127_166 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _127_170 = (let _127_169 = (let _127_168 = (subst' s t0)
in (let _127_167 = (subst' s t1)
in (_127_168, _127_167, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_127_169))
in (FStar_Syntax_Syntax.mk _127_170 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let n = (FStar_List.length bs)
in (let s' = (shift_subst' n s)
in (let _127_175 = (let _127_174 = (let _127_173 = (subst_binders' s bs)
in (let _127_172 = (subst' s' body)
in (let _127_171 = (push_subst_lcomp s' lopt)
in (_127_173, _127_172, _127_171))))
in FStar_Syntax_Syntax.Tm_abs (_127_174))
in (FStar_Syntax_Syntax.mk _127_175 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(let n = (FStar_List.length bs)
in (let _127_180 = (let _127_179 = (let _127_178 = (subst_binders' s bs)
in (let _127_177 = (let _127_176 = (shift_subst' n s)
in (subst_comp' _127_176 comp))
in (_127_178, _127_177)))
in FStar_Syntax_Syntax.Tm_arrow (_127_179))
in (FStar_Syntax_Syntax.mk _127_180 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let x = (let _36_373 = x
in (let _127_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_181}))
in (let phi = (let _127_182 = (shift_subst' 1 s)
in (subst' _127_182 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(let t0 = (subst' s t0)
in (let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _36_385 -> (match (_36_385) with
| (pat, wopt, branch) -> begin
(let _36_388 = (subst_pat' s pat)
in (match (_36_388) with
| (pat, n) -> begin
(let s = (shift_subst' n s)
in (let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _127_184 = (subst' s w)
in Some (_127_184))
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
in (let _36_408 = lb
in {FStar_Syntax_Syntax.lbname = _36_408.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _36_408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _36_408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd}))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _127_190 = (let _127_189 = (let _127_188 = (subst' s t0)
in (let _127_187 = (let _127_186 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_127_186))
in (_127_188, _127_187)))
in FStar_Syntax_Syntax.Tm_meta (_127_189))
in (FStar_Syntax_Syntax.mk _127_190 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _127_193 = (let _127_192 = (let _127_191 = (subst' s t)
in (_127_191, m))
in FStar_Syntax_Syntax.Tm_meta (_127_192))
in (FStar_Syntax_Syntax.mk _127_193 None t.FStar_Syntax_Syntax.pos))
end))

let rec compress = (fun t -> (let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(let t' = (let _127_196 = (push_subst s t)
in (compress _127_196))
in (let _36_430 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _36_433 -> begin
(force_uvar t)
end)))

let subst = (fun s t -> (subst' ((s)::[]) t))

let subst_comp = (fun s t -> (subst_comp' ((s)::[]) t))

let closing_subst = (fun bs -> (let _127_208 = (FStar_List.fold_right (fun _36_442 _36_445 -> (match ((_36_442, _36_445)) with
| ((x, _36_441), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _127_208 Prims.fst)))

let open_binders' = (fun bs -> (let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(let x' = (let _36_456 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _127_214 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_214}))
in (let o = (let _127_218 = (let _127_216 = (let _127_215 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _127_215))
in FStar_Syntax_Syntax.DB (_127_216))
in (let _127_217 = (shift_subst 1 o)
in (_127_218)::_127_217))
in (let _36_462 = (aux bs' o)
in (match (_36_462) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

let open_binders = (fun bs -> (let _127_221 = (open_binders' bs)
in (Prims.fst _127_221)))

let open_term' = (fun bs t -> (let _36_468 = (open_binders' bs)
in (match (_36_468) with
| (bs', opening) -> begin
(let _127_226 = (subst opening t)
in (bs', _127_226, opening))
end)))

let open_term = (fun bs t -> (let _36_475 = (open_term' bs t)
in (match (_36_475) with
| (b, t, _36_474) -> begin
(b, t)
end)))

let open_comp = (fun bs t -> (let _36_480 = (open_binders' bs)
in (match (_36_480) with
| (bs', opening) -> begin
(let _127_235 = (subst_comp opening t)
in (bs', _127_235))
end)))

let open_pat = (fun p -> (let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_36_488) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _36_496 = (aux sub p)
in (match (_36_496) with
| (p, sub) -> begin
(let ps = (FStar_List.map (fun p -> (let _127_243 = (aux sub p)
in (Prims.fst _127_243))) ps)
in ((let _36_499 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _36_499.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_499.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _36_516 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _36_507 _36_510 -> (match ((_36_507, _36_510)) with
| ((pats, sub), (p, imp)) -> begin
(let _36_513 = (aux sub p)
in (match (_36_513) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_36_516) with
| (pats, sub) -> begin
((let _36_517 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _36_517.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_517.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let x' = (let _36_521 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _127_246 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_246}))
in (let sub = (let _127_250 = (let _127_248 = (let _127_247 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _127_247))
in FStar_Syntax_Syntax.DB (_127_248))
in (let _127_249 = (shift_subst 1 sub)
in (_127_250)::_127_249))
in ((let _36_525 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _36_525.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_525.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let x' = (let _36_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _127_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_251}))
in (let sub = (let _127_255 = (let _127_253 = (let _127_252 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _127_252))
in FStar_Syntax_Syntax.DB (_127_253))
in (let _127_254 = (shift_subst 1 sub)
in (_127_255)::_127_254))
in ((let _36_533 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _36_533.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_533.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let x = (let _36_539 = x
in (let _127_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_539.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_539.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_256}))
in (let t0 = (subst sub t0)
in ((let _36_543 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _36_543.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_543.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

let open_branch = (fun _36_548 -> (match (_36_548) with
| (p, wopt, e) -> begin
(let _36_551 = (open_pat p)
in (match (_36_551) with
| (p, opening) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _127_259 = (subst opening w)
in Some (_127_259))
end)
in (let e = (subst opening e)
in (p, wopt, e)))
end))
end))

let close = (fun bs t -> (let _127_264 = (closing_subst bs)
in (subst _127_264 t)))

let close_comp = (fun bs c -> (let _127_269 = (closing_subst bs)
in (subst_comp _127_269 c)))

let close_binders = (fun bs -> (let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(let x = (let _36_571 = x
in (let _127_276 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_276}))
in (let s' = (let _127_277 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_127_277)
in (let _127_278 = (aux s' tl)
in ((x, imp))::_127_278)))
end))
in (aux [] bs)))

let close_lcomp = (fun bs lc -> (let s = (closing_subst bs)
in (let _36_578 = lc
in (let _127_285 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _36_578.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _127_285; FStar_Syntax_Syntax.cflags = _36_578.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _36_580 -> (match (()) with
| () -> begin
(let _127_284 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _127_284))
end))}))))

let close_pat = (fun p -> (let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_36_588) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(let _36_596 = (aux sub p)
in (match (_36_596) with
| (p, sub) -> begin
(let ps = (FStar_List.map (fun p -> (let _127_293 = (aux sub p)
in (Prims.fst _127_293))) ps)
in ((let _36_599 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _36_599.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_599.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _36_616 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _36_607 _36_610 -> (match ((_36_607, _36_610)) with
| ((pats, sub), (p, imp)) -> begin
(let _36_613 = (aux sub p)
in (match (_36_613) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_36_616) with
| (pats, sub) -> begin
((let _36_617 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _36_617.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_617.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let x = (let _36_621 = x
in (let _127_296 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_296}))
in (let sub = (let _127_297 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_127_297)
in ((let _36_625 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _36_625.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_625.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let x = (let _36_629 = x
in (let _127_298 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_629.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_629.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_298}))
in (let sub = (let _127_299 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_127_299)
in ((let _36_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _36_633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_633.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(let x = (let _36_639 = x
in (let _127_300 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_639.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_639.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _127_300}))
in (let t0 = (subst sub t0)
in ((let _36_643 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _36_643.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_643.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

let close_branch = (fun _36_648 -> (match (_36_648) with
| (p, wopt, e) -> begin
(let _36_651 = (close_pat p)
in (match (_36_651) with
| (p, closing) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _127_303 = (subst closing w)
in Some (_127_303))
end)
in (let e = (subst closing e)
in (p, wopt, e)))
end))
end))

let univ_var_opening = (fun us -> (let n = ((FStar_List.length us) - 1)
in (let _36_664 = (let _127_308 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _127_308 FStar_List.unzip))
in (match (_36_664) with
| (s, us') -> begin
(s, us')
end))))

let open_univ_vars = (fun us t -> (let _36_669 = (univ_var_opening us)
in (match (_36_669) with
| (s, us') -> begin
(let t = (subst s t)
in (us', t))
end)))

let open_univ_vars_comp = (fun us c -> (let _36_675 = (univ_var_opening us)
in (match (_36_675) with
| (s, us') -> begin
(let _127_317 = (subst_comp s c)
in (us', _127_317))
end)))

let close_univ_vars = (fun us t -> (let n = ((FStar_List.length us) - 1)
in (let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

let close_univ_vars_comp = (fun us c -> (let n = ((FStar_List.length us) - 1)
in (let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

let is_top_level = (fun _36_7 -> (match (_36_7) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_36_700); FStar_Syntax_Syntax.lbunivs = _36_698; FStar_Syntax_Syntax.lbtyp = _36_696; FStar_Syntax_Syntax.lbeff = _36_694; FStar_Syntax_Syntax.lbdef = _36_692}::_36_690 -> begin
true
end
| _36_705 -> begin
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

let mk_subst_binders = (fun args -> (let _36_718 = (FStar_List.fold_right (fun a _36_714 -> (match (_36_714) with
| (s, i) -> begin
((FStar_Syntax_Syntax.DB ((i, (Prims.fst a))))::s, (i + 1))
end)) args ([], 0))
in (match (_36_718) with
| (s, _36_717) -> begin
s
end)))

let subst_binders = (fun bs args t -> (let _127_349 = (mk_subst_binders args)
in (subst _127_349 t)))

let subst_binders_comp = (fun bs args t -> (let _127_356 = (mk_subst_binders args)
in (subst_comp _127_356 t)))

let close_tscheme = (fun binders _36_728 -> (match (_36_728) with
| (us, t) -> begin
(let n = ((FStar_List.length binders) - 1)
in (let k = (FStar_List.length us)
in (let s = (FStar_List.mapi (fun i _36_735 -> (match (_36_735) with
| (x, _36_734) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (let t = (subst s t)
in (us, t)))))
end))

let close_univ_vars_tscheme = (fun us _36_741 -> (match (_36_741) with
| (us', t) -> begin
(let n = ((FStar_List.length us) - 1)
in (let k = (FStar_List.length us')
in (let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _127_369 = (subst s t)
in (us', _127_369)))))
end))

let opening_of_binders = (fun bs -> (let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _36_753 -> (match (_36_753) with
| (x, _36_752) -> begin
(let _127_375 = (let _127_374 = (FStar_Syntax_Syntax.bv_to_name x)
in ((n - i), _127_374))
in FStar_Syntax_Syntax.DB (_127_375))
end))))))




