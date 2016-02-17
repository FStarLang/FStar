
open Prims
# 58 "FStar.Syntax.Subst.fst"
let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _32_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _32_17 -> begin
t
end)
end
| _32_19 -> begin
t
end))

# 67 "FStar.Syntax.Subst.fst"
let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(
# 72 "FStar.Syntax.Subst.fst"
let t' = (let _111_8 = (c ())
in (force_delayed_thunk _111_8))
in (
# 72 "FStar.Syntax.Subst.fst"
let _32_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _32_32 -> begin
t
end)
end
| Some (t') -> begin
(
# 75 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 75 "FStar.Syntax.Subst.fst"
let _32_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _32_39 -> begin
t
end))

# 78 "FStar.Syntax.Subst.fst"
let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _32_46 -> begin
u
end)
end
| _32_48 -> begin
u
end))

# 90 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _111_15 = (FStar_All.pipe_right s (FStar_List.map (fun _32_53 -> (match (_32_53) with
| (b, _32_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _111_15 (FStar_String.concat ", "))))

# 93 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _32_1 -> (match (_32_1) with
| FStar_Syntax_Syntax.DB (i, t) when (i = a.FStar_Syntax_Syntax.index) -> begin
Some (t)
end
| _32_62 -> begin
None
end))))

# 94 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _32_2 -> (match (_32_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _111_26 = (FStar_Syntax_Syntax.bv_to_tm (
# 95 "FStar.Syntax.Subst.fst"
let _32_70 = x
in {FStar_Syntax_Syntax.ppname = _32_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _32_70.FStar_Syntax_Syntax.sort}))
in Some (_111_26))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _32_77 -> begin
None
end))))

# 98 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _32_3 -> (match (_32_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _32_86 -> begin
None
end))))

# 101 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _32_4 -> (match (_32_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _32_95 -> begin
None
end))))

# 108 "FStar.Syntax.Subst.fst"
let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| s0::rest -> begin
(match ((f s0)) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some ((rest, st))
end)
end))

# 115 "FStar.Syntax.Subst.fst"
let map_some_curry = (fun f x _32_5 -> (match (_32_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 119 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _111_64 = (apply_until_some f s)
in (FStar_All.pipe_right _111_64 (map_some_curry g t))))

# 123 "FStar.Syntax.Subst.fst"
let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (
# 124 "FStar.Syntax.Subst.fst"
let u = (compress_univ u)
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
(let _111_69 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_111_69))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _111_70 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_111_70))
end)))

# 139 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _32_139 -> begin
(
# 143 "FStar.Syntax.Subst.fst"
let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t', (FStar_List.append s' s)))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_32_158), _32_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _111_86 = (let _111_85 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_111_85))
in (FStar_Syntax_Syntax.mk _111_86 None t0.FStar_Syntax_Syntax.pos))
end
| _32_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _32_6 -> (match (_32_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _111_91 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_111_91))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _32_184 -> begin
(
# 179 "FStar.Syntax.Subst.fst"
let _32_185 = t
in (let _111_98 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _111_97 = (FStar_List.map (fun _32_189 -> (match (_32_189) with
| (t, imp) -> begin
(let _111_95 = (subst' s t)
in (_111_95, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _111_96 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _32_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _111_98; FStar_Syntax_Syntax.effect_args = _111_97; FStar_Syntax_Syntax.flags = _111_96}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _32_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _111_101 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _111_101))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _111_102 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _111_102))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _111_103 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _111_103))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))

# 194 "FStar.Syntax.Subst.fst"
let shift : Prims.int  ->  FStar_Syntax_Syntax.subst_elt  ->  FStar_Syntax_Syntax.subst_elt = (fun n s -> (match (s) with
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
| FStar_Syntax_Syntax.NT (_32_224) -> begin
s
end))

# 200 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 201 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 202 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _32_233 -> (match (_32_233) with
| (x, imp) -> begin
(let _111_121 = (
# 202 "FStar.Syntax.Subst.fst"
let _32_234 = x
in (let _111_120 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_120}))
in (_111_121, imp))
end))

# 203 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _111_126 = (shift_subst' i s)
in (subst_binder' _111_126 b))
end))))

# 207 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _32_243 -> (match (_32_243) with
| (t, imp) -> begin
(let _111_129 = (subst' s t)
in (_111_129, imp))
end))

# 208 "FStar.Syntax.Subst.fst"
let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

# 209 "FStar.Syntax.Subst.fst"
let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (
# 210 "FStar.Syntax.Subst.fst"
let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_32_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 216 "FStar.Syntax.Subst.fst"
let _32_261 = (aux n p)
in (match (_32_261) with
| (p, m) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _111_142 = (aux n p)
in (Prims.fst _111_142))) ps)
in ((
# 218 "FStar.Syntax.Subst.fst"
let _32_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _32_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 221 "FStar.Syntax.Subst.fst"
let _32_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _32_272 _32_275 -> (match ((_32_272, _32_275)) with
| ((pats, n), (p, imp)) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _32_278 = (aux n p)
in (match (_32_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_32_281) with
| (pats, n) -> begin
((
# 224 "FStar.Syntax.Subst.fst"
let _32_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _32_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_282.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 227 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 228 "FStar.Syntax.Subst.fst"
let x = (
# 228 "FStar.Syntax.Subst.fst"
let _32_287 = x
in (let _111_145 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_145}))
in ((
# 229 "FStar.Syntax.Subst.fst"
let _32_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _32_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 232 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 233 "FStar.Syntax.Subst.fst"
let x = (
# 233 "FStar.Syntax.Subst.fst"
let _32_295 = x
in (let _111_146 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_146}))
in ((
# 234 "FStar.Syntax.Subst.fst"
let _32_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _32_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 237 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 238 "FStar.Syntax.Subst.fst"
let x = (
# 238 "FStar.Syntax.Subst.fst"
let _32_305 = x
in (let _111_147 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_147}))
in (
# 239 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 240 "FStar.Syntax.Subst.fst"
let _32_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _32_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 243 "FStar.Syntax.Subst.fst"
let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _111_155 = (
# 246 "FStar.Syntax.Subst.fst"
let _32_316 = l
in (let _111_154 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _32_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _111_154; FStar_Syntax_Syntax.cflags = _32_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _32_318 -> (match (()) with
| () -> begin
(let _111_153 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _111_153))
end))}))
in Some (_111_155))
end))

# 249 "FStar.Syntax.Subst.fst"
let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_32_322) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(
# 265 "FStar.Syntax.Subst.fst"
let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _111_166 = (let _111_165 = (let _111_164 = (subst' s t0)
in (let _111_163 = (subst_args' s args)
in (_111_164, _111_163)))
in FStar_Syntax_Syntax.Tm_app (_111_165))
in (FStar_Syntax_Syntax.mk _111_166 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _111_170 = (let _111_169 = (let _111_168 = (subst' s t0)
in (let _111_167 = (subst' s t1)
in (_111_168, _111_167, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_111_169))
in (FStar_Syntax_Syntax.mk _111_170 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 273 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 274 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _111_175 = (let _111_174 = (let _111_173 = (subst_binders' s bs)
in (let _111_172 = (subst' s' body)
in (let _111_171 = (push_subst_lcomp s' lopt)
in (_111_173, _111_172, _111_171))))
in FStar_Syntax_Syntax.Tm_abs (_111_174))
in (FStar_Syntax_Syntax.mk _111_175 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 278 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _111_180 = (let _111_179 = (let _111_178 = (subst_binders' s bs)
in (let _111_177 = (let _111_176 = (shift_subst' n s)
in (subst_comp' _111_176 comp))
in (_111_178, _111_177)))
in FStar_Syntax_Syntax.Tm_arrow (_111_179))
in (FStar_Syntax_Syntax.mk _111_180 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 282 "FStar.Syntax.Subst.fst"
let x = (
# 282 "FStar.Syntax.Subst.fst"
let _32_373 = x
in (let _111_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_181}))
in (
# 283 "FStar.Syntax.Subst.fst"
let phi = (let _111_182 = (shift_subst' 1 s)
in (subst' _111_182 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 287 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 288 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _32_385 -> (match (_32_385) with
| (pat, wopt, branch) -> begin
(
# 289 "FStar.Syntax.Subst.fst"
let _32_388 = (subst_pat' s pat)
in (match (_32_388) with
| (pat, n) -> begin
(
# 290 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 291 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _111_184 = (subst' s w)
in Some (_111_184))
end)
in (
# 294 "FStar.Syntax.Subst.fst"
let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(
# 299 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length lbs)
in (
# 300 "FStar.Syntax.Subst.fst"
let sn = (shift_subst' n s)
in (
# 301 "FStar.Syntax.Subst.fst"
let body = (subst' sn body)
in (
# 302 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 303 "FStar.Syntax.Subst.fst"
let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (
# 304 "FStar.Syntax.Subst.fst"
let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (
# 307 "FStar.Syntax.Subst.fst"
let _32_408 = lb
in {FStar_Syntax_Syntax.lbname = _32_408.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _32_408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _32_408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd}))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _111_190 = (let _111_189 = (let _111_188 = (subst' s t0)
in (let _111_187 = (let _111_186 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_111_186))
in (_111_188, _111_187)))
in FStar_Syntax_Syntax.Tm_meta (_111_189))
in (FStar_Syntax_Syntax.mk _111_190 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _111_193 = (let _111_192 = (let _111_191 = (subst' s t)
in (_111_191, m))
in FStar_Syntax_Syntax.Tm_meta (_111_192))
in (FStar_Syntax_Syntax.mk _111_193 None t.FStar_Syntax_Syntax.pos))
end))

# 316 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 317 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 320 "FStar.Syntax.Subst.fst"
let t' = (let _111_196 = (push_subst s t)
in (compress _111_196))
in (
# 321 "FStar.Syntax.Subst.fst"
let _32_430 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _32_433 -> begin
(force_uvar t)
end)))

# 327 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 328 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 329 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _111_208 = (FStar_List.fold_right (fun _32_442 _32_445 -> (match ((_32_442, _32_445)) with
| ((x, _32_441), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _111_208 Prims.fst)))

# 331 "FStar.Syntax.Subst.fst"
let open_binders' = (fun bs -> (
# 332 "FStar.Syntax.Subst.fst"
let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(
# 335 "FStar.Syntax.Subst.fst"
let x' = (
# 335 "FStar.Syntax.Subst.fst"
let _32_456 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _111_214 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_214}))
in (
# 336 "FStar.Syntax.Subst.fst"
let o = (let _111_218 = (let _111_216 = (let _111_215 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _111_215))
in FStar_Syntax_Syntax.DB (_111_216))
in (let _111_217 = (shift_subst 1 o)
in (_111_218)::_111_217))
in (
# 337 "FStar.Syntax.Subst.fst"
let _32_462 = (aux bs' o)
in (match (_32_462) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 340 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _111_221 = (open_binders' bs)
in (Prims.fst _111_221)))

# 341 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 342 "FStar.Syntax.Subst.fst"
let _32_468 = (open_binders' bs)
in (match (_32_468) with
| (bs', opening) -> begin
(let _111_226 = (subst opening t)
in (bs', _111_226, opening))
end)))

# 344 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 345 "FStar.Syntax.Subst.fst"
let _32_475 = (open_term' bs t)
in (match (_32_475) with
| (b, t, _32_474) -> begin
(b, t)
end)))

# 347 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 348 "FStar.Syntax.Subst.fst"
let _32_480 = (open_binders' bs)
in (match (_32_480) with
| (bs', opening) -> begin
(let _111_235 = (subst_comp opening t)
in (bs', _111_235))
end)))

# 350 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 351 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_32_488) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 357 "FStar.Syntax.Subst.fst"
let _32_496 = (aux sub p)
in (match (_32_496) with
| (p, sub) -> begin
(
# 358 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _111_243 = (aux sub p)
in (Prims.fst _111_243))) ps)
in ((
# 359 "FStar.Syntax.Subst.fst"
let _32_499 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _32_499.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_499.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 362 "FStar.Syntax.Subst.fst"
let _32_516 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _32_507 _32_510 -> (match ((_32_507, _32_510)) with
| ((pats, sub), (p, imp)) -> begin
(
# 363 "FStar.Syntax.Subst.fst"
let _32_513 = (aux sub p)
in (match (_32_513) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_32_516) with
| (pats, sub) -> begin
((
# 365 "FStar.Syntax.Subst.fst"
let _32_517 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _32_517.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_517.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 368 "FStar.Syntax.Subst.fst"
let x' = (
# 368 "FStar.Syntax.Subst.fst"
let _32_521 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _111_246 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_246}))
in (
# 369 "FStar.Syntax.Subst.fst"
let sub = (let _111_250 = (let _111_248 = (let _111_247 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _111_247))
in FStar_Syntax_Syntax.DB (_111_248))
in (let _111_249 = (shift_subst 1 sub)
in (_111_250)::_111_249))
in ((
# 370 "FStar.Syntax.Subst.fst"
let _32_525 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _32_525.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_525.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 373 "FStar.Syntax.Subst.fst"
let x' = (
# 373 "FStar.Syntax.Subst.fst"
let _32_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _111_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_251}))
in (
# 374 "FStar.Syntax.Subst.fst"
let sub = (let _111_255 = (let _111_253 = (let _111_252 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _111_252))
in FStar_Syntax_Syntax.DB (_111_253))
in (let _111_254 = (shift_subst 1 sub)
in (_111_255)::_111_254))
in ((
# 375 "FStar.Syntax.Subst.fst"
let _32_533 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _32_533.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_533.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 378 "FStar.Syntax.Subst.fst"
let x = (
# 378 "FStar.Syntax.Subst.fst"
let _32_539 = x
in (let _111_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_539.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_539.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_256}))
in (
# 379 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 380 "FStar.Syntax.Subst.fst"
let _32_543 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _32_543.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_543.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 384 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _32_548 -> (match (_32_548) with
| (p, wopt, e) -> begin
(
# 385 "FStar.Syntax.Subst.fst"
let _32_551 = (open_pat p)
in (match (_32_551) with
| (p, opening) -> begin
(
# 386 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _111_259 = (subst opening w)
in Some (_111_259))
end)
in (
# 389 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 392 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _111_264 = (closing_subst bs)
in (subst _111_264 t)))

# 393 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _111_269 = (closing_subst bs)
in (subst_comp _111_269 c)))

# 394 "FStar.Syntax.Subst.fst"
let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (
# 395 "FStar.Syntax.Subst.fst"
let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(
# 398 "FStar.Syntax.Subst.fst"
let x = (
# 398 "FStar.Syntax.Subst.fst"
let _32_571 = x
in (let _111_276 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_276}))
in (
# 399 "FStar.Syntax.Subst.fst"
let s' = (let _111_277 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_111_277)
in (let _111_278 = (aux s' tl)
in ((x, imp))::_111_278)))
end))
in (aux [] bs)))

# 403 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 404 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 405 "FStar.Syntax.Subst.fst"
let _32_578 = lc
in (let _111_285 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _32_578.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _111_285; FStar_Syntax_Syntax.cflags = _32_578.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _32_580 -> (match (()) with
| () -> begin
(let _111_284 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _111_284))
end))}))))

# 408 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 409 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_32_588) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 415 "FStar.Syntax.Subst.fst"
let _32_596 = (aux sub p)
in (match (_32_596) with
| (p, sub) -> begin
(
# 416 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _111_293 = (aux sub p)
in (Prims.fst _111_293))) ps)
in ((
# 417 "FStar.Syntax.Subst.fst"
let _32_599 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _32_599.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_599.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 420 "FStar.Syntax.Subst.fst"
let _32_616 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _32_607 _32_610 -> (match ((_32_607, _32_610)) with
| ((pats, sub), (p, imp)) -> begin
(
# 421 "FStar.Syntax.Subst.fst"
let _32_613 = (aux sub p)
in (match (_32_613) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_32_616) with
| (pats, sub) -> begin
((
# 423 "FStar.Syntax.Subst.fst"
let _32_617 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _32_617.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_617.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 426 "FStar.Syntax.Subst.fst"
let x = (
# 426 "FStar.Syntax.Subst.fst"
let _32_621 = x
in (let _111_296 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_296}))
in (
# 427 "FStar.Syntax.Subst.fst"
let sub = (let _111_297 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_111_297)
in ((
# 428 "FStar.Syntax.Subst.fst"
let _32_625 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _32_625.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_625.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 431 "FStar.Syntax.Subst.fst"
let x = (
# 431 "FStar.Syntax.Subst.fst"
let _32_629 = x
in (let _111_298 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_629.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_629.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_298}))
in (
# 432 "FStar.Syntax.Subst.fst"
let sub = (let _111_299 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_111_299)
in ((
# 433 "FStar.Syntax.Subst.fst"
let _32_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _32_633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_633.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 436 "FStar.Syntax.Subst.fst"
let x = (
# 436 "FStar.Syntax.Subst.fst"
let _32_639 = x
in (let _111_300 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _32_639.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _32_639.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _111_300}))
in (
# 437 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 438 "FStar.Syntax.Subst.fst"
let _32_643 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _32_643.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _32_643.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 441 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _32_648 -> (match (_32_648) with
| (p, wopt, e) -> begin
(
# 442 "FStar.Syntax.Subst.fst"
let _32_651 = (close_pat p)
in (match (_32_651) with
| (p, closing) -> begin
(
# 443 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _111_303 = (subst closing w)
in Some (_111_303))
end)
in (
# 446 "FStar.Syntax.Subst.fst"
let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 449 "FStar.Syntax.Subst.fst"
let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (
# 450 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 451 "FStar.Syntax.Subst.fst"
let _32_664 = (let _111_308 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 452 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _111_308 FStar_List.unzip))
in (match (_32_664) with
| (s, us') -> begin
(s, us')
end))))

# 456 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 457 "FStar.Syntax.Subst.fst"
let _32_669 = (univ_var_opening us)
in (match (_32_669) with
| (s, us') -> begin
(
# 458 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 461 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 462 "FStar.Syntax.Subst.fst"
let _32_675 = (univ_var_opening us)
in (match (_32_675) with
| (s, us') -> begin
(let _111_317 = (subst_comp s c)
in (us', _111_317))
end)))

# 465 "FStar.Syntax.Subst.fst"
let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (
# 466 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 467 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 470 "FStar.Syntax.Subst.fst"
let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (
# 471 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 472 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 475 "FStar.Syntax.Subst.fst"
let is_top_level : FStar_Syntax_Syntax.letbinding Prims.list  ->  Prims.bool = (fun _32_7 -> (match (_32_7) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_32_700); FStar_Syntax_Syntax.lbunivs = _32_698; FStar_Syntax_Syntax.lbtyp = _32_696; FStar_Syntax_Syntax.lbeff = _32_694; FStar_Syntax_Syntax.lbdef = _32_692}::_32_690 -> begin
true
end
| _32_705 -> begin
false
end))

# 479 "FStar.Syntax.Subst.fst"
let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: open_let_rec")
end)

# 483 "FStar.Syntax.Subst.fst"
let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: close_let_rec")
end)

# 488 "FStar.Syntax.Subst.fst"
let mk_subst_binders = (fun args -> (
# 489 "FStar.Syntax.Subst.fst"
let _32_718 = (FStar_List.fold_right (fun a _32_714 -> (match (_32_714) with
| (s, i) -> begin
((FStar_Syntax_Syntax.DB ((i, (Prims.fst a))))::s, (i + 1))
end)) args ([], 0))
in (match (_32_718) with
| (s, _32_717) -> begin
s
end)))

# 492 "FStar.Syntax.Subst.fst"
let subst_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs args t -> (let _111_349 = (mk_subst_binders args)
in (subst _111_349 t)))

# 493 "FStar.Syntax.Subst.fst"
let subst_binders_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs args t -> (let _111_356 = (mk_subst_binders args)
in (subst_comp _111_356 t)))

# 496 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _32_728 -> (match (_32_728) with
| (us, t) -> begin
(
# 497 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 498 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 499 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _32_735 -> (match (_32_735) with
| (x, _32_734) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 500 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 503 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _32_741 -> (match (_32_741) with
| (us', t) -> begin
(
# 504 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 505 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us')
in (
# 506 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _111_369 = (subst s t)
in (us', _111_369)))))
end))

# 509 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 510 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _32_753 -> (match (_32_753) with
| (x, _32_752) -> begin
(let _111_375 = (let _111_374 = (FStar_Syntax_Syntax.bv_to_name x)
in ((n - i), _111_374))
in FStar_Syntax_Syntax.DB (_111_375))
end))))))




