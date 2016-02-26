
open Prims
# 58 "FStar.Syntax.Subst.fst"
let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _31_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _31_17 -> begin
t
end)
end
| _31_19 -> begin
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
let t' = (let _113_8 = (c ())
in (force_delayed_thunk _113_8))
in (
# 72 "FStar.Syntax.Subst.fst"
let _31_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _31_32 -> begin
t
end)
end
| Some (t') -> begin
(
# 75 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 75 "FStar.Syntax.Subst.fst"
let _31_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _31_39 -> begin
t
end))

# 78 "FStar.Syntax.Subst.fst"
let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _31_46 -> begin
u
end)
end
| _31_48 -> begin
u
end))

# 90 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _113_15 = (FStar_All.pipe_right s (FStar_List.map (fun _31_53 -> (match (_31_53) with
| (b, _31_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _113_15 (FStar_String.concat ", "))))

# 93 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _31_1 -> (match (_31_1) with
| FStar_Syntax_Syntax.DB (i, t) when (i = a.FStar_Syntax_Syntax.index) -> begin
Some (t)
end
| _31_62 -> begin
None
end))))

# 94 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _31_2 -> (match (_31_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _113_26 = (FStar_Syntax_Syntax.bv_to_tm (
# 95 "FStar.Syntax.Subst.fst"
let _31_70 = x
in {FStar_Syntax_Syntax.ppname = _31_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _31_70.FStar_Syntax_Syntax.sort}))
in Some (_113_26))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _31_77 -> begin
None
end))))

# 98 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _31_3 -> (match (_31_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _31_86 -> begin
None
end))))

# 101 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _31_4 -> (match (_31_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _31_95 -> begin
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
let map_some_curry = (fun f x _31_5 -> (match (_31_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 119 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _113_64 = (apply_until_some f s)
in (FStar_All.pipe_right _113_64 (map_some_curry g t))))

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
(let _113_69 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_113_69))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _113_70 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_113_70))
end)))

# 139 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_139 -> begin
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
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_31_158), _31_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _113_86 = (let _113_85 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_113_85))
in (FStar_Syntax_Syntax.mk _113_86 None t0.FStar_Syntax_Syntax.pos))
end
| _31_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_6 -> (match (_31_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _113_91 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_113_91))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_184 -> begin
(
# 179 "FStar.Syntax.Subst.fst"
let _31_185 = t
in (let _113_98 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _113_97 = (FStar_List.map (fun _31_189 -> (match (_31_189) with
| (t, imp) -> begin
(let _113_95 = (subst' s t)
in (_113_95, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _113_96 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _31_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _113_98; FStar_Syntax_Syntax.effect_args = _113_97; FStar_Syntax_Syntax.flags = _113_96}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _113_101 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _113_101))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _113_102 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _113_102))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _113_103 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _113_103))
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
| FStar_Syntax_Syntax.NT (_31_224) -> begin
s
end))

# 200 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 201 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 202 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _31_233 -> (match (_31_233) with
| (x, imp) -> begin
(let _113_121 = (
# 202 "FStar.Syntax.Subst.fst"
let _31_234 = x
in (let _113_120 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_120}))
in (_113_121, imp))
end))

# 203 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _113_126 = (shift_subst' i s)
in (subst_binder' _113_126 b))
end))))

# 207 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _31_243 -> (match (_31_243) with
| (t, imp) -> begin
(let _113_129 = (subst' s t)
in (_113_129, imp))
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
| FStar_Syntax_Syntax.Pat_constant (_31_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 216 "FStar.Syntax.Subst.fst"
let _31_261 = (aux n p)
in (match (_31_261) with
| (p, m) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _113_142 = (aux n p)
in (Prims.fst _113_142))) ps)
in ((
# 218 "FStar.Syntax.Subst.fst"
let _31_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 221 "FStar.Syntax.Subst.fst"
let _31_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_272 _31_275 -> (match ((_31_272, _31_275)) with
| ((pats, n), (p, imp)) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _31_278 = (aux n p)
in (match (_31_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_31_281) with
| (pats, n) -> begin
((
# 224 "FStar.Syntax.Subst.fst"
let _31_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_282.FStar_Syntax_Syntax.p}), n)
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
let _31_287 = x
in (let _113_145 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_145}))
in ((
# 229 "FStar.Syntax.Subst.fst"
let _31_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _31_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 232 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 233 "FStar.Syntax.Subst.fst"
let x = (
# 233 "FStar.Syntax.Subst.fst"
let _31_295 = x
in (let _113_146 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_146}))
in ((
# 234 "FStar.Syntax.Subst.fst"
let _31_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _31_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 237 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 238 "FStar.Syntax.Subst.fst"
let x = (
# 238 "FStar.Syntax.Subst.fst"
let _31_305 = x
in (let _113_147 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_147}))
in (
# 239 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 240 "FStar.Syntax.Subst.fst"
let _31_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 243 "FStar.Syntax.Subst.fst"
let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _113_155 = (
# 246 "FStar.Syntax.Subst.fst"
let _31_316 = l
in (let _113_154 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _31_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _113_154; FStar_Syntax_Syntax.cflags = _31_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _31_318 -> (match (()) with
| () -> begin
(let _113_153 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _113_153))
end))}))
in Some (_113_155))
end))

# 249 "FStar.Syntax.Subst.fst"
let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_31_322) -> begin
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
(let _113_166 = (let _113_165 = (let _113_164 = (subst' s t0)
in (let _113_163 = (subst_args' s args)
in (_113_164, _113_163)))
in FStar_Syntax_Syntax.Tm_app (_113_165))
in (FStar_Syntax_Syntax.mk _113_166 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _113_170 = (let _113_169 = (let _113_168 = (subst' s t0)
in (let _113_167 = (subst' s t1)
in (_113_168, _113_167, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_113_169))
in (FStar_Syntax_Syntax.mk _113_170 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 273 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 274 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _113_175 = (let _113_174 = (let _113_173 = (subst_binders' s bs)
in (let _113_172 = (subst' s' body)
in (let _113_171 = (push_subst_lcomp s' lopt)
in (_113_173, _113_172, _113_171))))
in FStar_Syntax_Syntax.Tm_abs (_113_174))
in (FStar_Syntax_Syntax.mk _113_175 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 278 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _113_180 = (let _113_179 = (let _113_178 = (subst_binders' s bs)
in (let _113_177 = (let _113_176 = (shift_subst' n s)
in (subst_comp' _113_176 comp))
in (_113_178, _113_177)))
in FStar_Syntax_Syntax.Tm_arrow (_113_179))
in (FStar_Syntax_Syntax.mk _113_180 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 282 "FStar.Syntax.Subst.fst"
let x = (
# 282 "FStar.Syntax.Subst.fst"
let _31_373 = x
in (let _113_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_181}))
in (
# 283 "FStar.Syntax.Subst.fst"
let phi = (let _113_182 = (shift_subst' 1 s)
in (subst' _113_182 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 287 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 288 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _31_385 -> (match (_31_385) with
| (pat, wopt, branch) -> begin
(
# 289 "FStar.Syntax.Subst.fst"
let _31_388 = (subst_pat' s pat)
in (match (_31_388) with
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
(let _113_184 = (subst' s w)
in Some (_113_184))
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
let _31_408 = lb
in {FStar_Syntax_Syntax.lbname = _31_408.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _31_408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _31_408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd}))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _113_190 = (let _113_189 = (let _113_188 = (subst' s t0)
in (let _113_187 = (let _113_186 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_113_186))
in (_113_188, _113_187)))
in FStar_Syntax_Syntax.Tm_meta (_113_189))
in (FStar_Syntax_Syntax.mk _113_190 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _113_193 = (let _113_192 = (let _113_191 = (subst' s t)
in (_113_191, m))
in FStar_Syntax_Syntax.Tm_meta (_113_192))
in (FStar_Syntax_Syntax.mk _113_193 None t.FStar_Syntax_Syntax.pos))
end))

# 316 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 317 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 320 "FStar.Syntax.Subst.fst"
let t' = (let _113_196 = (push_subst s t)
in (compress _113_196))
in (
# 321 "FStar.Syntax.Subst.fst"
let _31_430 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _31_433 -> begin
(force_uvar t)
end)))

# 327 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 328 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 329 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _113_208 = (FStar_List.fold_right (fun _31_442 _31_445 -> (match ((_31_442, _31_445)) with
| ((x, _31_441), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _113_208 Prims.fst)))

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
let _31_456 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _113_214 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_214}))
in (
# 336 "FStar.Syntax.Subst.fst"
let o = (let _113_218 = (let _113_216 = (let _113_215 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _113_215))
in FStar_Syntax_Syntax.DB (_113_216))
in (let _113_217 = (shift_subst 1 o)
in (_113_218)::_113_217))
in (
# 337 "FStar.Syntax.Subst.fst"
let _31_462 = (aux bs' o)
in (match (_31_462) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 340 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _113_221 = (open_binders' bs)
in (Prims.fst _113_221)))

# 341 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 342 "FStar.Syntax.Subst.fst"
let _31_468 = (open_binders' bs)
in (match (_31_468) with
| (bs', opening) -> begin
(let _113_226 = (subst opening t)
in (bs', _113_226, opening))
end)))

# 344 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 345 "FStar.Syntax.Subst.fst"
let _31_475 = (open_term' bs t)
in (match (_31_475) with
| (b, t, _31_474) -> begin
(b, t)
end)))

# 347 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 348 "FStar.Syntax.Subst.fst"
let _31_480 = (open_binders' bs)
in (match (_31_480) with
| (bs', opening) -> begin
(let _113_235 = (subst_comp opening t)
in (bs', _113_235))
end)))

# 350 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 351 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_31_488) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 357 "FStar.Syntax.Subst.fst"
let _31_496 = (aux sub p)
in (match (_31_496) with
| (p, sub) -> begin
(
# 358 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _113_243 = (aux sub p)
in (Prims.fst _113_243))) ps)
in ((
# 359 "FStar.Syntax.Subst.fst"
let _31_499 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_499.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_499.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 362 "FStar.Syntax.Subst.fst"
let _31_516 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_507 _31_510 -> (match ((_31_507, _31_510)) with
| ((pats, sub), (p, imp)) -> begin
(
# 363 "FStar.Syntax.Subst.fst"
let _31_513 = (aux sub p)
in (match (_31_513) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_31_516) with
| (pats, sub) -> begin
((
# 365 "FStar.Syntax.Subst.fst"
let _31_517 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_517.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_517.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 368 "FStar.Syntax.Subst.fst"
let x' = (
# 368 "FStar.Syntax.Subst.fst"
let _31_521 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _113_246 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_246}))
in (
# 369 "FStar.Syntax.Subst.fst"
let sub = (let _113_250 = (let _113_248 = (let _113_247 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _113_247))
in FStar_Syntax_Syntax.DB (_113_248))
in (let _113_249 = (shift_subst 1 sub)
in (_113_250)::_113_249))
in ((
# 370 "FStar.Syntax.Subst.fst"
let _31_525 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _31_525.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_525.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 373 "FStar.Syntax.Subst.fst"
let x' = (
# 373 "FStar.Syntax.Subst.fst"
let _31_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _113_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_251}))
in (
# 374 "FStar.Syntax.Subst.fst"
let sub = (let _113_255 = (let _113_253 = (let _113_252 = (FStar_Syntax_Syntax.bv_to_name x')
in (0, _113_252))
in FStar_Syntax_Syntax.DB (_113_253))
in (let _113_254 = (shift_subst 1 sub)
in (_113_255)::_113_254))
in ((
# 375 "FStar.Syntax.Subst.fst"
let _31_533 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _31_533.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_533.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 378 "FStar.Syntax.Subst.fst"
let x = (
# 378 "FStar.Syntax.Subst.fst"
let _31_539 = x
in (let _113_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_539.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_539.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_256}))
in (
# 379 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 380 "FStar.Syntax.Subst.fst"
let _31_543 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_543.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_543.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 384 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _31_548 -> (match (_31_548) with
| (p, wopt, e) -> begin
(
# 385 "FStar.Syntax.Subst.fst"
let _31_551 = (open_pat p)
in (match (_31_551) with
| (p, opening) -> begin
(
# 386 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _113_259 = (subst opening w)
in Some (_113_259))
end)
in (
# 389 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 392 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _113_264 = (closing_subst bs)
in (subst _113_264 t)))

# 393 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _113_269 = (closing_subst bs)
in (subst_comp _113_269 c)))

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
let _31_571 = x
in (let _113_276 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_571.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_571.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_276}))
in (
# 399 "FStar.Syntax.Subst.fst"
let s' = (let _113_277 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_113_277)
in (let _113_278 = (aux s' tl)
in ((x, imp))::_113_278)))
end))
in (aux [] bs)))

# 403 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 404 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 405 "FStar.Syntax.Subst.fst"
let _31_578 = lc
in (let _113_285 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _31_578.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _113_285; FStar_Syntax_Syntax.cflags = _31_578.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _31_580 -> (match (()) with
| () -> begin
(let _113_284 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _113_284))
end))}))))

# 408 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 409 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_31_588) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 415 "FStar.Syntax.Subst.fst"
let _31_596 = (aux sub p)
in (match (_31_596) with
| (p, sub) -> begin
(
# 416 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _113_293 = (aux sub p)
in (Prims.fst _113_293))) ps)
in ((
# 417 "FStar.Syntax.Subst.fst"
let _31_599 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_599.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_599.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 420 "FStar.Syntax.Subst.fst"
let _31_616 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_607 _31_610 -> (match ((_31_607, _31_610)) with
| ((pats, sub), (p, imp)) -> begin
(
# 421 "FStar.Syntax.Subst.fst"
let _31_613 = (aux sub p)
in (match (_31_613) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_31_616) with
| (pats, sub) -> begin
((
# 423 "FStar.Syntax.Subst.fst"
let _31_617 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_617.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_617.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 426 "FStar.Syntax.Subst.fst"
let x = (
# 426 "FStar.Syntax.Subst.fst"
let _31_621 = x
in (let _113_296 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_296}))
in (
# 427 "FStar.Syntax.Subst.fst"
let sub = (let _113_297 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_113_297)
in ((
# 428 "FStar.Syntax.Subst.fst"
let _31_625 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _31_625.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_625.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 431 "FStar.Syntax.Subst.fst"
let x = (
# 431 "FStar.Syntax.Subst.fst"
let _31_629 = x
in (let _113_298 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_629.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_629.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_298}))
in (
# 432 "FStar.Syntax.Subst.fst"
let sub = (let _113_299 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_113_299)
in ((
# 433 "FStar.Syntax.Subst.fst"
let _31_633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _31_633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_633.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 436 "FStar.Syntax.Subst.fst"
let x = (
# 436 "FStar.Syntax.Subst.fst"
let _31_639 = x
in (let _113_300 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_639.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_639.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _113_300}))
in (
# 437 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 438 "FStar.Syntax.Subst.fst"
let _31_643 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_643.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_643.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 441 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _31_648 -> (match (_31_648) with
| (p, wopt, e) -> begin
(
# 442 "FStar.Syntax.Subst.fst"
let _31_651 = (close_pat p)
in (match (_31_651) with
| (p, closing) -> begin
(
# 443 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _113_303 = (subst closing w)
in Some (_113_303))
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
let _31_664 = (let _113_308 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 452 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _113_308 FStar_List.unzip))
in (match (_31_664) with
| (s, us') -> begin
(s, us')
end))))

# 456 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 457 "FStar.Syntax.Subst.fst"
let _31_669 = (univ_var_opening us)
in (match (_31_669) with
| (s, us') -> begin
(
# 458 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 461 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 462 "FStar.Syntax.Subst.fst"
let _31_675 = (univ_var_opening us)
in (match (_31_675) with
| (s, us') -> begin
(let _113_317 = (subst_comp s c)
in (us', _113_317))
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
let is_top_level : FStar_Syntax_Syntax.letbinding Prims.list  ->  Prims.bool = (fun _31_7 -> (match (_31_7) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_31_700); FStar_Syntax_Syntax.lbunivs = _31_698; FStar_Syntax_Syntax.lbtyp = _31_696; FStar_Syntax_Syntax.lbeff = _31_694; FStar_Syntax_Syntax.lbdef = _31_692}::_31_690 -> begin
true
end
| _31_705 -> begin
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
let _31_718 = (FStar_List.fold_right (fun a _31_714 -> (match (_31_714) with
| (s, i) -> begin
((FStar_Syntax_Syntax.DB ((i, (Prims.fst a))))::s, (i + 1))
end)) args ([], 0))
in (match (_31_718) with
| (s, _31_717) -> begin
s
end)))

# 492 "FStar.Syntax.Subst.fst"
let subst_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs args t -> (let _113_349 = (mk_subst_binders args)
in (subst _113_349 t)))

# 493 "FStar.Syntax.Subst.fst"
let subst_binders_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs args t -> (let _113_356 = (mk_subst_binders args)
in (subst_comp _113_356 t)))

# 496 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _31_728 -> (match (_31_728) with
| (us, t) -> begin
(
# 497 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 498 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 499 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _31_735 -> (match (_31_735) with
| (x, _31_734) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 500 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 503 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _31_741 -> (match (_31_741) with
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
in (let _113_369 = (subst s t)
in (us', _113_369)))))
end))

# 509 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 510 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _31_753 -> (match (_31_753) with
| (x, _31_752) -> begin
(let _113_375 = (let _113_374 = (FStar_Syntax_Syntax.bv_to_name x)
in ((n - i), _113_374))
in FStar_Syntax_Syntax.DB (_113_375))
end))))))




