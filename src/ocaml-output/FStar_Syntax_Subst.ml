
open Prims
# 56 "FStar.Syntax.Subst.fst"
let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _35_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _35_17 -> begin
t
end)
end
| _35_19 -> begin
t
end))

# 65 "FStar.Syntax.Subst.fst"
let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(
# 70 "FStar.Syntax.Subst.fst"
let t' = (let _124_8 = (c ())
in (force_delayed_thunk _124_8))
in (
# 70 "FStar.Syntax.Subst.fst"
let _35_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_32 -> begin
t
end)
end
| Some (t') -> begin
(
# 73 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 73 "FStar.Syntax.Subst.fst"
let _35_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_39 -> begin
t
end))

# 76 "FStar.Syntax.Subst.fst"
let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _35_46 -> begin
u
end)
end
| _35_48 -> begin
u
end))

# 88 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _124_15 = (FStar_All.pipe_right s (FStar_List.map (fun _35_53 -> (match (_35_53) with
| (b, _35_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _124_15 (FStar_String.concat ", "))))

# 91 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _124_23 = (let _124_22 = (let _124_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _124_21))
in (FStar_Syntax_Syntax.bv_to_name _124_22))
in Some (_124_23))
end
| _35_62 -> begin
None
end))))

# 95 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _124_29 = (FStar_Syntax_Syntax.bv_to_tm (
# 96 "FStar.Syntax.Subst.fst"
let _35_70 = a
in {FStar_Syntax_Syntax.ppname = _35_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_70.FStar_Syntax_Syntax.sort}))
in Some (_124_29))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _35_77 -> begin
None
end))))

# 99 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_3 -> (match (_35_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _35_86 -> begin
None
end))))

# 102 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _35_95 -> begin
None
end))))

# 109 "FStar.Syntax.Subst.fst"
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

# 116 "FStar.Syntax.Subst.fst"
let map_some_curry = (fun f x _35_5 -> (match (_35_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 120 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _124_67 = (apply_until_some f s)
in (FStar_All.pipe_right _124_67 (map_some_curry g t))))

# 124 "FStar.Syntax.Subst.fst"
let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (
# 125 "FStar.Syntax.Subst.fst"
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
(let _124_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_124_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _124_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_124_73))
end)))

# 140 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_139 -> begin
(
# 144 "FStar.Syntax.Subst.fst"
let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t', (FStar_List.append s' s)))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_35_158), _35_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _124_89 = (let _124_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_124_88))
in (FStar_Syntax_Syntax.mk _124_89 None t0.FStar_Syntax_Syntax.pos))
end
| _35_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _124_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_124_94))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_184 -> begin
(
# 180 "FStar.Syntax.Subst.fst"
let _35_185 = t
in (let _124_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _124_100 = (FStar_List.map (fun _35_189 -> (match (_35_189) with
| (t, imp) -> begin
(let _124_98 = (subst' s t)
in (_124_98, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _124_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _124_101; FStar_Syntax_Syntax.effect_args = _124_100; FStar_Syntax_Syntax.flags = _124_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _35_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _124_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _124_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _124_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _124_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _124_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _124_106))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))

# 195 "FStar.Syntax.Subst.fst"
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
| FStar_Syntax_Syntax.NT (_35_224) -> begin
s
end))

# 201 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 202 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 203 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _35_233 -> (match (_35_233) with
| (x, imp) -> begin
(let _124_124 = (
# 203 "FStar.Syntax.Subst.fst"
let _35_234 = x
in (let _124_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_123}))
in (_124_124, imp))
end))

# 204 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _124_129 = (shift_subst' i s)
in (subst_binder' _124_129 b))
end))))

# 208 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _35_243 -> (match (_35_243) with
| (t, imp) -> begin
(let _124_132 = (subst' s t)
in (_124_132, imp))
end))

# 209 "FStar.Syntax.Subst.fst"
let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

# 210 "FStar.Syntax.Subst.fst"
let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (
# 211 "FStar.Syntax.Subst.fst"
let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let _35_261 = (aux n p)
in (match (_35_261) with
| (p, m) -> begin
(
# 218 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _124_145 = (aux n p)
in (Prims.fst _124_145))) ps)
in ((
# 219 "FStar.Syntax.Subst.fst"
let _35_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _35_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_272 _35_275 -> (match ((_35_272, _35_275)) with
| ((pats, n), (p, imp)) -> begin
(
# 223 "FStar.Syntax.Subst.fst"
let _35_278 = (aux n p)
in (match (_35_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_35_281) with
| (pats, n) -> begin
((
# 225 "FStar.Syntax.Subst.fst"
let _35_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_282.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 228 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 229 "FStar.Syntax.Subst.fst"
let x = (
# 229 "FStar.Syntax.Subst.fst"
let _35_287 = x
in (let _124_148 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_148}))
in ((
# 230 "FStar.Syntax.Subst.fst"
let _35_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 233 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 234 "FStar.Syntax.Subst.fst"
let x = (
# 234 "FStar.Syntax.Subst.fst"
let _35_295 = x
in (let _124_149 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_149}))
in ((
# 235 "FStar.Syntax.Subst.fst"
let _35_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 238 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 239 "FStar.Syntax.Subst.fst"
let x = (
# 239 "FStar.Syntax.Subst.fst"
let _35_305 = x
in (let _124_150 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_150}))
in (
# 240 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 241 "FStar.Syntax.Subst.fst"
let _35_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 244 "FStar.Syntax.Subst.fst"
let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _124_158 = (
# 247 "FStar.Syntax.Subst.fst"
let _35_316 = l
in (let _124_157 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_157; FStar_Syntax_Syntax.cflags = _35_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_318 -> (match (()) with
| () -> begin
(let _124_156 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _124_156))
end))}))
in Some (_124_158))
end))

# 250 "FStar.Syntax.Subst.fst"
let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_322) -> begin
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
# 266 "FStar.Syntax.Subst.fst"
let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _124_169 = (let _124_168 = (let _124_167 = (subst' s t0)
in (let _124_166 = (subst_args' s args)
in (_124_167, _124_166)))
in FStar_Syntax_Syntax.Tm_app (_124_168))
in (FStar_Syntax_Syntax.mk _124_169 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _124_174 = (let _124_173 = (let _124_172 = (subst' s t0)
in (let _124_171 = (let _124_170 = (subst' s t1)
in FStar_Util.Inl (_124_170))
in (_124_172, _124_171, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_173))
in (FStar_Syntax_Syntax.mk _124_174 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _124_179 = (let _124_178 = (let _124_177 = (subst' s t0)
in (let _124_176 = (let _124_175 = (subst_comp' s c)
in FStar_Util.Inr (_124_175))
in (_124_177, _124_176, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_178))
in (FStar_Syntax_Syntax.mk _124_179 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 275 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 276 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _124_184 = (let _124_183 = (let _124_182 = (subst_binders' s bs)
in (let _124_181 = (subst' s' body)
in (let _124_180 = (push_subst_lcomp s' lopt)
in (_124_182, _124_181, _124_180))))
in FStar_Syntax_Syntax.Tm_abs (_124_183))
in (FStar_Syntax_Syntax.mk _124_184 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 280 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _124_189 = (let _124_188 = (let _124_187 = (subst_binders' s bs)
in (let _124_186 = (let _124_185 = (shift_subst' n s)
in (subst_comp' _124_185 comp))
in (_124_187, _124_186)))
in FStar_Syntax_Syntax.Tm_arrow (_124_188))
in (FStar_Syntax_Syntax.mk _124_189 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 284 "FStar.Syntax.Subst.fst"
let x = (
# 284 "FStar.Syntax.Subst.fst"
let _35_380 = x
in (let _124_190 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_380.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_380.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_190}))
in (
# 285 "FStar.Syntax.Subst.fst"
let phi = (let _124_191 = (shift_subst' 1 s)
in (subst' _124_191 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 289 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 290 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_392 -> (match (_35_392) with
| (pat, wopt, branch) -> begin
(
# 291 "FStar.Syntax.Subst.fst"
let _35_395 = (subst_pat' s pat)
in (match (_35_395) with
| (pat, n) -> begin
(
# 292 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 293 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_193 = (subst' s w)
in Some (_124_193))
end)
in (
# 296 "FStar.Syntax.Subst.fst"
let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(
# 301 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length lbs)
in (
# 302 "FStar.Syntax.Subst.fst"
let sn = (shift_subst' n s)
in (
# 303 "FStar.Syntax.Subst.fst"
let body = (subst' sn body)
in (
# 304 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 305 "FStar.Syntax.Subst.fst"
let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (
# 306 "FStar.Syntax.Subst.fst"
let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (
# 309 "FStar.Syntax.Subst.fst"
let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((
# 310 "FStar.Syntax.Subst.fst"
let _35_417 = x
in {FStar_Syntax_Syntax.ppname = _35_417.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_417.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((
# 311 "FStar.Syntax.Subst.fst"
let _35_421 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 311 "FStar.Syntax.Subst.fst"
let _35_423 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_423.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_423.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_421.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_421.FStar_Syntax_Syntax.fv_qual}))
end)
in (
# 312 "FStar.Syntax.Subst.fst"
let _35_426 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_426.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_426.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _124_199 = (let _124_198 = (let _124_197 = (subst' s t0)
in (let _124_196 = (let _124_195 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_124_195))
in (_124_197, _124_196)))
in FStar_Syntax_Syntax.Tm_meta (_124_198))
in (FStar_Syntax_Syntax.mk _124_199 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _124_202 = (let _124_201 = (let _124_200 = (subst' s t)
in (_124_200, m))
in FStar_Syntax_Syntax.Tm_meta (_124_201))
in (FStar_Syntax_Syntax.mk _124_202 None t.FStar_Syntax_Syntax.pos))
end))

# 321 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 322 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 325 "FStar.Syntax.Subst.fst"
let t' = (let _124_205 = (push_subst s t)
in (compress _124_205))
in (
# 326 "FStar.Syntax.Subst.fst"
let _35_448 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_451 -> begin
(force_uvar t)
end)))

# 332 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 333 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 334 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _124_217 = (FStar_List.fold_right (fun _35_460 _35_463 -> (match ((_35_460, _35_463)) with
| ((x, _35_459), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _124_217 Prims.fst)))

# 336 "FStar.Syntax.Subst.fst"
let open_binders' = (fun bs -> (
# 337 "FStar.Syntax.Subst.fst"
let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(
# 340 "FStar.Syntax.Subst.fst"
let x' = (
# 340 "FStar.Syntax.Subst.fst"
let _35_474 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_223 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_474.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_474.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_223}))
in (
# 341 "FStar.Syntax.Subst.fst"
let o = (let _124_224 = (shift_subst 1 o)
in (FStar_Syntax_Syntax.DB ((0, x')))::_124_224)
in (
# 342 "FStar.Syntax.Subst.fst"
let _35_480 = (aux bs' o)
in (match (_35_480) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 345 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _124_227 = (open_binders' bs)
in (Prims.fst _124_227)))

# 346 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 347 "FStar.Syntax.Subst.fst"
let _35_486 = (open_binders' bs)
in (match (_35_486) with
| (bs', opening) -> begin
(let _124_232 = (subst opening t)
in (bs', _124_232, opening))
end)))

# 349 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 350 "FStar.Syntax.Subst.fst"
let _35_493 = (open_term' bs t)
in (match (_35_493) with
| (b, t, _35_492) -> begin
(b, t)
end)))

# 352 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 353 "FStar.Syntax.Subst.fst"
let _35_498 = (open_binders' bs)
in (match (_35_498) with
| (bs', opening) -> begin
(let _124_241 = (subst_comp opening t)
in (bs', _124_241))
end)))

# 357 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (
# 358 "FStar.Syntax.Subst.fst"
let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_505) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_508) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 365 "FStar.Syntax.Subst.fst"
let _35_514 = p
in (let _124_254 = (let _124_253 = (let _124_252 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_518 -> (match (_35_518) with
| (p, b) -> begin
(let _124_251 = (aux_disj sub renaming p)
in (_124_251, b))
end))))
in (fv, _124_252))
in FStar_Syntax_Syntax.Pat_cons (_124_253))
in {FStar_Syntax_Syntax.v = _124_254; FStar_Syntax_Syntax.ty = _35_514.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_514.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 369 "FStar.Syntax.Subst.fst"
let yopt = (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_526 -> begin
None
end)))
in (
# 372 "FStar.Syntax.Subst.fst"
let y = (match (yopt) with
| None -> begin
(
# 373 "FStar.Syntax.Subst.fst"
let _35_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_256}))
end
| Some (y) -> begin
y
end)
in (
# 375 "FStar.Syntax.Subst.fst"
let _35_534 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_534.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_534.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 378 "FStar.Syntax.Subst.fst"
let x' = (
# 378 "FStar.Syntax.Subst.fst"
let _35_538 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_257 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_538.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_538.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_257}))
in (
# 379 "FStar.Syntax.Subst.fst"
let _35_541 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_541.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_541.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 382 "FStar.Syntax.Subst.fst"
let x = (
# 382 "FStar.Syntax.Subst.fst"
let _35_547 = x
in (let _124_258 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_547.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_547.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_258}))
in (
# 383 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in (
# 384 "FStar.Syntax.Subst.fst"
let _35_551 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_551.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_551.FStar_Syntax_Syntax.p})))
end))
in (
# 386 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_560) -> begin
(p, sub, renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 392 "FStar.Syntax.Subst.fst"
let _35_569 = (aux sub renaming p)
in (match (_35_569) with
| (p, sub, renaming) -> begin
(
# 393 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((
# 394 "FStar.Syntax.Subst.fst"
let _35_571 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_571.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_571.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 397 "FStar.Syntax.Subst.fst"
let _35_591 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_580 _35_583 -> (match ((_35_580, _35_583)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(
# 398 "FStar.Syntax.Subst.fst"
let _35_587 = (aux sub renaming p)
in (match (_35_587) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, renaming)))
in (match (_35_591) with
| (pats, sub, renaming) -> begin
((
# 400 "FStar.Syntax.Subst.fst"
let _35_592 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_592.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_592.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 403 "FStar.Syntax.Subst.fst"
let x' = (
# 403 "FStar.Syntax.Subst.fst"
let _35_596 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_267 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_596.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_596.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_267}))
in (
# 404 "FStar.Syntax.Subst.fst"
let sub = (let _124_268 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_124_268)
in ((
# 405 "FStar.Syntax.Subst.fst"
let _35_600 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_600.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_600.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 408 "FStar.Syntax.Subst.fst"
let x' = (
# 408 "FStar.Syntax.Subst.fst"
let _35_604 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_269 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_604.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_604.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_269}))
in (
# 409 "FStar.Syntax.Subst.fst"
let sub = (let _124_270 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_124_270)
in ((
# 410 "FStar.Syntax.Subst.fst"
let _35_608 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_608.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_608.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 413 "FStar.Syntax.Subst.fst"
let x = (
# 413 "FStar.Syntax.Subst.fst"
let _35_614 = x
in (let _124_271 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_614.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_614.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_271}))
in (
# 414 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 415 "FStar.Syntax.Subst.fst"
let _35_618 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_618.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_618.FStar_Syntax_Syntax.p}), sub, renaming)))
end))
in (
# 417 "FStar.Syntax.Subst.fst"
let _35_624 = (aux [] [] p)
in (match (_35_624) with
| (p, sub, _35_623) -> begin
(p, sub)
end)))))

# 420 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_628 -> (match (_35_628) with
| (p, wopt, e) -> begin
(
# 421 "FStar.Syntax.Subst.fst"
let _35_631 = (open_pat p)
in (match (_35_631) with
| (p, opening) -> begin
(
# 422 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_274 = (subst opening w)
in Some (_124_274))
end)
in (
# 425 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 428 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _124_279 = (closing_subst bs)
in (subst _124_279 t)))

# 429 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _124_284 = (closing_subst bs)
in (subst_comp _124_284 c)))

# 430 "FStar.Syntax.Subst.fst"
let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (
# 431 "FStar.Syntax.Subst.fst"
let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(
# 434 "FStar.Syntax.Subst.fst"
let x = (
# 434 "FStar.Syntax.Subst.fst"
let _35_651 = x
in (let _124_291 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_651.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_651.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_291}))
in (
# 435 "FStar.Syntax.Subst.fst"
let s' = (let _124_292 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_124_292)
in (let _124_293 = (aux s' tl)
in ((x, imp))::_124_293)))
end))
in (aux [] bs)))

# 439 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 440 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 441 "FStar.Syntax.Subst.fst"
let _35_658 = lc
in (let _124_300 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_658.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_300; FStar_Syntax_Syntax.cflags = _35_658.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_660 -> (match (()) with
| () -> begin
(let _124_299 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _124_299))
end))}))))

# 444 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 445 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_668) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 451 "FStar.Syntax.Subst.fst"
let _35_676 = (aux sub p)
in (match (_35_676) with
| (p, sub) -> begin
(
# 452 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _124_308 = (aux sub p)
in (Prims.fst _124_308))) ps)
in ((
# 453 "FStar.Syntax.Subst.fst"
let _35_679 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_679.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_679.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 456 "FStar.Syntax.Subst.fst"
let _35_696 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_687 _35_690 -> (match ((_35_687, _35_690)) with
| ((pats, sub), (p, imp)) -> begin
(
# 457 "FStar.Syntax.Subst.fst"
let _35_693 = (aux sub p)
in (match (_35_693) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_696) with
| (pats, sub) -> begin
((
# 459 "FStar.Syntax.Subst.fst"
let _35_697 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_697.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_697.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 462 "FStar.Syntax.Subst.fst"
let x = (
# 462 "FStar.Syntax.Subst.fst"
let _35_701 = x
in (let _124_311 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_701.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_701.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_311}))
in (
# 463 "FStar.Syntax.Subst.fst"
let sub = (let _124_312 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_124_312)
in ((
# 464 "FStar.Syntax.Subst.fst"
let _35_705 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_705.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_705.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 467 "FStar.Syntax.Subst.fst"
let x = (
# 467 "FStar.Syntax.Subst.fst"
let _35_709 = x
in (let _124_313 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_709.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_709.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_313}))
in (
# 468 "FStar.Syntax.Subst.fst"
let sub = (let _124_314 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_124_314)
in ((
# 469 "FStar.Syntax.Subst.fst"
let _35_713 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_713.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_713.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 472 "FStar.Syntax.Subst.fst"
let x = (
# 472 "FStar.Syntax.Subst.fst"
let _35_719 = x
in (let _124_315 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_719.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_719.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_315}))
in (
# 473 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 474 "FStar.Syntax.Subst.fst"
let _35_723 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_723.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_723.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 477 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_728 -> (match (_35_728) with
| (p, wopt, e) -> begin
(
# 478 "FStar.Syntax.Subst.fst"
let _35_731 = (close_pat p)
in (match (_35_731) with
| (p, closing) -> begin
(
# 479 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_318 = (subst closing w)
in Some (_124_318))
end)
in (
# 482 "FStar.Syntax.Subst.fst"
let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 485 "FStar.Syntax.Subst.fst"
let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (
# 486 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 487 "FStar.Syntax.Subst.fst"
let _35_744 = (let _124_323 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 488 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _124_323 FStar_List.unzip))
in (match (_35_744) with
| (s, us') -> begin
(s, us')
end))))

# 492 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 493 "FStar.Syntax.Subst.fst"
let _35_749 = (univ_var_opening us)
in (match (_35_749) with
| (s, us') -> begin
(
# 494 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 497 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 498 "FStar.Syntax.Subst.fst"
let _35_755 = (univ_var_opening us)
in (match (_35_755) with
| (s, us') -> begin
(let _124_332 = (subst_comp s c)
in (us', _124_332))
end)))

# 501 "FStar.Syntax.Subst.fst"
let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (
# 502 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 503 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 506 "FStar.Syntax.Subst.fst"
let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (
# 507 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 508 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 511 "FStar.Syntax.Subst.fst"
let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 528 "FStar.Syntax.Subst.fst"
let _35_781 = (FStar_List.fold_right (fun lb _35_774 -> (match (_35_774) with
| (i, lbs, out) -> begin
(
# 530 "FStar.Syntax.Subst.fst"
let x = (let _124_351 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _124_351))
in ((i + 1), ((
# 531 "FStar.Syntax.Subst.fst"
let _35_776 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_776.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_776.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_776.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_776.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.DB ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_35_781) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(
# 533 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 534 "FStar.Syntax.Subst.fst"
let _35_793 = (FStar_List.fold_right (fun u _35_787 -> (match (_35_787) with
| (i, us, out) -> begin
(
# 536 "FStar.Syntax.Subst.fst"
let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UN ((i, FStar_Syntax_Syntax.U_name (u))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_35_793) with
| (_35_790, us, u_let_rec_opening) -> begin
(
# 539 "FStar.Syntax.Subst.fst"
let _35_794 = lb
in (let _124_355 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_794.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_794.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_794.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_355}))
end)))))
in (
# 541 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_opening t)
in (lbs, t)))
end))
end)

# 544 "FStar.Syntax.Subst.fst"
let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 546 "FStar.Syntax.Subst.fst"
let _35_806 = (FStar_List.fold_right (fun lb _35_803 -> (match (_35_803) with
| (i, out) -> begin
(let _124_365 = (let _124_364 = (let _124_363 = (let _124_362 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_124_362, i))
in FStar_Syntax_Syntax.NM (_124_363))
in (_124_364)::out)
in ((i + 1), _124_365))
end)) lbs (0, []))
in (match (_35_806) with
| (n_let_recs, let_rec_closing) -> begin
(
# 548 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 549 "FStar.Syntax.Subst.fst"
let _35_815 = (FStar_List.fold_right (fun u _35_811 -> (match (_35_811) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UD ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_35_815) with
| (_35_813, u_let_rec_closing) -> begin
(
# 550 "FStar.Syntax.Subst.fst"
let _35_816 = lb
in (let _124_369 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_816.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_816.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_816.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_816.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_369}))
end)))))
in (
# 551 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_closing t)
in (lbs, t)))
end))
end)

# 554 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_823 -> (match (_35_823) with
| (us, t) -> begin
(
# 555 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 556 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 557 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _35_830 -> (match (_35_830) with
| (x, _35_829) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 558 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 561 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_836 -> (match (_35_836) with
| (us', t) -> begin
(
# 562 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 563 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us')
in (
# 564 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _124_382 = (subst s t)
in (us', _124_382)))))
end))

# 567 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 568 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_848 -> (match (_35_848) with
| (x, _35_847) -> begin
FStar_Syntax_Syntax.DB (((n - i), x))
end))))))




