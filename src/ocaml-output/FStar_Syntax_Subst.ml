
open Prims
# 49 "FStar.Syntax.Subst.fst"
let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _25_11) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _25_17 -> begin
t
end)
end
| _25_19 -> begin
t
end))

# 63 "FStar.Syntax.Subst.fst"
let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(
# 70 "FStar.Syntax.Subst.fst"
let t' = (let _104_8 = (c ())
in (force_delayed_thunk _104_8))
in (
# 70 "FStar.Syntax.Subst.fst"
let _25_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _25_32 -> begin
t
end)
end
| Some (t') -> begin
(
# 73 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 73 "FStar.Syntax.Subst.fst"
let _25_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _25_39 -> begin
t
end))

# 74 "FStar.Syntax.Subst.fst"
let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _25_46 -> begin
u
end)
end
| _25_48 -> begin
u
end))

# 82 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _104_15 = (FStar_All.pipe_right s (FStar_List.map (fun _25_53 -> (match (_25_53) with
| (b, _25_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _104_15 (FStar_String.concat ", "))))

# 88 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _25_1 -> (match (_25_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _104_23 = (let _104_22 = (let _104_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _104_21))
in (FStar_Syntax_Syntax.bv_to_name _104_22))
in Some (_104_23))
end
| _25_62 -> begin
None
end))))

# 94 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _25_2 -> (match (_25_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _104_29 = (FStar_Syntax_Syntax.bv_to_tm (
# 96 "FStar.Syntax.Subst.fst"
let _25_70 = a
in {FStar_Syntax_Syntax.ppname = _25_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _25_70.FStar_Syntax_Syntax.sort}))
in Some (_104_29))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _25_77 -> begin
None
end))))

# 98 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _25_3 -> (match (_25_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _25_86 -> begin
None
end))))

# 101 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _25_4 -> (match (_25_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _25_95 -> begin
None
end))))

# 104 "FStar.Syntax.Subst.fst"
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

# 114 "FStar.Syntax.Subst.fst"
let map_some_curry = (fun f x _25_5 -> (match (_25_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 118 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _104_67 = (apply_until_some f s)
in (FStar_All.pipe_right _104_67 (map_some_curry g t))))

# 122 "FStar.Syntax.Subst.fst"
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
(let _104_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_104_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _104_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_104_73))
end)))

# 137 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _25_139 -> begin
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
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_25_158), _25_161) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _104_89 = (let _104_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_104_88))
in (FStar_Syntax_Syntax.mk _104_89 None t0.FStar_Syntax_Syntax.pos))
end
| _25_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _25_6 -> (match (_25_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _104_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_104_94))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _25_184 -> begin
(
# 180 "FStar.Syntax.Subst.fst"
let _25_185 = t
in (let _104_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _104_100 = (FStar_List.map (fun _25_189 -> (match (_25_189) with
| (t, imp) -> begin
(let _104_98 = (subst' s t)
in (_104_98, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _104_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _25_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _104_101; FStar_Syntax_Syntax.effect_args = _104_100; FStar_Syntax_Syntax.flags = _104_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _25_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _104_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _104_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _104_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _104_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _104_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _104_106))
end)
end))
and compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_elt Prims.list Prims.list = (fun s1 s2 -> (FStar_List.append s1 s2))

# 193 "FStar.Syntax.Subst.fst"
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
| FStar_Syntax_Syntax.NT (_25_224) -> begin
s
end))

# 200 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 201 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 202 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _25_233 -> (match (_25_233) with
| (x, imp) -> begin
(let _104_124 = (
# 203 "FStar.Syntax.Subst.fst"
let _25_234 = x
in (let _104_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_123}))
in (_104_124, imp))
end))

# 203 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _104_129 = (shift_subst' i s)
in (subst_binder' _104_129 b))
end))))

# 207 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _25_243 -> (match (_25_243) with
| (t, imp) -> begin
(let _104_132 = (subst' s t)
in (_104_132, imp))
end))

# 208 "FStar.Syntax.Subst.fst"
let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))

# 209 "FStar.Syntax.Subst.fst"
let subst_pat' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (
# 211 "FStar.Syntax.Subst.fst"
let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_25_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let _25_261 = (aux n p)
in (match (_25_261) with
| (p, m) -> begin
(
# 218 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _104_145 = (aux n p)
in (Prims.fst _104_145))) ps)
in ((
# 219 "FStar.Syntax.Subst.fst"
let _25_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _25_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _25_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _25_272 _25_275 -> (match ((_25_272, _25_275)) with
| ((pats, n), (p, imp)) -> begin
(
# 223 "FStar.Syntax.Subst.fst"
let _25_278 = (aux n p)
in (match (_25_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_25_281) with
| (pats, n) -> begin
((
# 225 "FStar.Syntax.Subst.fst"
let _25_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _25_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_282.FStar_Syntax_Syntax.p}), n)
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
let _25_287 = x
in (let _104_148 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_148}))
in ((
# 230 "FStar.Syntax.Subst.fst"
let _25_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _25_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 233 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 234 "FStar.Syntax.Subst.fst"
let x = (
# 234 "FStar.Syntax.Subst.fst"
let _25_295 = x
in (let _104_149 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_149}))
in ((
# 235 "FStar.Syntax.Subst.fst"
let _25_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _25_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 238 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 239 "FStar.Syntax.Subst.fst"
let x = (
# 239 "FStar.Syntax.Subst.fst"
let _25_305 = x
in (let _104_150 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_150}))
in (
# 240 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 241 "FStar.Syntax.Subst.fst"
let _25_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _25_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 242 "FStar.Syntax.Subst.fst"
let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _104_158 = (
# 247 "FStar.Syntax.Subst.fst"
let _25_316 = l
in (let _104_157 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _25_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _104_157; FStar_Syntax_Syntax.cflags = _25_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _25_318 -> (match (()) with
| () -> begin
(let _104_156 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _104_156))
end))}))
in Some (_104_158))
end))

# 248 "FStar.Syntax.Subst.fst"
let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_25_322) -> begin
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
(let _104_169 = (let _104_168 = (let _104_167 = (subst' s t0)
in (let _104_166 = (subst_args' s args)
in (_104_167, _104_166)))
in FStar_Syntax_Syntax.Tm_app (_104_168))
in (FStar_Syntax_Syntax.mk _104_169 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _104_174 = (let _104_173 = (let _104_172 = (subst' s t0)
in (let _104_171 = (let _104_170 = (subst' s t1)
in FStar_Util.Inl (_104_170))
in (_104_172, _104_171, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_104_173))
in (FStar_Syntax_Syntax.mk _104_174 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _104_179 = (let _104_178 = (let _104_177 = (subst' s t0)
in (let _104_176 = (let _104_175 = (subst_comp' s c)
in FStar_Util.Inr (_104_175))
in (_104_177, _104_176, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_104_178))
in (FStar_Syntax_Syntax.mk _104_179 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 275 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 276 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _104_184 = (let _104_183 = (let _104_182 = (subst_binders' s bs)
in (let _104_181 = (subst' s' body)
in (let _104_180 = (push_subst_lcomp s' lopt)
in (_104_182, _104_181, _104_180))))
in FStar_Syntax_Syntax.Tm_abs (_104_183))
in (FStar_Syntax_Syntax.mk _104_184 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 280 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _104_189 = (let _104_188 = (let _104_187 = (subst_binders' s bs)
in (let _104_186 = (let _104_185 = (shift_subst' n s)
in (subst_comp' _104_185 comp))
in (_104_187, _104_186)))
in FStar_Syntax_Syntax.Tm_arrow (_104_188))
in (FStar_Syntax_Syntax.mk _104_189 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 284 "FStar.Syntax.Subst.fst"
let x = (
# 284 "FStar.Syntax.Subst.fst"
let _25_380 = x
in (let _104_190 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_380.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_380.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_190}))
in (
# 285 "FStar.Syntax.Subst.fst"
let phi = (let _104_191 = (shift_subst' 1 s)
in (subst' _104_191 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 289 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 290 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _25_392 -> (match (_25_392) with
| (pat, wopt, branch) -> begin
(
# 291 "FStar.Syntax.Subst.fst"
let _25_395 = (subst_pat' s pat)
in (match (_25_395) with
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
(let _104_193 = (subst' s w)
in Some (_104_193))
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
let _25_417 = x
in {FStar_Syntax_Syntax.ppname = _25_417.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_417.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((
# 311 "FStar.Syntax.Subst.fst"
let _25_421 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 311 "FStar.Syntax.Subst.fst"
let _25_423 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _25_423.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _25_423.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _25_421.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _25_421.FStar_Syntax_Syntax.fv_qual}))
end)
in (
# 312 "FStar.Syntax.Subst.fst"
let _25_426 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _25_426.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _25_426.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _104_199 = (let _104_198 = (let _104_197 = (subst' s t0)
in (let _104_196 = (let _104_195 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_104_195))
in (_104_197, _104_196)))
in FStar_Syntax_Syntax.Tm_meta (_104_198))
in (FStar_Syntax_Syntax.mk _104_199 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _104_202 = (let _104_201 = (let _104_200 = (subst' s t)
in (_104_200, m))
in FStar_Syntax_Syntax.Tm_meta (_104_201))
in (FStar_Syntax_Syntax.mk _104_202 None t.FStar_Syntax_Syntax.pos))
end))

# 319 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 322 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 325 "FStar.Syntax.Subst.fst"
let t' = (let _104_205 = (push_subst s t)
in (compress _104_205))
in (
# 326 "FStar.Syntax.Subst.fst"
let _25_448 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _25_451 -> begin
(force_uvar t)
end)))

# 329 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 332 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 333 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _104_217 = (FStar_List.fold_right (fun _25_460 _25_463 -> (match ((_25_460, _25_463)) with
| ((x, _25_459), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _104_217 Prims.fst)))

# 335 "FStar.Syntax.Subst.fst"
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
let _25_474 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _104_223 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_474.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_474.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_223}))
in (
# 341 "FStar.Syntax.Subst.fst"
let o = (let _104_224 = (shift_subst 1 o)
in (FStar_Syntax_Syntax.DB ((0, x')))::_104_224)
in (
# 342 "FStar.Syntax.Subst.fst"
let _25_480 = (aux bs' o)
in (match (_25_480) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 344 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _104_227 = (open_binders' bs)
in (Prims.fst _104_227)))

# 345 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 347 "FStar.Syntax.Subst.fst"
let _25_486 = (open_binders' bs)
in (match (_25_486) with
| (bs', opening) -> begin
(let _104_232 = (subst opening t)
in (bs', _104_232, opening))
end)))

# 348 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 350 "FStar.Syntax.Subst.fst"
let _25_493 = (open_term' bs t)
in (match (_25_493) with
| (b, t, _25_492) -> begin
(b, t)
end)))

# 351 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 353 "FStar.Syntax.Subst.fst"
let _25_498 = (open_binders' bs)
in (match (_25_498) with
| (bs', opening) -> begin
(let _104_241 = (subst_comp opening t)
in (bs', _104_241))
end)))

# 354 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (
# 358 "FStar.Syntax.Subst.fst"
let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_25_505) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_25_508) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 365 "FStar.Syntax.Subst.fst"
let _25_514 = p
in (let _104_254 = (let _104_253 = (let _104_252 = (FStar_All.pipe_right pats (FStar_List.map (fun _25_518 -> (match (_25_518) with
| (p, b) -> begin
(let _104_251 = (aux_disj sub renaming p)
in (_104_251, b))
end))))
in (fv, _104_252))
in FStar_Syntax_Syntax.Pat_cons (_104_253))
in {FStar_Syntax_Syntax.v = _104_254; FStar_Syntax_Syntax.ty = _25_514.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_514.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 369 "FStar.Syntax.Subst.fst"
let yopt = (FStar_Util.find_map renaming (fun _25_7 -> (match (_25_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _25_526 -> begin
None
end)))
in (
# 372 "FStar.Syntax.Subst.fst"
let y = (match (yopt) with
| None -> begin
(
# 373 "FStar.Syntax.Subst.fst"
let _25_529 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _104_256 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_256}))
end
| Some (y) -> begin
y
end)
in (
# 375 "FStar.Syntax.Subst.fst"
let _25_534 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _25_534.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_534.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 378 "FStar.Syntax.Subst.fst"
let x' = (
# 378 "FStar.Syntax.Subst.fst"
let _25_538 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _104_257 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_538.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_538.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_257}))
in (
# 379 "FStar.Syntax.Subst.fst"
let _25_541 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _25_541.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_541.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 382 "FStar.Syntax.Subst.fst"
let x = (
# 382 "FStar.Syntax.Subst.fst"
let _25_547 = x
in (let _104_258 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_547.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_547.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_258}))
in (
# 383 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in (
# 384 "FStar.Syntax.Subst.fst"
let _25_551 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _25_551.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_551.FStar_Syntax_Syntax.p})))
end))
in (
# 386 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_25_560) -> begin
(p, sub, renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 392 "FStar.Syntax.Subst.fst"
let _25_569 = (aux sub renaming p)
in (match (_25_569) with
| (p, sub, renaming) -> begin
(
# 393 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((
# 394 "FStar.Syntax.Subst.fst"
let _25_571 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _25_571.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_571.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 397 "FStar.Syntax.Subst.fst"
let _25_591 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _25_580 _25_583 -> (match ((_25_580, _25_583)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(
# 398 "FStar.Syntax.Subst.fst"
let _25_587 = (aux sub renaming p)
in (match (_25_587) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, renaming)))
in (match (_25_591) with
| (pats, sub, renaming) -> begin
((
# 400 "FStar.Syntax.Subst.fst"
let _25_592 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _25_592.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_592.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 403 "FStar.Syntax.Subst.fst"
let x' = (
# 403 "FStar.Syntax.Subst.fst"
let _25_596 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _104_267 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_596.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_596.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_267}))
in (
# 404 "FStar.Syntax.Subst.fst"
let sub = (let _104_268 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_104_268)
in ((
# 405 "FStar.Syntax.Subst.fst"
let _25_600 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _25_600.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_600.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 408 "FStar.Syntax.Subst.fst"
let x' = (
# 408 "FStar.Syntax.Subst.fst"
let _25_604 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _104_269 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_604.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_604.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_269}))
in (
# 409 "FStar.Syntax.Subst.fst"
let sub = (let _104_270 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_104_270)
in ((
# 410 "FStar.Syntax.Subst.fst"
let _25_608 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _25_608.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_608.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 413 "FStar.Syntax.Subst.fst"
let x = (
# 413 "FStar.Syntax.Subst.fst"
let _25_614 = x
in (let _104_271 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_614.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_614.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_271}))
in (
# 414 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 415 "FStar.Syntax.Subst.fst"
let _25_618 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _25_618.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_618.FStar_Syntax_Syntax.p}), sub, renaming)))
end))
in (
# 417 "FStar.Syntax.Subst.fst"
let _25_624 = (aux [] [] p)
in (match (_25_624) with
| (p, sub, _25_623) -> begin
(p, sub)
end)))))

# 418 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _25_628 -> (match (_25_628) with
| (p, wopt, e) -> begin
(
# 421 "FStar.Syntax.Subst.fst"
let _25_631 = (open_pat p)
in (match (_25_631) with
| (p, opening) -> begin
(
# 422 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _104_274 = (subst opening w)
in Some (_104_274))
end)
in (
# 425 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 426 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _104_279 = (closing_subst bs)
in (subst _104_279 t)))

# 428 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _104_284 = (closing_subst bs)
in (subst_comp _104_284 c)))

# 429 "FStar.Syntax.Subst.fst"
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
let _25_651 = x
in (let _104_291 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_651.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_651.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_291}))
in (
# 435 "FStar.Syntax.Subst.fst"
let s' = (let _104_292 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_104_292)
in (let _104_293 = (aux s' tl)
in ((x, imp))::_104_293)))
end))
in (aux [] bs)))

# 437 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 440 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 441 "FStar.Syntax.Subst.fst"
let _25_658 = lc
in (let _104_300 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _25_658.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _104_300; FStar_Syntax_Syntax.cflags = _25_658.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _25_660 -> (match (()) with
| () -> begin
(let _104_299 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _104_299))
end))}))))

# 442 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 445 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_25_668) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 451 "FStar.Syntax.Subst.fst"
let _25_676 = (aux sub p)
in (match (_25_676) with
| (p, sub) -> begin
(
# 452 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _104_308 = (aux sub p)
in (Prims.fst _104_308))) ps)
in ((
# 453 "FStar.Syntax.Subst.fst"
let _25_679 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _25_679.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_679.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 456 "FStar.Syntax.Subst.fst"
let _25_696 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _25_687 _25_690 -> (match ((_25_687, _25_690)) with
| ((pats, sub), (p, imp)) -> begin
(
# 457 "FStar.Syntax.Subst.fst"
let _25_693 = (aux sub p)
in (match (_25_693) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_25_696) with
| (pats, sub) -> begin
((
# 459 "FStar.Syntax.Subst.fst"
let _25_697 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _25_697.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_697.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 462 "FStar.Syntax.Subst.fst"
let x = (
# 462 "FStar.Syntax.Subst.fst"
let _25_701 = x
in (let _104_311 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_701.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_701.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_311}))
in (
# 463 "FStar.Syntax.Subst.fst"
let sub = (let _104_312 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_104_312)
in ((
# 464 "FStar.Syntax.Subst.fst"
let _25_705 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _25_705.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_705.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 467 "FStar.Syntax.Subst.fst"
let x = (
# 467 "FStar.Syntax.Subst.fst"
let _25_709 = x
in (let _104_313 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_709.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_709.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_313}))
in (
# 468 "FStar.Syntax.Subst.fst"
let sub = (let _104_314 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_104_314)
in ((
# 469 "FStar.Syntax.Subst.fst"
let _25_713 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _25_713.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_713.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 472 "FStar.Syntax.Subst.fst"
let x = (
# 472 "FStar.Syntax.Subst.fst"
let _25_719 = x
in (let _104_315 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _25_719.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _25_719.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _104_315}))
in (
# 473 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 474 "FStar.Syntax.Subst.fst"
let _25_723 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _25_723.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _25_723.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 475 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _25_728 -> (match (_25_728) with
| (p, wopt, e) -> begin
(
# 478 "FStar.Syntax.Subst.fst"
let _25_731 = (close_pat p)
in (match (_25_731) with
| (p, closing) -> begin
(
# 479 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _104_318 = (subst closing w)
in Some (_104_318))
end)
in (
# 482 "FStar.Syntax.Subst.fst"
let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 483 "FStar.Syntax.Subst.fst"
let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (
# 486 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 487 "FStar.Syntax.Subst.fst"
let _25_744 = (let _104_323 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 488 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _104_323 FStar_List.unzip))
in (match (_25_744) with
| (s, us') -> begin
(s, us')
end))))

# 490 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 493 "FStar.Syntax.Subst.fst"
let _25_749 = (univ_var_opening us)
in (match (_25_749) with
| (s, us') -> begin
(
# 494 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 495 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 498 "FStar.Syntax.Subst.fst"
let _25_755 = (univ_var_opening us)
in (match (_25_755) with
| (s, us') -> begin
(let _104_332 = (subst_comp s c)
in (us', _104_332))
end)))

# 499 "FStar.Syntax.Subst.fst"
let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (
# 502 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 503 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 504 "FStar.Syntax.Subst.fst"
let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (
# 507 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 508 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 509 "FStar.Syntax.Subst.fst"
let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 528 "FStar.Syntax.Subst.fst"
let _25_781 = (FStar_List.fold_right (fun lb _25_774 -> (match (_25_774) with
| (i, lbs, out) -> begin
(
# 530 "FStar.Syntax.Subst.fst"
let x = (let _104_351 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _104_351))
in ((i + 1), ((
# 531 "FStar.Syntax.Subst.fst"
let _25_776 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _25_776.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _25_776.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _25_776.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _25_776.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.DB ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_25_781) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(
# 533 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 534 "FStar.Syntax.Subst.fst"
let _25_793 = (FStar_List.fold_right (fun u _25_787 -> (match (_25_787) with
| (i, us, out) -> begin
(
# 536 "FStar.Syntax.Subst.fst"
let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UN ((i, FStar_Syntax_Syntax.U_name (u))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_25_793) with
| (_25_790, us, u_let_rec_opening) -> begin
(
# 539 "FStar.Syntax.Subst.fst"
let _25_794 = lb
in (let _104_355 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _25_794.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _25_794.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _25_794.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _104_355}))
end)))))
in (
# 541 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_opening t)
in (lbs, t)))
end))
end)

# 542 "FStar.Syntax.Subst.fst"
let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 546 "FStar.Syntax.Subst.fst"
let _25_806 = (FStar_List.fold_right (fun lb _25_803 -> (match (_25_803) with
| (i, out) -> begin
(let _104_365 = (let _104_364 = (let _104_363 = (let _104_362 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_104_362, i))
in FStar_Syntax_Syntax.NM (_104_363))
in (_104_364)::out)
in ((i + 1), _104_365))
end)) lbs (0, []))
in (match (_25_806) with
| (n_let_recs, let_rec_closing) -> begin
(
# 548 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 549 "FStar.Syntax.Subst.fst"
let _25_815 = (FStar_List.fold_right (fun u _25_811 -> (match (_25_811) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UD ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_25_815) with
| (_25_813, u_let_rec_closing) -> begin
(
# 550 "FStar.Syntax.Subst.fst"
let _25_816 = lb
in (let _104_369 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _25_816.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _25_816.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _25_816.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _25_816.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _104_369}))
end)))))
in (
# 551 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_closing t)
in (lbs, t)))
end))
end)

# 552 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _25_823 -> (match (_25_823) with
| (us, t) -> begin
(
# 555 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 556 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 557 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _25_830 -> (match (_25_830) with
| (x, _25_829) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 558 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 559 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _25_836 -> (match (_25_836) with
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
in (let _104_382 = (subst s t)
in (us', _104_382)))))
end))

# 565 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 568 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _25_848 -> (match (_25_848) with
| (x, _25_847) -> begin
FStar_Syntax_Syntax.DB (((n - i), x))
end))))))




