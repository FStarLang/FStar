
open Prims
# 56 "FStar.Syntax.Subst.fst"
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

# 65 "FStar.Syntax.Subst.fst"
let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(
# 70 "FStar.Syntax.Subst.fst"
let t' = (let _115_8 = (c ())
in (force_delayed_thunk _115_8))
in (
# 70 "FStar.Syntax.Subst.fst"
let _31_29 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _31_32 -> begin
t
end)
end
| Some (t') -> begin
(
# 73 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 73 "FStar.Syntax.Subst.fst"
let _31_36 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _31_39 -> begin
t
end))

# 76 "FStar.Syntax.Subst.fst"
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

# 88 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _115_15 = (FStar_All.pipe_right s (FStar_List.map (fun _31_53 -> (match (_31_53) with
| (b, _31_52) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _115_15 (FStar_String.concat ", "))))

# 91 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _31_1 -> (match (_31_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _115_23 = (let _115_22 = (let _115_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _115_21))
in (FStar_Syntax_Syntax.bv_to_name _115_22))
in Some (_115_23))
end
| _31_62 -> begin
None
end))))

# 95 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _31_2 -> (match (_31_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _115_29 = (FStar_Syntax_Syntax.bv_to_tm (
# 96 "FStar.Syntax.Subst.fst"
let _31_70 = a
in {FStar_Syntax_Syntax.ppname = _31_70.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _31_70.FStar_Syntax_Syntax.sort}))
in Some (_115_29))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _31_77 -> begin
None
end))))

# 99 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _31_3 -> (match (_31_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _31_86 -> begin
None
end))))

# 102 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _31_4 -> (match (_31_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _31_95 -> begin
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
let map_some_curry = (fun f x _31_5 -> (match (_31_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 120 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _115_67 = (apply_until_some f s)
in (FStar_All.pipe_right _115_67 (map_some_curry g t))))

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
(let _115_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_115_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _115_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_115_73))
end)))

# 140 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_139 -> begin
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
(let _115_89 = (let _115_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_115_88))
in (FStar_Syntax_Syntax.mk _115_89 None t0.FStar_Syntax_Syntax.pos))
end
| _31_171 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_6 -> (match (_31_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _115_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_115_94))
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
# 180 "FStar.Syntax.Subst.fst"
let _31_185 = t
in (let _115_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _115_100 = (FStar_List.map (fun _31_189 -> (match (_31_189) with
| (t, imp) -> begin
(let _115_98 = (subst' s t)
in (_115_98, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _115_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _31_185.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _115_101; FStar_Syntax_Syntax.effect_args = _115_100; FStar_Syntax_Syntax.flags = _115_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_196 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _115_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _115_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _115_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _115_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _115_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _115_106))
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
| FStar_Syntax_Syntax.NT (_31_224) -> begin
s
end))

# 201 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 202 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 203 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _31_233 -> (match (_31_233) with
| (x, imp) -> begin
(let _115_124 = (
# 203 "FStar.Syntax.Subst.fst"
let _31_234 = x
in (let _115_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_123}))
in (_115_124, imp))
end))

# 204 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _115_129 = (shift_subst' i s)
in (subst_binder' _115_129 b))
end))))

# 208 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _31_243 -> (match (_31_243) with
| (t, imp) -> begin
(let _115_132 = (subst' s t)
in (_115_132, imp))
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
| FStar_Syntax_Syntax.Pat_constant (_31_253) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let _31_261 = (aux n p)
in (match (_31_261) with
| (p, m) -> begin
(
# 218 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _115_145 = (aux n p)
in (Prims.fst _115_145))) ps)
in ((
# 219 "FStar.Syntax.Subst.fst"
let _31_264 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_264.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_264.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _31_281 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_272 _31_275 -> (match ((_31_272, _31_275)) with
| ((pats, n), (p, imp)) -> begin
(
# 223 "FStar.Syntax.Subst.fst"
let _31_278 = (aux n p)
in (match (_31_278) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_31_281) with
| (pats, n) -> begin
((
# 225 "FStar.Syntax.Subst.fst"
let _31_282 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_282.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_282.FStar_Syntax_Syntax.p}), n)
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
let _31_287 = x
in (let _115_148 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_287.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_287.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_148}))
in ((
# 230 "FStar.Syntax.Subst.fst"
let _31_290 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _31_290.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_290.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 233 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 234 "FStar.Syntax.Subst.fst"
let x = (
# 234 "FStar.Syntax.Subst.fst"
let _31_295 = x
in (let _115_149 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_149}))
in ((
# 235 "FStar.Syntax.Subst.fst"
let _31_298 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _31_298.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_298.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 238 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 239 "FStar.Syntax.Subst.fst"
let x = (
# 239 "FStar.Syntax.Subst.fst"
let _31_305 = x
in (let _115_150 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_150}))
in (
# 240 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 241 "FStar.Syntax.Subst.fst"
let _31_309 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_309.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_309.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 244 "FStar.Syntax.Subst.fst"
let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _115_158 = (
# 247 "FStar.Syntax.Subst.fst"
let _31_316 = l
in (let _115_157 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _31_316.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _115_157; FStar_Syntax_Syntax.cflags = _31_316.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _31_318 -> (match (()) with
| () -> begin
(let _115_156 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _115_156))
end))}))
in Some (_115_158))
end))

# 250 "FStar.Syntax.Subst.fst"
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
# 266 "FStar.Syntax.Subst.fst"
let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _115_169 = (let _115_168 = (let _115_167 = (subst' s t0)
in (let _115_166 = (subst_args' s args)
in (_115_167, _115_166)))
in FStar_Syntax_Syntax.Tm_app (_115_168))
in (FStar_Syntax_Syntax.mk _115_169 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _115_173 = (let _115_172 = (let _115_171 = (subst' s t0)
in (let _115_170 = (subst' s t1)
in (_115_171, _115_170, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_115_172))
in (FStar_Syntax_Syntax.mk _115_173 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 274 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 275 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _115_178 = (let _115_177 = (let _115_176 = (subst_binders' s bs)
in (let _115_175 = (subst' s' body)
in (let _115_174 = (push_subst_lcomp s' lopt)
in (_115_176, _115_175, _115_174))))
in FStar_Syntax_Syntax.Tm_abs (_115_177))
in (FStar_Syntax_Syntax.mk _115_178 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 279 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _115_183 = (let _115_182 = (let _115_181 = (subst_binders' s bs)
in (let _115_180 = (let _115_179 = (shift_subst' n s)
in (subst_comp' _115_179 comp))
in (_115_181, _115_180)))
in FStar_Syntax_Syntax.Tm_arrow (_115_182))
in (FStar_Syntax_Syntax.mk _115_183 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 283 "FStar.Syntax.Subst.fst"
let x = (
# 283 "FStar.Syntax.Subst.fst"
let _31_373 = x
in (let _115_184 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_184}))
in (
# 284 "FStar.Syntax.Subst.fst"
let phi = (let _115_185 = (shift_subst' 1 s)
in (subst' _115_185 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 288 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 289 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _31_385 -> (match (_31_385) with
| (pat, wopt, branch) -> begin
(
# 290 "FStar.Syntax.Subst.fst"
let _31_388 = (subst_pat' s pat)
in (match (_31_388) with
| (pat, n) -> begin
(
# 291 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 292 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _115_187 = (subst' s w)
in Some (_115_187))
end)
in (
# 295 "FStar.Syntax.Subst.fst"
let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(
# 300 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length lbs)
in (
# 301 "FStar.Syntax.Subst.fst"
let sn = (shift_subst' n s)
in (
# 302 "FStar.Syntax.Subst.fst"
let body = (subst' sn body)
in (
# 303 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 304 "FStar.Syntax.Subst.fst"
let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (
# 305 "FStar.Syntax.Subst.fst"
let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (
# 308 "FStar.Syntax.Subst.fst"
let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((
# 309 "FStar.Syntax.Subst.fst"
let _31_410 = x
in {FStar_Syntax_Syntax.ppname = _31_410.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_410.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((
# 310 "FStar.Syntax.Subst.fst"
let _31_414 = fv
in {FStar_Syntax_Syntax.fv_name = (
# 310 "FStar.Syntax.Subst.fst"
let _31_416 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _31_416.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _31_416.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _31_414.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _31_414.FStar_Syntax_Syntax.fv_qual}))
end)
in (
# 311 "FStar.Syntax.Subst.fst"
let _31_419 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _31_419.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _31_419.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _115_193 = (let _115_192 = (let _115_191 = (subst' s t0)
in (let _115_190 = (let _115_189 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_115_189))
in (_115_191, _115_190)))
in FStar_Syntax_Syntax.Tm_meta (_115_192))
in (FStar_Syntax_Syntax.mk _115_193 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _115_196 = (let _115_195 = (let _115_194 = (subst' s t)
in (_115_194, m))
in FStar_Syntax_Syntax.Tm_meta (_115_195))
in (FStar_Syntax_Syntax.mk _115_196 None t.FStar_Syntax_Syntax.pos))
end))

# 320 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 321 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 324 "FStar.Syntax.Subst.fst"
let t' = (let _115_199 = (push_subst s t)
in (compress _115_199))
in (
# 325 "FStar.Syntax.Subst.fst"
let _31_441 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _31_444 -> begin
(force_uvar t)
end)))

# 331 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 332 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 333 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _115_211 = (FStar_List.fold_right (fun _31_453 _31_456 -> (match ((_31_453, _31_456)) with
| ((x, _31_452), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _115_211 Prims.fst)))

# 335 "FStar.Syntax.Subst.fst"
let open_binders' = (fun bs -> (
# 336 "FStar.Syntax.Subst.fst"
let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(
# 339 "FStar.Syntax.Subst.fst"
let x' = (
# 339 "FStar.Syntax.Subst.fst"
let _31_467 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _115_217 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_467.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_467.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_217}))
in (
# 340 "FStar.Syntax.Subst.fst"
let o = (let _115_218 = (shift_subst 1 o)
in (FStar_Syntax_Syntax.DB ((0, x')))::_115_218)
in (
# 341 "FStar.Syntax.Subst.fst"
let _31_473 = (aux bs' o)
in (match (_31_473) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 344 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _115_221 = (open_binders' bs)
in (Prims.fst _115_221)))

# 345 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 346 "FStar.Syntax.Subst.fst"
let _31_479 = (open_binders' bs)
in (match (_31_479) with
| (bs', opening) -> begin
(let _115_226 = (subst opening t)
in (bs', _115_226, opening))
end)))

# 348 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 349 "FStar.Syntax.Subst.fst"
let _31_486 = (open_term' bs t)
in (match (_31_486) with
| (b, t, _31_485) -> begin
(b, t)
end)))

# 351 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 352 "FStar.Syntax.Subst.fst"
let _31_491 = (open_binders' bs)
in (match (_31_491) with
| (bs', opening) -> begin
(let _115_235 = (subst_comp opening t)
in (bs', _115_235))
end)))

# 356 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (
# 357 "FStar.Syntax.Subst.fst"
let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_31_498) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_31_501) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 364 "FStar.Syntax.Subst.fst"
let _31_507 = p
in (let _115_248 = (let _115_247 = (let _115_246 = (FStar_All.pipe_right pats (FStar_List.map (fun _31_511 -> (match (_31_511) with
| (p, b) -> begin
(let _115_245 = (aux_disj sub renaming p)
in (_115_245, b))
end))))
in (fv, _115_246))
in FStar_Syntax_Syntax.Pat_cons (_115_247))
in {FStar_Syntax_Syntax.v = _115_248; FStar_Syntax_Syntax.ty = _31_507.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_507.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 368 "FStar.Syntax.Subst.fst"
let yopt = (FStar_Util.find_map renaming (fun _31_7 -> (match (_31_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _31_519 -> begin
None
end)))
in (
# 371 "FStar.Syntax.Subst.fst"
let y = (match (yopt) with
| None -> begin
(
# 372 "FStar.Syntax.Subst.fst"
let _31_522 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _115_250 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_522.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_522.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_250}))
end
| Some (y) -> begin
y
end)
in (
# 374 "FStar.Syntax.Subst.fst"
let _31_527 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _31_527.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_527.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 377 "FStar.Syntax.Subst.fst"
let x' = (
# 377 "FStar.Syntax.Subst.fst"
let _31_531 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _115_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_531.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_531.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_251}))
in (
# 378 "FStar.Syntax.Subst.fst"
let _31_534 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _31_534.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_534.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 381 "FStar.Syntax.Subst.fst"
let x = (
# 381 "FStar.Syntax.Subst.fst"
let _31_540 = x
in (let _115_252 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_540.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_540.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_252}))
in (
# 382 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in (
# 383 "FStar.Syntax.Subst.fst"
let _31_544 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_544.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_544.FStar_Syntax_Syntax.p})))
end))
in (
# 385 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_31_553) -> begin
(p, sub, renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 391 "FStar.Syntax.Subst.fst"
let _31_562 = (aux sub renaming p)
in (match (_31_562) with
| (p, sub, renaming) -> begin
(
# 392 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((
# 393 "FStar.Syntax.Subst.fst"
let _31_564 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_564.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_564.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 396 "FStar.Syntax.Subst.fst"
let _31_584 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_573 _31_576 -> (match ((_31_573, _31_576)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(
# 397 "FStar.Syntax.Subst.fst"
let _31_580 = (aux sub renaming p)
in (match (_31_580) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, renaming)))
in (match (_31_584) with
| (pats, sub, renaming) -> begin
((
# 399 "FStar.Syntax.Subst.fst"
let _31_585 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_585.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_585.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 402 "FStar.Syntax.Subst.fst"
let x' = (
# 402 "FStar.Syntax.Subst.fst"
let _31_589 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _115_261 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_589.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_589.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_261}))
in (
# 403 "FStar.Syntax.Subst.fst"
let sub = (let _115_262 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_115_262)
in ((
# 404 "FStar.Syntax.Subst.fst"
let _31_593 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _31_593.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_593.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 407 "FStar.Syntax.Subst.fst"
let x' = (
# 407 "FStar.Syntax.Subst.fst"
let _31_597 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _115_263 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_263}))
in (
# 408 "FStar.Syntax.Subst.fst"
let sub = (let _115_264 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_115_264)
in ((
# 409 "FStar.Syntax.Subst.fst"
let _31_601 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _31_601.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_601.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 412 "FStar.Syntax.Subst.fst"
let x = (
# 412 "FStar.Syntax.Subst.fst"
let _31_607 = x
in (let _115_265 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_607.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_607.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_265}))
in (
# 413 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 414 "FStar.Syntax.Subst.fst"
let _31_611 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_611.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_611.FStar_Syntax_Syntax.p}), sub, renaming)))
end))
in (
# 416 "FStar.Syntax.Subst.fst"
let _31_617 = (aux [] [] p)
in (match (_31_617) with
| (p, sub, _31_616) -> begin
(p, sub)
end)))))

# 419 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _31_621 -> (match (_31_621) with
| (p, wopt, e) -> begin
(
# 420 "FStar.Syntax.Subst.fst"
let _31_624 = (open_pat p)
in (match (_31_624) with
| (p, opening) -> begin
(
# 421 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _115_268 = (subst opening w)
in Some (_115_268))
end)
in (
# 424 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 427 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _115_273 = (closing_subst bs)
in (subst _115_273 t)))

# 428 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _115_278 = (closing_subst bs)
in (subst_comp _115_278 c)))

# 429 "FStar.Syntax.Subst.fst"
let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (
# 430 "FStar.Syntax.Subst.fst"
let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(
# 433 "FStar.Syntax.Subst.fst"
let x = (
# 433 "FStar.Syntax.Subst.fst"
let _31_644 = x
in (let _115_285 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_644.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_644.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_285}))
in (
# 434 "FStar.Syntax.Subst.fst"
let s' = (let _115_286 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_115_286)
in (let _115_287 = (aux s' tl)
in ((x, imp))::_115_287)))
end))
in (aux [] bs)))

# 438 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 439 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 440 "FStar.Syntax.Subst.fst"
let _31_651 = lc
in (let _115_294 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _31_651.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _115_294; FStar_Syntax_Syntax.cflags = _31_651.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _31_653 -> (match (()) with
| () -> begin
(let _115_293 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _115_293))
end))}))))

# 443 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 444 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_31_661) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 450 "FStar.Syntax.Subst.fst"
let _31_669 = (aux sub p)
in (match (_31_669) with
| (p, sub) -> begin
(
# 451 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _115_302 = (aux sub p)
in (Prims.fst _115_302))) ps)
in ((
# 452 "FStar.Syntax.Subst.fst"
let _31_672 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_672.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_672.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 455 "FStar.Syntax.Subst.fst"
let _31_689 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_680 _31_683 -> (match ((_31_680, _31_683)) with
| ((pats, sub), (p, imp)) -> begin
(
# 456 "FStar.Syntax.Subst.fst"
let _31_686 = (aux sub p)
in (match (_31_686) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_31_689) with
| (pats, sub) -> begin
((
# 458 "FStar.Syntax.Subst.fst"
let _31_690 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_690.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_690.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 461 "FStar.Syntax.Subst.fst"
let x = (
# 461 "FStar.Syntax.Subst.fst"
let _31_694 = x
in (let _115_305 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_694.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_694.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_305}))
in (
# 462 "FStar.Syntax.Subst.fst"
let sub = (let _115_306 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_115_306)
in ((
# 463 "FStar.Syntax.Subst.fst"
let _31_698 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _31_698.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_698.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 466 "FStar.Syntax.Subst.fst"
let x = (
# 466 "FStar.Syntax.Subst.fst"
let _31_702 = x
in (let _115_307 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_702.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_702.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_307}))
in (
# 467 "FStar.Syntax.Subst.fst"
let sub = (let _115_308 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_115_308)
in ((
# 468 "FStar.Syntax.Subst.fst"
let _31_706 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _31_706.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_706.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 471 "FStar.Syntax.Subst.fst"
let x = (
# 471 "FStar.Syntax.Subst.fst"
let _31_712 = x
in (let _115_309 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_712.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_712.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _115_309}))
in (
# 472 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 473 "FStar.Syntax.Subst.fst"
let _31_716 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_716.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_716.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 476 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _31_721 -> (match (_31_721) with
| (p, wopt, e) -> begin
(
# 477 "FStar.Syntax.Subst.fst"
let _31_724 = (close_pat p)
in (match (_31_724) with
| (p, closing) -> begin
(
# 478 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _115_312 = (subst closing w)
in Some (_115_312))
end)
in (
# 481 "FStar.Syntax.Subst.fst"
let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 484 "FStar.Syntax.Subst.fst"
let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (
# 485 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 486 "FStar.Syntax.Subst.fst"
let _31_737 = (let _115_317 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 487 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _115_317 FStar_List.unzip))
in (match (_31_737) with
| (s, us') -> begin
(s, us')
end))))

# 491 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 492 "FStar.Syntax.Subst.fst"
let _31_742 = (univ_var_opening us)
in (match (_31_742) with
| (s, us') -> begin
(
# 493 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 496 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 497 "FStar.Syntax.Subst.fst"
let _31_748 = (univ_var_opening us)
in (match (_31_748) with
| (s, us') -> begin
(let _115_326 = (subst_comp s c)
in (us', _115_326))
end)))

# 500 "FStar.Syntax.Subst.fst"
let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (
# 501 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 502 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 505 "FStar.Syntax.Subst.fst"
let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (
# 506 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 507 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 510 "FStar.Syntax.Subst.fst"
let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 527 "FStar.Syntax.Subst.fst"
let _31_774 = (FStar_List.fold_right (fun lb _31_767 -> (match (_31_767) with
| (i, lbs, out) -> begin
(
# 529 "FStar.Syntax.Subst.fst"
let x = (let _115_345 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _115_345))
in ((i + 1), ((
# 530 "FStar.Syntax.Subst.fst"
let _31_769 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _31_769.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _31_769.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _31_769.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _31_769.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.DB ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_31_774) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(
# 532 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 533 "FStar.Syntax.Subst.fst"
let _31_786 = (FStar_List.fold_right (fun u _31_780 -> (match (_31_780) with
| (i, us, out) -> begin
(
# 535 "FStar.Syntax.Subst.fst"
let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UN ((i, FStar_Syntax_Syntax.U_name (u))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_31_786) with
| (_31_783, us, u_let_rec_opening) -> begin
(
# 538 "FStar.Syntax.Subst.fst"
let _31_787 = lb
in (let _115_349 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _31_787.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _31_787.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _31_787.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _115_349}))
end)))))
in (
# 540 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_opening t)
in (lbs, t)))
end))
end)

# 543 "FStar.Syntax.Subst.fst"
let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(
# 545 "FStar.Syntax.Subst.fst"
let _31_799 = (FStar_List.fold_right (fun lb _31_796 -> (match (_31_796) with
| (i, out) -> begin
(let _115_359 = (let _115_358 = (let _115_357 = (let _115_356 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_115_356, i))
in FStar_Syntax_Syntax.NM (_115_357))
in (_115_358)::out)
in ((i + 1), _115_359))
end)) lbs (0, []))
in (match (_31_799) with
| (n_let_recs, let_rec_closing) -> begin
(
# 547 "FStar.Syntax.Subst.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (
# 548 "FStar.Syntax.Subst.fst"
let _31_808 = (FStar_List.fold_right (fun u _31_804 -> (match (_31_804) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UD ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_31_808) with
| (_31_806, u_let_rec_closing) -> begin
(
# 549 "FStar.Syntax.Subst.fst"
let _31_809 = lb
in (let _115_363 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _31_809.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _31_809.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _31_809.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _31_809.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _115_363}))
end)))))
in (
# 550 "FStar.Syntax.Subst.fst"
let t = (subst let_rec_closing t)
in (lbs, t)))
end))
end)

# 553 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _31_816 -> (match (_31_816) with
| (us, t) -> begin
(
# 554 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 555 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 556 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _31_823 -> (match (_31_823) with
| (x, _31_822) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 557 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 560 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _31_829 -> (match (_31_829) with
| (us', t) -> begin
(
# 561 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 562 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us')
in (
# 563 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _115_376 = (subst s t)
in (us', _115_376)))))
end))

# 566 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 567 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _31_841 -> (match (_31_841) with
| (x, _31_840) -> begin
FStar_Syntax_Syntax.DB (((n - i), x))
end))))))




