
open Prims
# 49 "FStar.Syntax.Subst.fst"
let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _31_12) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _31_18 -> begin
t
end)
end
| _31_20 -> begin
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
let t' = (let _112_8 = (c ())
in (force_delayed_thunk _112_8))
in (
# 70 "FStar.Syntax.Subst.fst"
let _31_30 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _31_33 -> begin
t
end)
end
| Some (t') -> begin
(
# 73 "FStar.Syntax.Subst.fst"
let t' = (force_delayed_thunk t')
in (
# 73 "FStar.Syntax.Subst.fst"
let _31_37 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _31_40 -> begin
t
end))

# 74 "FStar.Syntax.Subst.fst"
let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _31_47 -> begin
u
end)
end
| _31_49 -> begin
u
end))

# 82 "FStar.Syntax.Subst.fst"
let subst_to_string = (fun s -> (let _112_15 = (FStar_All.pipe_right s (FStar_List.map (fun _31_54 -> (match (_31_54) with
| (b, _31_53) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _112_15 (FStar_String.concat ", "))))

# 88 "FStar.Syntax.Subst.fst"
let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _31_1 -> (match (_31_1) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _112_23 = (let _112_22 = (let _112_21 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _112_21))
in (FStar_Syntax_Syntax.bv_to_name _112_22))
in Some (_112_23))
end
| _31_63 -> begin
None
end))))

# 94 "FStar.Syntax.Subst.fst"
let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _31_2 -> (match (_31_2) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _112_29 = (FStar_Syntax_Syntax.bv_to_tm (
# 96 "FStar.Syntax.Subst.fst"
let _31_71 = x
in {FStar_Syntax_Syntax.ppname = _31_71.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _31_71.FStar_Syntax_Syntax.sort}))
in Some (_112_29))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _31_78 -> begin
None
end))))

# 98 "FStar.Syntax.Subst.fst"
let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _31_3 -> (match (_31_3) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _31_87 -> begin
None
end))))

# 101 "FStar.Syntax.Subst.fst"
let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _31_4 -> (match (_31_4) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _31_96 -> begin
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
let map_some_curry = (fun f x _31_5 -> (match (_31_5) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))

# 118 "FStar.Syntax.Subst.fst"
let apply_until_some_then_map = (fun f s g t -> (let _112_67 = (apply_until_some f s)
in (FStar_All.pipe_right _112_67 (map_some_curry g t))))

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
(let _112_72 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_112_72))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _112_73 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_112_73))
end)))

# 137 "FStar.Syntax.Subst.fst"
let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_140 -> begin
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
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_31_159), _31_162) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _112_89 = (let _112_88 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_112_88))
in (FStar_Syntax_Syntax.mk _112_89 None t0.FStar_Syntax_Syntax.pos))
end
| _31_172 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_6 -> (match (_31_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _112_94 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_112_94))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_185 -> begin
(
# 180 "FStar.Syntax.Subst.fst"
let _31_186 = t
in (let _112_101 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _112_100 = (FStar_List.map (fun _31_190 -> (match (_31_190) with
| (t, imp) -> begin
(let _112_98 = (subst' s t)
in (_112_98, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _112_99 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _31_186.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _112_101; FStar_Syntax_Syntax.effect_args = _112_100; FStar_Syntax_Syntax.flags = _112_99}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_197 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _112_104 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _112_104))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _112_105 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _112_105))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _112_106 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _112_106))
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
| FStar_Syntax_Syntax.NT (_31_225) -> begin
s
end))

# 200 "FStar.Syntax.Subst.fst"
let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))

# 201 "FStar.Syntax.Subst.fst"
let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_All.pipe_right s (FStar_List.map (shift_subst n))))

# 202 "FStar.Syntax.Subst.fst"
let subst_binder' = (fun s _31_234 -> (match (_31_234) with
| (x, imp) -> begin
(let _112_124 = (
# 203 "FStar.Syntax.Subst.fst"
let _31_235 = x
in (let _112_123 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_235.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_235.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_123}))
in (_112_124, imp))
end))

# 203 "FStar.Syntax.Subst.fst"
let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _112_129 = (shift_subst' i s)
in (subst_binder' _112_129 b))
end))))

# 207 "FStar.Syntax.Subst.fst"
let subst_arg' = (fun s _31_244 -> (match (_31_244) with
| (t, imp) -> begin
(let _112_132 = (subst' s t)
in (_112_132, imp))
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
| FStar_Syntax_Syntax.Pat_constant (_31_254) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 217 "FStar.Syntax.Subst.fst"
let _31_262 = (aux n p)
in (match (_31_262) with
| (p, m) -> begin
(
# 218 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _112_145 = (aux n p)
in (Prims.fst _112_145))) ps)
in ((
# 219 "FStar.Syntax.Subst.fst"
let _31_265 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_265.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_265.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 222 "FStar.Syntax.Subst.fst"
let _31_282 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_273 _31_276 -> (match ((_31_273, _31_276)) with
| ((pats, n), (p, imp)) -> begin
(
# 223 "FStar.Syntax.Subst.fst"
let _31_279 = (aux n p)
in (match (_31_279) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_31_282) with
| (pats, n) -> begin
((
# 225 "FStar.Syntax.Subst.fst"
let _31_283 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_283.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_283.FStar_Syntax_Syntax.p}), n)
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
let _31_288 = x
in (let _112_148 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_288.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_288.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_148}))
in ((
# 230 "FStar.Syntax.Subst.fst"
let _31_291 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _31_291.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_291.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 233 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 234 "FStar.Syntax.Subst.fst"
let x = (
# 234 "FStar.Syntax.Subst.fst"
let _31_296 = x
in (let _112_149 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_296.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_296.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_149}))
in ((
# 235 "FStar.Syntax.Subst.fst"
let _31_299 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _31_299.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_299.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 238 "FStar.Syntax.Subst.fst"
let s = (shift_subst' n s)
in (
# 239 "FStar.Syntax.Subst.fst"
let x = (
# 239 "FStar.Syntax.Subst.fst"
let _31_306 = x
in (let _112_150 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_306.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_306.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_150}))
in (
# 240 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in ((
# 241 "FStar.Syntax.Subst.fst"
let _31_310 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_310.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_310.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))

# 242 "FStar.Syntax.Subst.fst"
let push_subst_lcomp : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s lopt -> (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _112_158 = (
# 247 "FStar.Syntax.Subst.fst"
let _31_317 = l
in (let _112_157 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _31_317.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _112_157; FStar_Syntax_Syntax.cflags = _31_317.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _31_319 -> (match (()) with
| () -> begin
(let _112_156 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _112_156))
end))}))
in Some (_112_158))
end))

# 248 "FStar.Syntax.Subst.fst"
let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_31_323) -> begin
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
(let _112_169 = (let _112_168 = (let _112_167 = (subst' s t0)
in (let _112_166 = (subst_args' s args)
in (_112_167, _112_166)))
in FStar_Syntax_Syntax.Tm_app (_112_168))
in (FStar_Syntax_Syntax.mk _112_169 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, t1, lopt) -> begin
(let _112_173 = (let _112_172 = (let _112_171 = (subst' s t0)
in (let _112_170 = (subst' s t1)
in (_112_171, _112_170, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_112_172))
in (FStar_Syntax_Syntax.mk _112_173 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 274 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (
# 275 "FStar.Syntax.Subst.fst"
let s' = (shift_subst' n s)
in (let _112_178 = (let _112_177 = (let _112_176 = (subst_binders' s bs)
in (let _112_175 = (subst' s' body)
in (let _112_174 = (push_subst_lcomp s' lopt)
in (_112_176, _112_175, _112_174))))
in FStar_Syntax_Syntax.Tm_abs (_112_177))
in (FStar_Syntax_Syntax.mk _112_178 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(
# 279 "FStar.Syntax.Subst.fst"
let n = (FStar_List.length bs)
in (let _112_183 = (let _112_182 = (let _112_181 = (subst_binders' s bs)
in (let _112_180 = (let _112_179 = (shift_subst' n s)
in (subst_comp' _112_179 comp))
in (_112_181, _112_180)))
in FStar_Syntax_Syntax.Tm_arrow (_112_182))
in (FStar_Syntax_Syntax.mk _112_183 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 283 "FStar.Syntax.Subst.fst"
let x = (
# 283 "FStar.Syntax.Subst.fst"
let _31_374 = x
in (let _112_184 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_374.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_374.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_184}))
in (
# 284 "FStar.Syntax.Subst.fst"
let phi = (let _112_185 = (shift_subst' 1 s)
in (subst' _112_185 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(
# 288 "FStar.Syntax.Subst.fst"
let t0 = (subst' s t0)
in (
# 289 "FStar.Syntax.Subst.fst"
let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _31_386 -> (match (_31_386) with
| (pat, wopt, branch) -> begin
(
# 290 "FStar.Syntax.Subst.fst"
let _31_389 = (subst_pat' s pat)
in (match (_31_389) with
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
(let _112_187 = (subst' s w)
in Some (_112_187))
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
let _31_409 = lb
in {FStar_Syntax_Syntax.lbname = _31_409.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _31_409.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _31_409.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd}))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _112_193 = (let _112_192 = (let _112_191 = (subst' s t0)
in (let _112_190 = (let _112_189 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_112_189))
in (_112_191, _112_190)))
in FStar_Syntax_Syntax.Tm_meta (_112_192))
in (FStar_Syntax_Syntax.mk _112_193 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _112_196 = (let _112_195 = (let _112_194 = (subst' s t)
in (_112_194, m))
in FStar_Syntax_Syntax.Tm_meta (_112_195))
in (FStar_Syntax_Syntax.mk _112_196 None t.FStar_Syntax_Syntax.pos))
end))

# 315 "FStar.Syntax.Subst.fst"
let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (
# 318 "FStar.Syntax.Subst.fst"
let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(
# 321 "FStar.Syntax.Subst.fst"
let t' = (let _112_199 = (push_subst s t)
in (compress _112_199))
in (
# 322 "FStar.Syntax.Subst.fst"
let _31_431 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _31_434 -> begin
(force_uvar t)
end)))

# 325 "FStar.Syntax.Subst.fst"
let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))

# 328 "FStar.Syntax.Subst.fst"
let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))

# 329 "FStar.Syntax.Subst.fst"
let closing_subst = (fun bs -> (let _112_211 = (FStar_List.fold_right (fun _31_443 _31_446 -> (match ((_31_443, _31_446)) with
| ((x, _31_442), (subst, n)) -> begin
((FStar_Syntax_Syntax.NM ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _112_211 Prims.fst)))

# 331 "FStar.Syntax.Subst.fst"
let open_binders' = (fun bs -> (
# 333 "FStar.Syntax.Subst.fst"
let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(
# 336 "FStar.Syntax.Subst.fst"
let x' = (
# 336 "FStar.Syntax.Subst.fst"
let _31_457 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _112_217 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_217}))
in (
# 337 "FStar.Syntax.Subst.fst"
let o = (let _112_218 = (shift_subst 1 o)
in (FStar_Syntax_Syntax.DB ((0, x')))::_112_218)
in (
# 338 "FStar.Syntax.Subst.fst"
let _31_463 = (aux bs' o)
in (match (_31_463) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))

# 340 "FStar.Syntax.Subst.fst"
let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _112_221 = (open_binders' bs)
in (Prims.fst _112_221)))

# 341 "FStar.Syntax.Subst.fst"
let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (
# 343 "FStar.Syntax.Subst.fst"
let _31_469 = (open_binders' bs)
in (match (_31_469) with
| (bs', opening) -> begin
(let _112_226 = (subst opening t)
in (bs', _112_226, opening))
end)))

# 344 "FStar.Syntax.Subst.fst"
let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (
# 346 "FStar.Syntax.Subst.fst"
let _31_476 = (open_term' bs t)
in (match (_31_476) with
| (b, t, _31_475) -> begin
(b, t)
end)))

# 347 "FStar.Syntax.Subst.fst"
let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (
# 349 "FStar.Syntax.Subst.fst"
let _31_481 = (open_binders' bs)
in (match (_31_481) with
| (bs', opening) -> begin
(let _112_235 = (subst_comp opening t)
in (bs', _112_235))
end)))

# 350 "FStar.Syntax.Subst.fst"
let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (
# 354 "FStar.Syntax.Subst.fst"
let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_31_488) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_31_491) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 361 "FStar.Syntax.Subst.fst"
let _31_497 = p
in (let _112_248 = (let _112_247 = (let _112_246 = (FStar_All.pipe_right pats (FStar_List.map (fun _31_501 -> (match (_31_501) with
| (p, b) -> begin
(let _112_245 = (aux_disj sub renaming p)
in (_112_245, b))
end))))
in (fv, _112_246))
in FStar_Syntax_Syntax.Pat_cons (_112_247))
in {FStar_Syntax_Syntax.v = _112_248; FStar_Syntax_Syntax.ty = _31_497.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_497.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 365 "FStar.Syntax.Subst.fst"
let yopt = (FStar_Util.find_map renaming (fun _31_7 -> (match (_31_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _31_509 -> begin
None
end)))
in (
# 368 "FStar.Syntax.Subst.fst"
let y = (match (yopt) with
| None -> begin
(
# 369 "FStar.Syntax.Subst.fst"
let _31_512 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _112_250 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_512.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_512.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_250}))
end
| Some (y) -> begin
y
end)
in (
# 371 "FStar.Syntax.Subst.fst"
let _31_517 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _31_517.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_517.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 374 "FStar.Syntax.Subst.fst"
let x' = (
# 374 "FStar.Syntax.Subst.fst"
let _31_521 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _112_251 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_251}))
in (
# 375 "FStar.Syntax.Subst.fst"
let _31_524 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _31_524.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_524.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 378 "FStar.Syntax.Subst.fst"
let x = (
# 378 "FStar.Syntax.Subst.fst"
let _31_530 = x
in (let _112_252 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_530.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_530.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_252}))
in (
# 379 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in (
# 380 "FStar.Syntax.Subst.fst"
let _31_534 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_534.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_534.FStar_Syntax_Syntax.p})))
end))
in (
# 382 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_31_543) -> begin
(p, sub, renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 388 "FStar.Syntax.Subst.fst"
let _31_552 = (aux sub renaming p)
in (match (_31_552) with
| (p, sub, renaming) -> begin
(
# 389 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((
# 390 "FStar.Syntax.Subst.fst"
let _31_554 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_554.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_554.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 393 "FStar.Syntax.Subst.fst"
let _31_574 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_563 _31_566 -> (match ((_31_563, _31_566)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(
# 394 "FStar.Syntax.Subst.fst"
let _31_570 = (aux sub renaming p)
in (match (_31_570) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, renaming)))
in (match (_31_574) with
| (pats, sub, renaming) -> begin
((
# 396 "FStar.Syntax.Subst.fst"
let _31_575 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_575.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_575.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 399 "FStar.Syntax.Subst.fst"
let x' = (
# 399 "FStar.Syntax.Subst.fst"
let _31_579 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _112_261 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_579.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_579.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_261}))
in (
# 400 "FStar.Syntax.Subst.fst"
let sub = (let _112_262 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_112_262)
in ((
# 401 "FStar.Syntax.Subst.fst"
let _31_583 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _31_583.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_583.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 404 "FStar.Syntax.Subst.fst"
let x' = (
# 404 "FStar.Syntax.Subst.fst"
let _31_587 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _112_263 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_587.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_587.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_263}))
in (
# 405 "FStar.Syntax.Subst.fst"
let sub = (let _112_264 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.DB ((0, x')))::_112_264)
in ((
# 406 "FStar.Syntax.Subst.fst"
let _31_591 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _31_591.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_591.FStar_Syntax_Syntax.p}), sub, ((x, x'))::renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 409 "FStar.Syntax.Subst.fst"
let x = (
# 409 "FStar.Syntax.Subst.fst"
let _31_597 = x
in (let _112_265 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_265}))
in (
# 410 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 411 "FStar.Syntax.Subst.fst"
let _31_601 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_601.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_601.FStar_Syntax_Syntax.p}), sub, renaming)))
end))
in (
# 413 "FStar.Syntax.Subst.fst"
let _31_607 = (aux [] [] p)
in (match (_31_607) with
| (p, sub, _31_606) -> begin
(p, sub)
end)))))

# 414 "FStar.Syntax.Subst.fst"
let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _31_611 -> (match (_31_611) with
| (p, wopt, e) -> begin
(
# 417 "FStar.Syntax.Subst.fst"
let _31_614 = (open_pat p)
in (match (_31_614) with
| (p, opening) -> begin
(
# 418 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _112_268 = (subst opening w)
in Some (_112_268))
end)
in (
# 421 "FStar.Syntax.Subst.fst"
let e = (subst opening e)
in (p, wopt, e)))
end))
end))

# 422 "FStar.Syntax.Subst.fst"
let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _112_273 = (closing_subst bs)
in (subst _112_273 t)))

# 424 "FStar.Syntax.Subst.fst"
let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _112_278 = (closing_subst bs)
in (subst_comp _112_278 c)))

# 425 "FStar.Syntax.Subst.fst"
let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (
# 427 "FStar.Syntax.Subst.fst"
let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(
# 430 "FStar.Syntax.Subst.fst"
let x = (
# 430 "FStar.Syntax.Subst.fst"
let _31_634 = x
in (let _112_285 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_634.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_634.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_285}))
in (
# 431 "FStar.Syntax.Subst.fst"
let s' = (let _112_286 = (shift_subst 1 s)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_112_286)
in (let _112_287 = (aux s' tl)
in ((x, imp))::_112_287)))
end))
in (aux [] bs)))

# 433 "FStar.Syntax.Subst.fst"
let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (
# 436 "FStar.Syntax.Subst.fst"
let s = (closing_subst bs)
in (
# 437 "FStar.Syntax.Subst.fst"
let _31_641 = lc
in (let _112_294 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _31_641.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _112_294; FStar_Syntax_Syntax.cflags = _31_641.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _31_643 -> (match (()) with
| () -> begin
(let _112_293 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _112_293))
end))}))))

# 438 "FStar.Syntax.Subst.fst"
let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (
# 441 "FStar.Syntax.Subst.fst"
let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_31_651) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(
# 447 "FStar.Syntax.Subst.fst"
let _31_659 = (aux sub p)
in (match (_31_659) with
| (p, sub) -> begin
(
# 448 "FStar.Syntax.Subst.fst"
let ps = (FStar_List.map (fun p -> (let _112_302 = (aux sub p)
in (Prims.fst _112_302))) ps)
in ((
# 449 "FStar.Syntax.Subst.fst"
let _31_662 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _31_662.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_662.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 452 "FStar.Syntax.Subst.fst"
let _31_679 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _31_670 _31_673 -> (match ((_31_670, _31_673)) with
| ((pats, sub), (p, imp)) -> begin
(
# 453 "FStar.Syntax.Subst.fst"
let _31_676 = (aux sub p)
in (match (_31_676) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_31_679) with
| (pats, sub) -> begin
((
# 455 "FStar.Syntax.Subst.fst"
let _31_680 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _31_680.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_680.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 458 "FStar.Syntax.Subst.fst"
let x = (
# 458 "FStar.Syntax.Subst.fst"
let _31_684 = x
in (let _112_305 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_684.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_684.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_305}))
in (
# 459 "FStar.Syntax.Subst.fst"
let sub = (let _112_306 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_112_306)
in ((
# 460 "FStar.Syntax.Subst.fst"
let _31_688 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _31_688.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_688.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 463 "FStar.Syntax.Subst.fst"
let x = (
# 463 "FStar.Syntax.Subst.fst"
let _31_692 = x
in (let _112_307 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_692.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_692.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_307}))
in (
# 464 "FStar.Syntax.Subst.fst"
let sub = (let _112_308 = (shift_subst 1 sub)
in (FStar_Syntax_Syntax.NM ((x, 0)))::_112_308)
in ((
# 465 "FStar.Syntax.Subst.fst"
let _31_696 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _31_696.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_696.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(
# 468 "FStar.Syntax.Subst.fst"
let x = (
# 468 "FStar.Syntax.Subst.fst"
let _31_702 = x
in (let _112_309 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _31_702.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _31_702.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _112_309}))
in (
# 469 "FStar.Syntax.Subst.fst"
let t0 = (subst sub t0)
in ((
# 470 "FStar.Syntax.Subst.fst"
let _31_706 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _31_706.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _31_706.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))

# 471 "FStar.Syntax.Subst.fst"
let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _31_711 -> (match (_31_711) with
| (p, wopt, e) -> begin
(
# 474 "FStar.Syntax.Subst.fst"
let _31_714 = (close_pat p)
in (match (_31_714) with
| (p, closing) -> begin
(
# 475 "FStar.Syntax.Subst.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _112_312 = (subst closing w)
in Some (_112_312))
end)
in (
# 478 "FStar.Syntax.Subst.fst"
let e = (subst closing e)
in (p, wopt, e)))
end))
end))

# 479 "FStar.Syntax.Subst.fst"
let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (
# 482 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 483 "FStar.Syntax.Subst.fst"
let _31_727 = (let _112_317 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (
# 484 "FStar.Syntax.Subst.fst"
let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UN (((n - i), FStar_Syntax_Syntax.U_name (u'))), u')))))
in (FStar_All.pipe_right _112_317 FStar_List.unzip))
in (match (_31_727) with
| (s, us') -> begin
(s, us')
end))))

# 486 "FStar.Syntax.Subst.fst"
let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (
# 489 "FStar.Syntax.Subst.fst"
let _31_732 = (univ_var_opening us)
in (match (_31_732) with
| (s, us') -> begin
(
# 490 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us', t))
end)))

# 491 "FStar.Syntax.Subst.fst"
let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (
# 494 "FStar.Syntax.Subst.fst"
let _31_738 = (univ_var_opening us)
in (match (_31_738) with
| (s, us') -> begin
(let _112_326 = (subst_comp s c)
in (us', _112_326))
end)))

# 495 "FStar.Syntax.Subst.fst"
let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (
# 498 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 499 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst s t))))

# 500 "FStar.Syntax.Subst.fst"
let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (
# 503 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 504 "FStar.Syntax.Subst.fst"
let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD ((u, (n - i))))))
in (subst_comp s c))))

# 505 "FStar.Syntax.Subst.fst"
let is_top_level : FStar_Syntax_Syntax.letbinding Prims.list  ->  Prims.bool = (fun _31_8 -> (match (_31_8) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_31_763); FStar_Syntax_Syntax.lbunivs = _31_761; FStar_Syntax_Syntax.lbtyp = _31_759; FStar_Syntax_Syntax.lbeff = _31_757; FStar_Syntax_Syntax.lbdef = _31_755}::_31_753 -> begin
true
end
| _31_768 -> begin
false
end))

# 509 "FStar.Syntax.Subst.fst"
let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: open_let_rec")
end)

# 513 "FStar.Syntax.Subst.fst"
let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (is_top_level lbs) then begin
(lbs, t)
end else begin
(FStar_All.failwith "NYI: close_let_rec")
end)

# 517 "FStar.Syntax.Subst.fst"
let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _31_776 -> (match (_31_776) with
| (us, t) -> begin
(
# 520 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length binders) - 1)
in (
# 521 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us)
in (
# 522 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i _31_783 -> (match (_31_783) with
| (x, _31_782) -> begin
FStar_Syntax_Syntax.NM ((x, (k + (n - i))))
end)) binders)
in (
# 523 "FStar.Syntax.Subst.fst"
let t = (subst s t)
in (us, t)))))
end))

# 524 "FStar.Syntax.Subst.fst"
let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _31_789 -> (match (_31_789) with
| (us', t) -> begin
(
# 527 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length us) - 1)
in (
# 528 "FStar.Syntax.Subst.fst"
let k = (FStar_List.length us')
in (
# 529 "FStar.Syntax.Subst.fst"
let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD ((x, (k + (n - i))))) us)
in (let _112_361 = (subst s t)
in (us', _112_361)))))
end))

# 530 "FStar.Syntax.Subst.fst"
let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (
# 533 "FStar.Syntax.Subst.fst"
let n = ((FStar_List.length bs) - 1)
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _31_801 -> (match (_31_801) with
| (x, _31_800) -> begin
FStar_Syntax_Syntax.DB (((n - i), x))
end))))))




