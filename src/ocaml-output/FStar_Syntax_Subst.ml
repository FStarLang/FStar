
open Prims

let subst_to_string = (fun s -> (let _129_3 = (FStar_All.pipe_right s (FStar_List.map (fun _35_12 -> (match (_35_12) with
| (b, _35_11) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _129_3 (FStar_String.concat ", "))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| (s0)::rest -> begin
(match ((f s0)) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some (((rest), (st)))
end)
end))


let map_some_curry = (fun f x _35_1 -> (match (_35_1) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _129_31 = (apply_until_some f s)
in (FStar_All.pipe_right _129_31 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (Prims.fst s1) (Prims.fst s2))
in (

let ropt = (match ((Prims.snd s2)) with
| Some (_35_38) -> begin
(Prims.snd s2)
end
| _35_41 -> begin
(Prims.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| _35_53 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t), (s)))) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _35_57) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar' t')
end
| _35_63 -> begin
t
end)
end
| _35_65 -> begin
t
end))


let force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (

let t' = (force_uvar' t)
in if (FStar_Util.physical_equality t t') then begin
t
end else begin
(delay t' (([]), (Some (t.FStar_Syntax_Syntax.pos))))
end))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (let _129_49 = (c ())
in (force_delayed_thunk _129_49))
in (

let _35_77 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_80 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in (

let _35_84 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_87 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _35_94 -> begin
u
end)
end
| _35_96 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _129_61 = (let _129_60 = (let _129_59 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _129_59))
in (FStar_Syntax_Syntax.bv_to_name _129_60))
in Some (_129_61))
end
| _35_105 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _35_3 -> (match (_35_3) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _129_67 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_113 = a
in {FStar_Syntax_Syntax.ppname = _35_113.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_113.FStar_Syntax_Syntax.sort}))
in Some (_129_67))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _35_120 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _35_129 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _35_5 -> (match (_35_5) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _35_138 -> begin
None
end))))


let rec subst_univ : FStar_Syntax_Syntax.subst_elt Prims.list Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (

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
(let _129_82 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_129_82))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _129_83 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_129_83))
end)))


let tag_with_range = (fun t s -> (match ((Prims.snd s)) with
| None -> begin
t
end
| Some (r) -> begin
(

let _35_160 = t
in (let _129_86 = (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r)
in {FStar_Syntax_Syntax.n = _35_160.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _35_160.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _129_86; FStar_Syntax_Syntax.vars = _35_160.FStar_Syntax_Syntax.vars}))
end))


let mk_range : FStar_Range.range  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Range.range = (fun r s -> (match ((Prims.snd s)) with
| None -> begin
r
end
| Some (r') -> begin
(FStar_Range.set_use_range r r')
end))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let subst_tail = (fun tl -> (subst' ((tl), ((Prims.snd s)))))
in (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _35_179 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_35_199), _35_202) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _129_111 = (let _129_109 = (subst_univ (Prims.fst s) u)
in FStar_Syntax_Syntax.Tm_type (_129_109))
in (let _129_110 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk _129_111 None _129_110)))
end
| _35_212 -> begin
(let _129_113 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) _129_113))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _129_117 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_129_117))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _35_229 -> begin
(

let _35_230 = t
in (let _129_125 = (FStar_List.map (subst_univ (Prims.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (let _129_124 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _129_123 = (FStar_List.map (fun _35_234 -> (match (_35_234) with
| (t, imp) -> begin
(let _129_121 = (subst' s t)
in ((_129_121), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _129_122 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = _129_125; FStar_Syntax_Syntax.effect_name = _35_230.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _129_124; FStar_Syntax_Syntax.effect_args = _129_123; FStar_Syntax_Syntax.flags = _129_122})))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _35_245 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _129_129 = (subst' s t)
in (let _129_128 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' _129_129 _129_128)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _129_131 = (subst' s t)
in (let _129_130 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _129_131 _129_130)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _129_132 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _129_132))
end)
end))


let shift : Prims.int  ->  FStar_Syntax_Syntax.subst_elt  ->  FStar_Syntax_Syntax.subst_elt = (fun n s -> (match (s) with
| FStar_Syntax_Syntax.DB (i, t) -> begin
FStar_Syntax_Syntax.DB ((((i + n)), (t)))
end
| FStar_Syntax_Syntax.UN (i, t) -> begin
FStar_Syntax_Syntax.UN ((((i + n)), (t)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
FStar_Syntax_Syntax.NM (((x), ((i + n))))
end
| FStar_Syntax_Syntax.UD (x, i) -> begin
FStar_Syntax_Syntax.UD (((x), ((i + n))))
end
| FStar_Syntax_Syntax.NT (_35_275) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' = (fun n s -> (let _129_143 = (FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n)))
in ((_129_143), ((Prims.snd s)))))


let subst_binder' = (fun s _35_284 -> (match (_35_284) with
| (x, imp) -> begin
(let _129_147 = (

let _35_285 = x
in (let _129_146 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_285.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_285.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_146}))
in ((_129_147), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = (Prims.parse_int "0")) then begin
(subst_binder' s b)
end else begin
(let _129_152 = (shift_subst' i s)
in (subst_binder' _129_152 b))
end))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (None)) bs))


let subst_arg' = (fun s _35_296 -> (match (_35_296) with
| (t, imp) -> begin
(let _129_159 = (subst' s t)
in ((_129_159), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_306) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_314 = (aux n p)
in (match (_35_314) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _129_172 = (aux n p)
in (Prims.fst _129_172))) ps)
in (((

let _35_317 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_317.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_317.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_334 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_325 _35_328 -> (match (((_35_325), (_35_328))) with
| ((pats, n), (p, imp)) -> begin
(

let _35_331 = (aux n p)
in (match (_35_331) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (_35_334) with
| (pats, n) -> begin
(((

let _35_335 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_335.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_335.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_340 = x
in (let _129_175 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_340.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_340.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_175}))
in (((

let _35_343 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_343.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_343.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_348 = x
in (let _129_176 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_348.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_348.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_176}))
in (((

let _35_351 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_351.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_351.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _35_358 = x
in (let _129_177 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_358.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_358.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_177}))
in (

let t0 = (subst' s t0)
in (((

let _35_362 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_362.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_362.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _129_184 = (let _129_183 = (

let _35_374 = l
in (let _129_182 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_374.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _129_182; FStar_Syntax_Syntax.cflags = _35_374.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_376 -> (match (()) with
| () -> begin
(let _129_181 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _129_181))
end))}))
in FStar_Util.Inl (_129_183))
in Some (_129_184))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk = (fun t' -> (let _129_191 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' None _129_191)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_382) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t s)
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us = (FStar_List.map (subst_univ (Prims.fst s)) us)
in (let _129_195 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us)
in (tag_with_range _129_195 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _129_199 = (let _129_198 = (let _129_197 = (subst' s t0)
in (let _129_196 = (subst_args' s args)
in ((_129_197), (_129_196))))
in FStar_Syntax_Syntax.Tm_app (_129_198))
in (mk _129_199))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _129_204 = (let _129_203 = (let _129_202 = (subst' s t0)
in (let _129_201 = (let _129_200 = (subst' s t1)
in FStar_Util.Inl (_129_200))
in ((_129_202), (_129_201), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_129_203))
in (mk _129_204))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _129_209 = (let _129_208 = (let _129_207 = (subst' s t0)
in (let _129_206 = (let _129_205 = (subst_comp' s c)
in FStar_Util.Inr (_129_205))
in ((_129_207), (_129_206), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_129_208))
in (mk _129_209))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (let _129_214 = (let _129_213 = (let _129_212 = (subst_binders' s bs)
in (let _129_211 = (subst' s' body)
in (let _129_210 = (push_subst_lcomp s' lopt)
in ((_129_212), (_129_211), (_129_210)))))
in FStar_Syntax_Syntax.Tm_abs (_129_213))
in (mk _129_214))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _129_219 = (let _129_218 = (let _129_217 = (subst_binders' s bs)
in (let _129_216 = (let _129_215 = (shift_subst' n s)
in (subst_comp' _129_215 comp))
in ((_129_217), (_129_216))))
in FStar_Syntax_Syntax.Tm_arrow (_129_218))
in (mk _129_219)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _35_440 = x
in (let _129_220 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_440.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_440.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_220}))
in (

let phi = (let _129_221 = (shift_subst' (Prims.parse_int "1") s)
in (subst' _129_221 phi))
in (mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_452 -> (match (_35_452) with
| (pat, wopt, branch) -> begin
(

let _35_455 = (subst_pat' s pat)
in (match (_35_455) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _129_223 = (subst' s w)
in Some (_129_223))
end)
in (

let branch = (subst' s branch)
in ((pat), (wopt), (branch)))))
end))
end))))
in (mk (FStar_Syntax_Syntax.Tm_match (((t0), (pats)))))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(

let n = (FStar_List.length lbs)
in (

let sn = (shift_subst' n s)
in (

let body = (subst' sn body)
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let _35_477 = x
in {FStar_Syntax_Syntax.ppname = _35_477.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_477.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _35_481 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _35_483 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_483.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_483.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_481.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_481.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _35_486 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_486.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_486.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _129_229 = (let _129_228 = (let _129_227 = (subst' s t0)
in (let _129_226 = (let _129_225 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_129_225))
in ((_129_227), (_129_226))))
in FStar_Syntax_Syntax.Tm_meta (_129_228))
in (mk _129_229))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(let _129_235 = (let _129_234 = (let _129_233 = (subst' s t0)
in (let _129_232 = (let _129_231 = (let _129_230 = (subst' s t)
in ((m), (_129_230)))
in FStar_Syntax_Syntax.Meta_monadic (_129_231))
in ((_129_233), (_129_232))))
in FStar_Syntax_Syntax.Tm_meta (_129_234))
in (mk _129_235))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _129_238 = (let _129_237 = (let _129_236 = (subst' s t)
in ((_129_236), (m)))
in FStar_Syntax_Syntax.Tm_meta (_129_237))
in (mk _129_238))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _129_241 = (push_subst s t)
in (compress _129_241))
in (

let _35_515 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_518 -> begin
(

let t' = (force_uvar t)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_521) -> begin
(compress t')
end
| _35_524 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (Some (r))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (None)) t))


let closing_subst = (fun bs -> (let _129_260 = (FStar_List.fold_right (fun _35_535 _35_538 -> (match (((_35_535), (_35_538))) with
| ((x, _35_534), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right _129_260 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let _35_549 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _129_266 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_549.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_549.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_266}))
in (

let o = (let _129_267 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_129_267)
in (

let _35_555 = (aux bs' o)
in (match (_35_555) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _129_270 = (open_binders' bs)
in (Prims.fst _129_270)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _35_561 = (open_binders' bs)
in (match (_35_561) with
| (bs', opening) -> begin
(let _129_275 = (subst opening t)
in ((bs'), (_129_275), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _35_568 = (open_term' bs t)
in (match (_35_568) with
| (b, t, _35_567) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _35_573 = (open_binders' bs)
in (match (_35_573) with
| (bs', opening) -> begin
(let _129_284 = (subst_comp opening t)
in ((bs'), (_129_284)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_580) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_583) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_589 = p
in (let _129_297 = (let _129_296 = (let _129_295 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_593 -> (match (_35_593) with
| (p, b) -> begin
(let _129_294 = (aux_disj sub renaming p)
in ((_129_294), (b)))
end))))
in ((fv), (_129_295)))
in FStar_Syntax_Syntax.Pat_cons (_129_296))
in {FStar_Syntax_Syntax.v = _129_297; FStar_Syntax_Syntax.ty = _35_589.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_589.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_601 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _35_604 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _129_299 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_604.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_604.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_299}))
end
| Some (y) -> begin
y
end)
in (

let _35_609 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_609.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_609.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_613 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _129_300 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_300}))
in (

let _35_616 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_616.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_616.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_622 = x
in (let _129_301 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_622.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_622.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_301}))
in (

let t0 = (subst sub t0)
in (

let _35_626 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_626.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_626.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_635) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_644 = (aux sub renaming p)
in (match (_35_644) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let _35_646 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_646.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_646.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_666 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_655 _35_658 -> (match (((_35_655), (_35_658))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _35_662 = (aux sub renaming p)
in (match (_35_662) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (_35_666) with
| (pats, sub, renaming) -> begin
(((

let _35_667 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_667.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_667.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _35_671 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _129_310 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_671.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_671.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_310}))
in (

let sub = (let _129_311 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_129_311)
in (((

let _35_675 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_675.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_675.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_679 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _129_312 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_679.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_679.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_312}))
in (

let sub = (let _129_313 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_129_313)
in (((

let _35_683 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_683.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_683.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_689 = x
in (let _129_314 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_689.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_689.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_314}))
in (

let t0 = (subst sub t0)
in (((

let _35_693 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_693.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_693.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let _35_699 = (aux [] [] p)
in (match (_35_699) with
| (p, sub, _35_698) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_703 -> (match (_35_703) with
| (p, wopt, e) -> begin
(

let _35_706 = (open_pat p)
in (match (_35_706) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _129_317 = (subst opening w)
in Some (_129_317))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _129_322 = (closing_subst bs)
in (subst _129_322 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _129_327 = (closing_subst bs)
in (subst_comp _129_327 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let _35_726 = x
in (let _129_334 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_726.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_726.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_334}))
in (

let s' = (let _129_335 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_129_335)
in (let _129_336 = (aux s' tl)
in (((x), (imp)))::_129_336)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _35_733 = lc
in (let _129_343 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_733.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _129_343; FStar_Syntax_Syntax.cflags = _35_733.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_735 -> (match (()) with
| () -> begin
(let _129_342 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _129_342))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_743) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _35_751 = (aux sub p)
in (match (_35_751) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _129_351 = (aux sub p)
in (Prims.fst _129_351))) ps)
in (((

let _35_754 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_754.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_754.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_771 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_762 _35_765 -> (match (((_35_762), (_35_765))) with
| ((pats, sub), (p, imp)) -> begin
(

let _35_768 = (aux sub p)
in (match (_35_768) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (_35_771) with
| (pats, sub) -> begin
(((

let _35_772 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _35_772.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_772.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _35_776 = x
in (let _129_354 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_776.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_776.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_354}))
in (

let sub = (let _129_355 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_129_355)
in (((

let _35_780 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_780.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_780.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _35_784 = x
in (let _129_356 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_784.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_784.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_356}))
in (

let sub = (let _129_357 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_129_357)
in (((

let _35_788 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_788.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_788.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_794 = x
in (let _129_358 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_794.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_794.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _129_358}))
in (

let t0 = (subst sub t0)
in (((

let _35_798 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _35_798.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_798.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_803 -> (match (_35_803) with
| (p, wopt, e) -> begin
(

let _35_806 = (close_pat p)
in (match (_35_806) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _129_361 = (subst closing w)
in Some (_129_361))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let _35_819 = (let _129_366 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right _129_366 FStar_List.unzip))
in (match (_35_819) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _35_824 = (univ_var_opening us)
in (match (_35_824) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _35_830 = (univ_var_opening us)
in (match (_35_830) with
| (s, us') -> begin
(let _129_375 = (subst_comp s c)
in ((us'), (_129_375)))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n - i)))))))
in (subst s t))))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UD (((u), ((n - i)))))))
in (subst_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (t))
end else begin
(

let _35_856 = (FStar_List.fold_right (fun lb _35_849 -> (match (_35_849) with
| (i, lbs, out) -> begin
(

let x = (let _129_394 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _129_394))
in (((i + (Prims.parse_int "1"))), (((

let _35_851 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_851.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_851.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_851.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_851.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (_35_856) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_868 = (FStar_List.fold_right (fun u _35_862 -> (match (_35_862) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (_35_868) with
| (_35_865, us, u_let_rec_opening) -> begin
(

let _35_869 = lb
in (let _129_398 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_869.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_869.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_869.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _129_398}))
end)))))
in (

let t = (subst let_rec_opening t)
in ((lbs), (t))))
end))
end)


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (t))
end else begin
(

let _35_881 = (FStar_List.fold_right (fun lb _35_878 -> (match (_35_878) with
| (i, out) -> begin
(let _129_408 = (let _129_407 = (let _129_406 = (let _129_405 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((_129_405), (i)))
in FStar_Syntax_Syntax.NM (_129_406))
in (_129_407)::out)
in (((i + (Prims.parse_int "1"))), (_129_408)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (_35_881) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_890 = (FStar_List.fold_right (fun u _35_886 -> (match (_35_886) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (_35_890) with
| (_35_888, u_let_rec_closing) -> begin
(

let _35_891 = lb
in (let _129_412 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_891.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_891.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_891.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_891.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _129_412}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_898 -> (match (_35_898) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _35_905 -> (match (_35_905) with
| (x, _35_904) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_911 -> (match (_35_911) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (let _129_425 = (subst s t)
in ((us'), (_129_425))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_923 -> (match (_35_923) with
| (x, _35_922) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




