
open Prims

let subst_to_string = (fun s -> (let _135_3 = (FStar_All.pipe_right s (FStar_List.map (fun _36_12 -> (match (_36_12) with
| (b, _36_11) -> begin
b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _135_3 (FStar_String.concat ", "))))


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


let map_some_curry = (fun f x _36_1 -> (match (_36_1) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _135_31 = (apply_until_some f s)
in (FStar_All.pipe_right _135_31 (map_some_curry g t))))


let compose_subst = (fun s1 s2 -> (

let s = (FStar_List.append (Prims.fst s1) (Prims.fst s2))
in (

let ropt = (match ((Prims.snd s2)) with
| Some (_36_38) -> begin
(Prims.snd s2)
end
| _36_41 -> begin
(Prims.snd s1)
end)
in ((s), (ropt)))))


let delay : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.term = (fun t s -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| _36_53 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t), (s)))) t.FStar_Syntax_Syntax.pos)
end))


let rec force_uvar' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _36_57) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar' t')
end
| _36_63 -> begin
t
end)
end
| _36_65 -> begin
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

let t' = (let _135_49 = (c ())
in (force_delayed_thunk _135_49))
in (

let _36_77 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _36_80 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in (

let _36_84 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _36_87 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _36_94 -> begin
u
end)
end
| _36_96 -> begin
u
end))


let subst_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _36_2 -> (match (_36_2) with
| FStar_Syntax_Syntax.DB (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _135_61 = (let _135_60 = (let _135_59 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _135_59))
in (FStar_Syntax_Syntax.bv_to_name _135_60))
in Some (_135_61))
end
| _36_105 -> begin
None
end))))


let subst_nm : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun a s -> (FStar_Util.find_map s (fun _36_3 -> (match (_36_3) with
| FStar_Syntax_Syntax.NM (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _135_67 = (FStar_Syntax_Syntax.bv_to_tm (

let _36_113 = a
in {FStar_Syntax_Syntax.ppname = _36_113.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _36_113.FStar_Syntax_Syntax.sort}))
in Some (_135_67))
end
| FStar_Syntax_Syntax.NT (x, t) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
Some (t)
end
| _36_120 -> begin
None
end))))


let subst_univ_bv : Prims.int  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _36_4 -> (match (_36_4) with
| FStar_Syntax_Syntax.UN (y, t) when (x = y) -> begin
Some (t)
end
| _36_129 -> begin
None
end))))


let subst_univ_nm : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (FStar_Util.find_map s (fun _36_5 -> (match (_36_5) with
| FStar_Syntax_Syntax.UD (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| _36_138 -> begin
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
(let _135_82 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_135_82))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _135_83 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_135_83))
end)))


let tag_with_range = (fun t s -> (match ((Prims.snd s)) with
| None -> begin
t
end
| Some (r) -> begin
(

let r = (FStar_Range.set_use_range t.FStar_Syntax_Syntax.pos r)
in (

let t' = (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(let _135_86 = (FStar_Syntax_Syntax.set_range_of_bv bv r)
in FStar_Syntax_Syntax.Tm_bvar (_135_86))
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(let _135_87 = (FStar_Syntax_Syntax.set_range_of_bv bv r)
in FStar_Syntax_Syntax.Tm_name (_135_87))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in (

let v = (

let _36_168 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = (FStar_Ident.set_lid_range l r); FStar_Syntax_Syntax.ty = _36_168.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_168.FStar_Syntax_Syntax.p})
in (

let fv = (

let _36_171 = fv
in {FStar_Syntax_Syntax.fv_name = v; FStar_Syntax_Syntax.fv_delta = _36_171.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _36_171.FStar_Syntax_Syntax.fv_qual})
in FStar_Syntax_Syntax.Tm_fvar (fv))))
end
| t' -> begin
t'
end)
in (

let _36_176 = t
in {FStar_Syntax_Syntax.n = t'; FStar_Syntax_Syntax.tk = _36_176.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _36_176.FStar_Syntax_Syntax.vars})))
end))


let tag_lid_with_range = (fun l s -> (match ((Prims.snd s)) with
| None -> begin
l
end
| Some (r) -> begin
(let _135_90 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid l) r)
in (FStar_Ident.set_lid_range l _135_90))
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
| _36_200 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(tag_with_range t0 s)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t'), ((compose_subst s' s))))) t.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_36_220), _36_223) -> begin
(failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_bv a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_nm a) (Prims.fst s) subst_tail t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _135_115 = (let _135_113 = (subst_univ (Prims.fst s) u)
in FStar_Syntax_Syntax.Tm_type (_135_113))
in (let _135_114 = (mk_range t0.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk _135_115 None _135_114)))
end
| _36_233 -> begin
(let _135_117 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl (((t0), (s)))) _135_117))
end))
end)))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _36_6 -> (match (_36_6) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _135_121 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_135_121))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _36_250 -> begin
(

let _36_251 = t
in (let _135_130 = (FStar_List.map (subst_univ (Prims.fst s)) t.FStar_Syntax_Syntax.comp_univs)
in (let _135_129 = (tag_lid_with_range t.FStar_Syntax_Syntax.effect_name s)
in (let _135_128 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _135_127 = (FStar_List.map (fun _36_255 -> (match (_36_255) with
| (t, imp) -> begin
(let _135_125 = (subst' s t)
in ((_135_125), (imp)))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _135_126 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = _135_130; FStar_Syntax_Syntax.effect_name = _135_129; FStar_Syntax_Syntax.result_typ = _135_128; FStar_Syntax_Syntax.effect_args = _135_127; FStar_Syntax_Syntax.flags = _135_126}))))))
end))
and subst_comp' : (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| (([], None)) | ((([])::[], None)) -> begin
t
end
| _36_266 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _135_134 = (subst' s t)
in (let _135_133 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_Total' _135_134 _135_133)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _135_136 = (subst' s t)
in (let _135_135 = (FStar_Option.map (subst_univ (Prims.fst s)) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _135_136 _135_135)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _135_137 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _135_137))
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
| FStar_Syntax_Syntax.NT (_36_296) -> begin
s
end))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.subst_t = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst' = (fun n s -> (let _135_148 = (FStar_All.pipe_right (Prims.fst s) (FStar_List.map (shift_subst n)))
in ((_135_148), ((Prims.snd s)))))


let subst_binder' = (fun s _36_305 -> (match (_36_305) with
| (x, imp) -> begin
(let _135_152 = (

let _36_306 = x
in (let _135_151 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_306.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_306.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_151}))
in ((_135_152), (imp)))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = (Prims.parse_int "0")) then begin
(subst_binder' s b)
end else begin
(let _135_157 = (shift_subst' i s)
in (subst_binder' _135_157 b))
end))))


let subst_binders : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun s bs -> (subst_binders' (((s)::[]), (None)) bs))


let subst_arg' = (fun s _36_317 -> (match (_36_317) with
| (t, imp) -> begin
(let _135_164 = (subst' s t)
in ((_135_164), (imp)))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Range.range Prims.option)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_36_327) -> begin
((p), (n))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _36_335 = (aux n p)
in (match (_36_335) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _135_177 = (aux n p)
in (Prims.fst _135_177))) ps)
in (((

let _36_338 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _36_338.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_338.FStar_Syntax_Syntax.p})), (m)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _36_355 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _36_346 _36_349 -> (match (((_36_346), (_36_349))) with
| ((pats, n), (p, imp)) -> begin
(

let _36_352 = (aux n p)
in (match (_36_352) with
| (p, m) -> begin
(((((p), (imp)))::pats), (m))
end))
end)) (([]), (n))))
in (match (_36_355) with
| (pats, n) -> begin
(((

let _36_356 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _36_356.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_356.FStar_Syntax_Syntax.p})), (n))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _36_361 = x
in (let _135_180 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_361.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_361.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_180}))
in (((

let _36_364 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _36_364.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_364.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _36_369 = x
in (let _135_181 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_369.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_369.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_181}))
in (((

let _36_372 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _36_372.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_372.FStar_Syntax_Syntax.p})), ((n + (Prims.parse_int "1"))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst' n s)
in (

let x = (

let _36_379 = x
in (let _135_182 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_379.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_379.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_182}))
in (

let t0 = (subst' s t0)
in (((

let _36_383 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _36_383.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_383.FStar_Syntax_Syntax.p})), (n)))))
end))
in (aux (Prims.parse_int "0") p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _135_189 = (let _135_188 = (

let _36_395 = l
in (let _135_187 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _36_395.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _135_187; FStar_Syntax_Syntax.cflags = _36_395.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _36_397 -> (match (()) with
| () -> begin
(let _135_186 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _135_186))
end))}))
in FStar_Util.Inl (_135_188))
in Some (_135_189))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (

let mk = (fun t' -> (let _135_196 = (mk_range t.FStar_Syntax_Syntax.pos s)
in (FStar_Syntax_Syntax.mk t' None _135_196)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_403) -> begin
(failwith "Impossible")
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
in (let _135_200 = (FStar_Syntax_Syntax.mk_Tm_uinst t' us)
in (tag_with_range _135_200 s)))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _135_204 = (let _135_203 = (let _135_202 = (subst' s t0)
in (let _135_201 = (subst_args' s args)
in ((_135_202), (_135_201))))
in FStar_Syntax_Syntax.Tm_app (_135_203))
in (mk _135_204))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _135_209 = (let _135_208 = (let _135_207 = (subst' s t0)
in (let _135_206 = (let _135_205 = (subst' s t1)
in FStar_Util.Inl (_135_205))
in ((_135_207), (_135_206), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_135_208))
in (mk _135_209))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _135_214 = (let _135_213 = (let _135_212 = (subst' s t0)
in (let _135_211 = (let _135_210 = (subst_comp' s c)
in FStar_Util.Inr (_135_210))
in ((_135_212), (_135_211), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_135_213))
in (mk _135_214))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst' n s)
in (let _135_219 = (let _135_218 = (let _135_217 = (subst_binders' s bs)
in (let _135_216 = (subst' s' body)
in (let _135_215 = (push_subst_lcomp s' lopt)
in ((_135_217), (_135_216), (_135_215)))))
in FStar_Syntax_Syntax.Tm_abs (_135_218))
in (mk _135_219))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _135_224 = (let _135_223 = (let _135_222 = (subst_binders' s bs)
in (let _135_221 = (let _135_220 = (shift_subst' n s)
in (subst_comp' _135_220 comp))
in ((_135_222), (_135_221))))
in FStar_Syntax_Syntax.Tm_arrow (_135_223))
in (mk _135_224)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _36_461 = x
in (let _135_225 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_461.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_461.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_225}))
in (

let phi = (let _135_226 = (shift_subst' (Prims.parse_int "1") s)
in (subst' _135_226 phi))
in (mk (FStar_Syntax_Syntax.Tm_refine (((x), (phi)))))))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _36_473 -> (match (_36_473) with
| (pat, wopt, branch) -> begin
(

let _36_476 = (subst_pat' s pat)
in (match (_36_476) with
| (pat, n) -> begin
(

let s = (shift_subst' n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _135_228 = (subst' s w)
in Some (_135_228))
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

let _36_498 = x
in {FStar_Syntax_Syntax.ppname = _36_498.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_498.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _36_502 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _36_504 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _36_504.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _36_504.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _36_502.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _36_502.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _36_507 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _36_507.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _36_507.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (mk (FStar_Syntax_Syntax.Tm_let (((((is_rec), (lbs))), (body)))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _135_234 = (let _135_233 = (let _135_232 = (subst' s t0)
in (let _135_231 = (let _135_230 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_135_230))
in ((_135_232), (_135_231))))
in FStar_Syntax_Syntax.Tm_meta (_135_233))
in (mk _135_234))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic (m, t)) -> begin
(let _135_240 = (let _135_239 = (let _135_238 = (subst' s t0)
in (let _135_237 = (let _135_236 = (let _135_235 = (subst' s t)
in ((m), (_135_235)))
in FStar_Syntax_Syntax.Meta_monadic (_135_236))
in ((_135_238), (_135_237))))
in FStar_Syntax_Syntax.Tm_meta (_135_239))
in (mk _135_240))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t)) -> begin
(let _135_246 = (let _135_245 = (let _135_244 = (subst' s t0)
in (let _135_243 = (let _135_242 = (let _135_241 = (subst' s t)
in ((m1), (m2), (_135_241)))
in FStar_Syntax_Syntax.Meta_monadic_lift (_135_242))
in ((_135_244), (_135_243))))
in FStar_Syntax_Syntax.Tm_meta (_135_245))
in (mk _135_246))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _135_249 = (let _135_248 = (let _135_247 = (subst' s t)
in ((_135_247), (m)))
in FStar_Syntax_Syntax.Tm_meta (_135_248))
in (mk _135_249))
end)))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _135_252 = (push_subst s t)
in (compress _135_252))
in (

let _36_544 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _36_547 -> begin
(

let t' = (force_uvar t)
in (match (t'.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_36_550) -> begin
(compress t')
end
| _36_553 -> begin
t'
end))
end)))


let subst : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' (((s)::[]), (None)) t))


let set_use_range : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun r t -> (subst' (([]), (Some ((

let _36_558 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = _36_558.FStar_Range.use_range})))) t))


let subst_comp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' (((s)::[]), (None)) t))


let closing_subst = (fun bs -> (let _135_271 = (FStar_List.fold_right (fun _36_566 _36_569 -> (match (((_36_566), (_36_569))) with
| ((x, _36_565), (subst, n)) -> begin
(((FStar_Syntax_Syntax.NM (((x), (n))))::subst), ((n + (Prims.parse_int "1"))))
end)) bs (([]), ((Prims.parse_int "0"))))
in (FStar_All.pipe_right _135_271 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
(([]), (o))
end
| ((x, imp))::bs' -> begin
(

let x' = (

let _36_580 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _135_277 = (subst o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_580.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_580.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_277}))
in (

let o = (let _135_278 = (shift_subst (Prims.parse_int "1") o)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_135_278)
in (

let _36_586 = (aux bs' o)
in (match (_36_586) with
| (bs', o) -> begin
(((((x'), (imp)))::bs'), (o))
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _135_281 = (open_binders' bs)
in (Prims.fst _135_281)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _36_592 = (open_binders' bs)
in (match (_36_592) with
| (bs', opening) -> begin
(let _135_286 = (subst opening t)
in ((bs'), (_135_286), (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _36_599 = (open_term' bs t)
in (match (_36_599) with
| (b, t, _36_598) -> begin
((b), (t))
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _36_604 = (open_binders' bs)
in (match (_36_604) with
| (bs', opening) -> begin
(let _135_295 = (subst_comp opening t)
in ((bs'), (_135_295)))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.subst_t) = (fun p -> (

let rec aux_disj = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_36_611) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_36_614) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _36_620 = p
in (let _135_308 = (let _135_307 = (let _135_306 = (FStar_All.pipe_right pats (FStar_List.map (fun _36_624 -> (match (_36_624) with
| (p, b) -> begin
(let _135_305 = (aux_disj sub renaming p)
in ((_135_305), (b)))
end))))
in ((fv), (_135_306)))
in FStar_Syntax_Syntax.Pat_cons (_135_307))
in {FStar_Syntax_Syntax.v = _135_308; FStar_Syntax_Syntax.ty = _36_620.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_620.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map renaming (fun _36_7 -> (match (_36_7) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _36_632 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _36_635 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _135_310 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_635.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_635.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_310}))
end
| Some (y) -> begin
y
end)
in (

let _36_640 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _36_640.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_640.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _36_644 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _135_311 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_644.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_644.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_311}))
in (

let _36_647 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _36_647.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_647.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _36_653 = x
in (let _135_312 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_653.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_653.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_312}))
in (

let t0 = (subst sub t0)
in (

let _36_657 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _36_657.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_657.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_36_666) -> begin
((p), (sub), (renaming))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _36_675 = (aux sub renaming p)
in (match (_36_675) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in (((

let _36_677 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _36_677.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_677.FStar_Syntax_Syntax.p})), (sub), (renaming)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _36_697 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _36_686 _36_689 -> (match (((_36_686), (_36_689))) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _36_693 = (aux sub renaming p)
in (match (_36_693) with
| (p, sub, renaming) -> begin
(((((p), (imp)))::pats), (sub), (renaming))
end))
end)) (([]), (sub), (renaming))))
in (match (_36_697) with
| (pats, sub, renaming) -> begin
(((

let _36_698 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _36_698.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_698.FStar_Syntax_Syntax.p})), (sub), (renaming))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _36_702 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _135_321 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_702.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_702.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_321}))
in (

let sub = (let _135_322 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_135_322)
in (((

let _36_706 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _36_706.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_706.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _36_710 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _135_323 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_710.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_710.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_323}))
in (

let sub = (let _135_324 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x'))))::_135_324)
in (((

let _36_714 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _36_714.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_714.FStar_Syntax_Syntax.p})), (sub), ((((x), (x')))::renaming))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _36_720 = x
in (let _135_325 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_720.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_720.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_325}))
in (

let t0 = (subst sub t0)
in (((

let _36_724 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _36_724.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_724.FStar_Syntax_Syntax.p})), (sub), (renaming))))
end))
in (

let _36_730 = (aux [] [] p)
in (match (_36_730) with
| (p, sub, _36_729) -> begin
((p), (sub))
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _36_734 -> (match (_36_734) with
| (p, wopt, e) -> begin
(

let _36_737 = (open_pat p)
in (match (_36_737) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _135_328 = (subst opening w)
in Some (_135_328))
end)
in (

let e = (subst opening e)
in ((p), (wopt), (e))))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _135_333 = (closing_subst bs)
in (subst _135_333 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _135_338 = (closing_subst bs)
in (subst_comp _135_338 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| ((x, imp))::tl -> begin
(

let x = (

let _36_757 = x
in (let _135_345 = (subst s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_757.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_757.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_345}))
in (

let s' = (let _135_346 = (shift_subst (Prims.parse_int "1") s)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_135_346)
in (let _135_347 = (aux s' tl)
in (((x), (imp)))::_135_347)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _36_764 = lc
in (let _135_354 = (subst s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _36_764.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _135_354; FStar_Syntax_Syntax.cflags = _36_764.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _36_766 -> (match (()) with
| () -> begin
(let _135_353 = (lc.FStar_Syntax_Syntax.comp ())
in (subst_comp s _135_353))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * FStar_Syntax_Syntax.subst_elt Prims.list) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_36_774) -> begin
((p), (sub))
end
| FStar_Syntax_Syntax.Pat_disj ((p)::ps) -> begin
(

let _36_782 = (aux sub p)
in (match (_36_782) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _135_362 = (aux sub p)
in (Prims.fst _135_362))) ps)
in (((

let _36_785 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _36_785.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_785.FStar_Syntax_Syntax.p})), (sub)))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _36_802 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _36_793 _36_796 -> (match (((_36_793), (_36_796))) with
| ((pats, sub), (p, imp)) -> begin
(

let _36_799 = (aux sub p)
in (match (_36_799) with
| (p, sub) -> begin
(((((p), (imp)))::pats), (sub))
end))
end)) (([]), (sub))))
in (match (_36_802) with
| (pats, sub) -> begin
(((

let _36_803 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _36_803.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_803.FStar_Syntax_Syntax.p})), (sub))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _36_807 = x
in (let _135_365 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_807.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_807.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_365}))
in (

let sub = (let _135_366 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_135_366)
in (((

let _36_811 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _36_811.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_811.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _36_815 = x
in (let _135_367 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_815.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_815.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_367}))
in (

let sub = (let _135_368 = (shift_subst (Prims.parse_int "1") sub)
in (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::_135_368)
in (((

let _36_819 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _36_819.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_819.FStar_Syntax_Syntax.p})), (sub))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _36_825 = x
in (let _135_369 = (subst sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _36_825.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _36_825.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_369}))
in (

let t0 = (subst sub t0)
in (((

let _36_829 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t0))); FStar_Syntax_Syntax.ty = _36_829.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _36_829.FStar_Syntax_Syntax.p})), (sub))))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _36_834 -> (match (_36_834) with
| (p, wopt, e) -> begin
(

let _36_837 = (close_pat p)
in (match (_36_837) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _135_372 = (subst closing w)
in Some (_135_372))
end)
in (

let e = (subst closing e)
in ((p), (wopt), (e))))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.subst_elt Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let _36_850 = (let _135_377 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in ((FStar_Syntax_Syntax.UN ((((n - i)), (FStar_Syntax_Syntax.U_name (u'))))), (u'))))))
in (FStar_All.pipe_right _135_377 FStar_List.unzip))
in (match (_36_850) with
| (s, us') -> begin
((s), (us'))
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _36_855 = (univ_var_opening us)
in (match (_36_855) with
| (s, us') -> begin
(

let t = (subst s t)
in ((us'), (t)))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _36_861 = (univ_var_opening us)
in (match (_36_861) with
| (s, us') -> begin
(let _135_386 = (subst_comp s c)
in ((us'), (_135_386)))
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

let _36_887 = (FStar_List.fold_right (fun lb _36_880 -> (match (_36_880) with
| (i, lbs, out) -> begin
(

let x = (let _135_405 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _135_405))
in (((i + (Prims.parse_int "1"))), (((

let _36_882 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _36_882.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _36_882.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _36_882.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _36_882.FStar_Syntax_Syntax.lbdef}))::lbs), ((FStar_Syntax_Syntax.DB (((i), (x))))::out)))
end)) lbs (((Prims.parse_int "0")), ([]), ([])))
in (match (_36_887) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _36_899 = (FStar_List.fold_right (fun u _36_893 -> (match (_36_893) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in (((i + (Prims.parse_int "1"))), ((u)::us), ((FStar_Syntax_Syntax.UN (((i), (FStar_Syntax_Syntax.U_name (u)))))::out)))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), ([]), (let_rec_opening)))
in (match (_36_899) with
| (_36_896, us, u_let_rec_opening) -> begin
(

let _36_900 = lb
in (let _135_409 = (subst u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _36_900.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _36_900.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _36_900.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _135_409}))
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

let _36_912 = (FStar_List.fold_right (fun lb _36_909 -> (match (_36_909) with
| (i, out) -> begin
(let _135_419 = (let _135_418 = (let _135_417 = (let _135_416 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in ((_135_416), (i)))
in FStar_Syntax_Syntax.NM (_135_417))
in (_135_418)::out)
in (((i + (Prims.parse_int "1"))), (_135_419)))
end)) lbs (((Prims.parse_int "0")), ([])))
in (match (_36_912) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _36_921 = (FStar_List.fold_right (fun u _36_917 -> (match (_36_917) with
| (i, out) -> begin
(((i + (Prims.parse_int "1"))), ((FStar_Syntax_Syntax.UD (((u), (i))))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs ((n_let_recs), (let_rec_closing)))
in (match (_36_921) with
| (_36_919, u_let_rec_closing) -> begin
(

let _36_922 = lb
in (let _135_423 = (subst u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _36_922.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _36_922.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _36_922.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _36_922.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _135_423}))
end)))))
in (

let t = (subst let_rec_closing t)
in ((lbs), (t))))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _36_929 -> (match (_36_929) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _36_936 -> (match (_36_936) with
| (x, _36_935) -> begin
FStar_Syntax_Syntax.NM (((x), ((k + (n - i)))))
end)) binders)
in (

let t = (subst s t)
in ((us), (t))))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _36_942 -> (match (_36_942) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - (Prims.parse_int "1"))
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UD (((x), ((k + (n - i)))))) us)
in (let _135_436 = (subst s t)
in ((us'), (_135_436))))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - (Prims.parse_int "1"))
in (FStar_All.pipe_right bs (FStar_List.mapi (fun i _36_954 -> (match (_36_954) with
| (x, _36_953) -> begin
FStar_Syntax_Syntax.DB ((((n - i)), (x)))
end))))))




