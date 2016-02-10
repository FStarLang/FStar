
open Prims
# 28 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let syn' = (fun env k -> (FStar_Absyn_Syntax.syn (FStar_Tc_Env.get_range env) (Some (k))))

# 30 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let log : FStar_Tc_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid (FStar_Tc_Env.current_module env))))))

# 31 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let rng : FStar_Tc_Env.env  ->  FStar_Range.range = (fun env -> (FStar_Tc_Env.get_range env))

# 32 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let instantiate_both : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (let _53_24 = env
in {FStar_Tc_Env.solver = _53_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _53_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_24.FStar_Tc_Env.default_effects}))

# 33 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let no_inst : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (let _53_27 = env
in {FStar_Tc_Env.solver = _53_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _53_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_27.FStar_Tc_Env.default_effects}))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let mk_lex_list : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _155_28 = (let _155_27 = (let _155_26 = (let _155_25 = (let _155_24 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _155_23 -> FStar_Util.Inl (_155_23)) _155_24))
in (_155_25, Some (FStar_Absyn_Syntax.Implicit (false))))
in (_155_26)::((FStar_Absyn_Syntax.varg v))::((FStar_Absyn_Syntax.varg tl))::[])
in (FStar_Absyn_Util.lex_pair, _155_27))
in (FStar_Absyn_Syntax.mk_Exp_app _155_28 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

# 38 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let is_eq : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _53_1 -> (match (_53_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _53_37 -> begin
false
end))

# 41 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let steps : FStar_Tc_Env.env  ->  FStar_Tc_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)

# 45 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))

# 46 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let norm_t : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _155_41 = (steps env)
in (FStar_Tc_Normalize.norm_typ _155_41 env t)))

# 47 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let norm_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env k -> (let _155_46 = (steps env)
in (FStar_Tc_Normalize.norm_kind _155_46 env k)))

# 48 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let norm_c : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun env c -> (let _155_51 = (steps env)
in (FStar_Tc_Normalize.norm_comp _155_51 env c)))

# 49 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let fxv_check : FStar_Absyn_Syntax.exp  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either  ->  (FStar_Absyn_Syntax.bvvar Prims.list * (FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.bvvar  ->  Prims.bool))  ->  Prims.unit = (fun head env kt fvs -> (let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _155_70 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _155_70))
end
| FStar_Util.Inr (t) -> begin
(let _155_71 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _155_71))
end)
in (let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (norm)) then begin
(aux true kt)
end else begin
(let fail = (fun _53_61 -> (match (()) with
| () -> begin
(let escaping = (let _155_76 = (let _155_75 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _155_75 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _155_76 (FStar_String.concat ", ")))
in (let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _155_77 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _155_77))
end else begin
(let _155_78 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _155_78))
end
in (Prims.raise (FStar_Absyn_Syntax.Error ((msg, (FStar_Tc_Env.get_range env)))))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _53_71 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _53_78 -> begin
(fail ())
end))
end))
end
end))
end)
in (aux false kt)))

# 82 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let maybe_push_binding : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binder  ->  FStar_Tc_Env.env = (fun env b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
env
end else begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let b = FStar_Tc_Env.Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
in (FStar_Tc_Env.push_local_binding env b))
end
| FStar_Util.Inr (x) -> begin
(let b = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (FStar_Tc_Env.push_local_binding env b))
end)
end)

# 92 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let maybe_make_subst = (fun _53_2 -> (match (_53_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _53_99 -> begin
[]
end))

# 97 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let maybe_alpha_subst = (fun s b1 b2 -> if (FStar_Absyn_Syntax.is_null_binder b1) then begin
s
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (FStar_Absyn_Util.bvar_eq a b) then begin
s
end else begin
(let _155_89 = (let _155_88 = (let _155_87 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _155_87))
in FStar_Util.Inl (_155_88))
in (_155_89)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _155_92 = (let _155_91 = (let _155_90 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _155_90))
in FStar_Util.Inr (_155_91))
in (_155_92)::s)
end
end
| _53_114 -> begin
(FStar_All.failwith "impossible")
end)
end)

# 104 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let maybe_extend_subst = (fun s b v -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
s
end else begin
(match (((Prims.fst b), (Prims.fst v))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::s
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::s
end
| _53_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

# 111 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let set_lcomp_result : FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.lcomp = (fun lc t -> (let _53_132 = lc
in {FStar_Absyn_Syntax.eff_name = _53_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _53_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _53_134 -> (match (()) with
| () -> begin
(let _155_101 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _155_101 t))
end))}))

# 114 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let value_check_expected_typ : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, FStar_Absyn_Syntax.lcomp) FStar_Util.either  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e tlc -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _155_108 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _155_108))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Absyn_Syntax.res_typ
in (let _53_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _53_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_110 = (FStar_Absyn_Print.typ_to_string t)
in (let _155_109 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _155_110 _155_109)))
end else begin
()
end
in (let _53_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_53_151) with
| (e, g) -> begin
(let _53_154 = (let _155_116 = (FStar_All.pipe_left (fun _155_115 -> Some (_155_115)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _155_116 env e lc g))
in (match (_53_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_53_158) with
| (e, lc, g) -> begin
(let _53_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_117 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _155_117))
end else begin
()
end
in (e, lc, g))
end)))))

# 133 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let comp_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t) -> begin
(FStar_Tc_Util.weaken_result_typ env e lc t)
end))

# 138 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let check_expected_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp Prims.option  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp)  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env copt _53_171 -> (match (_53_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_53_173) -> begin
copt
end
| None -> begin
(let c1 = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let md = (FStar_Tc_Env.get_effect_decl env c1.FStar_Absyn_Syntax.effect_name)
in (match ((FStar_Tc_Env.default_effect env md.FStar_Absyn_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(let flags = if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_Tot_lid) then begin
(FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_ML_lid) then begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
in (let def = (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = flags})
in Some (def)))
end)))
end)
in (match (expected_c_opt) with
| None -> begin
(let _155_130 = (norm_c env c)
in (e, _155_130, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _53_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_133 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _155_132 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _155_131 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _155_133 _155_132 _155_131))))
end else begin
()
end
in (let c = (norm_c env c)
in (let expected_c' = (let _155_134 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _155_134))
in (let _53_195 = (let _155_135 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _155_135))
in (match (_53_195) with
| (e, _53_193, g) -> begin
(let _53_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_137 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _155_136 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _155_137 _155_136)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

# 168 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let no_logical_guard = (fun env _53_202 -> (match (_53_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _155_142 = (let _155_141 = (let _155_140 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (_155_140, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_155_141))
in (Prims.raise _155_142))
end)
end))

# 173 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let binding_of_lb : (FStar_Absyn_Syntax.bvvdef, FStar_Ident.lident) FStar_Util.either  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.binding = (fun x t -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
FStar_Tc_Env.Binding_var ((bvd, t))
end
| FStar_Util.Inr (lid) -> begin
FStar_Tc_Env.Binding_lid ((lid, t))
end))

# 177 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let print_expected_ty : FStar_Tc_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _155_149 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _155_149))
end))

# 181 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let with_implicits = (fun imps _53_220 -> (match (_53_220) with
| (e, l, g) -> begin
(e, l, (let _53_221 = g
in {FStar_Tc_Rel.guard_f = _53_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _53_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

# 182 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let add_implicit : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * Prims.int64), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * Prims.int64)) FStar_Util.either  ->  FStar_Tc_Rel.guard_t  ->  FStar_Tc_Rel.guard_t = (fun u g -> (let _53_225 = g
in {FStar_Tc_Rel.guard_f = _53_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _53_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

# 183 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let rec tc_kind : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd * FStar_Tc_Rel.guard_t) = (fun env k -> (let k = (FStar_Absyn_Util.compress_kind k)
in (let w = (fun f -> (f k.FStar_Absyn_Syntax.pos))
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(k, FStar_Tc_Rel.trivial_guard)
end
| FStar_Absyn_Syntax.Kind_uvar (u, args) -> begin
(let _53_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _155_202 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _155_201 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _155_202 _155_201)))
end else begin
()
end
in (let _53_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_53_249) with
| (env, _53_248) -> begin
(let _53_252 = (tc_args env args)
in (match (_53_252) with
| (args, g) -> begin
(let _155_204 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_155_204, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _53_263; FStar_Absyn_Syntax.pos = _53_261; FStar_Absyn_Syntax.fvs = _53_259; FStar_Absyn_Syntax.uvs = _53_257}) -> begin
(let _53_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_53_272) with
| (_53_269, binders, body) -> begin
(let _53_275 = (tc_args env args)
in (match (_53_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _155_208 = (let _155_207 = (let _155_206 = (let _155_205 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _155_205))
in (_155_206, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_207))
in (Prims.raise _155_208))
end else begin
(let _53_308 = (FStar_List.fold_left2 (fun _53_279 b a -> (match (_53_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(let _53_289 = (let _155_212 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _155_212))
in (match (_53_289) with
| (t, g) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (subst, ((FStar_Absyn_Syntax.targ t))::args, (g)::guards))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(let env = (let _155_213 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _155_213))
in (let _53_301 = (tc_ghost_exp env e)
in (match (_53_301) with
| (e, _53_299, g) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (subst, ((FStar_Absyn_Syntax.varg e))::args, (g)::guards))
end)))
end
| _53_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_53_308) with
| (subst, args, guards) -> begin
(let args = (FStar_List.rev args)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _155_216 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _155_216))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _53_319 = (tc_kind env k)
in (match (_53_319) with
| (k, f) -> begin
(let _53_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_53_322) with
| (args, g) -> begin
(let kabr = ((Prims.fst kabr), args)
in (let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _155_218 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _155_218))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _53_332 = (tc_binders env bs)
in (match (_53_332) with
| (bs, env, g) -> begin
(let _53_335 = (tc_kind env k)
in (match (_53_335) with
| (k, f) -> begin
(let f = (FStar_Tc_Rel.close_guard bs f)
in (let _155_221 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _155_220 = (FStar_Tc_Rel.conj_guard g f)
in (_155_221, _155_220))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _155_222 = (FStar_Tc_Util.new_kvar env)
in (_155_222, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder : FStar_Tc_Env.env  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env x -> (let _53_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_53_342) with
| (t, g) -> begin
(let x = (let _53_343 = x
in {FStar_Absyn_Syntax.v = _53_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_343.FStar_Absyn_Syntax.p})
in (let env' = (maybe_push_binding env (FStar_Absyn_Syntax.v_binder x))
in (x, env', g)))
end)))
and tc_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binder Prims.list * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env bs -> (let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _53_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_53_362) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _53_363 = a
in {FStar_Absyn_Syntax.v = _53_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_363.FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _53_370 = (aux env' bs)
in (match (_53_370) with
| (bs, env', g') -> begin
(let _155_232 = (let _155_231 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _155_231))
in ((b)::bs, env', _155_232))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _53_376 = (tc_vbinder env x)
in (match (_53_376) with
| (x, env', g) -> begin
(let b = (FStar_Util.Inr (x), imp)
in (let _53_381 = (aux env' bs)
in (match (_53_381) with
| (bs, env', g') -> begin
(let _155_234 = (let _155_233 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _155_233))
in ((b)::bs, env', _155_234))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.args * FStar_Tc_Rel.guard_t) = (fun env args -> (FStar_List.fold_right (fun _53_386 _53_389 -> (match ((_53_386, _53_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _53_396 = (tc_typ env t)
in (match (_53_396) with
| (t, _53_394, g') -> begin
(let _155_239 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _155_239))
end))
end
| FStar_Util.Inr (e) -> begin
(let _53_403 = (tc_ghost_exp env e)
in (match (_53_403) with
| (e, _53_401, g') -> begin
(let _155_240 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _155_240))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list Prims.list  ->  (FStar_Absyn_Syntax.args Prims.list * FStar_Tc_Rel.guard_t) = (fun env pats -> (FStar_List.fold_right (fun p _53_409 -> (match (_53_409) with
| (pats, g) -> begin
(let _53_412 = (tc_args env p)
in (match (_53_412) with
| (args, g') -> begin
(let _155_245 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _155_245))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax * FStar_Tc_Rel.guard_t) = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _53_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_53_419) with
| (t, g) -> begin
(let _155_248 = (FStar_Absyn_Syntax.mk_Total t)
in (_155_248, g))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (let tc = (FStar_Absyn_Syntax.mk_Typ_app (head, ((FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ))::c.FStar_Absyn_Syntax.effect_args) None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let _53_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_53_427) with
| (tc, f) -> begin
(let _53_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_53_431) with
| (_53_429, args) -> begin
(let _53_443 = (match (args) with
| (FStar_Util.Inl (res), _53_436)::args -> begin
(res, args)
end
| _53_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_53_443) with
| (res, args) -> begin
(let _53_459 = (let _155_250 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _53_3 -> (match (_53_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _53_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_53_450) with
| (env, _53_449) -> begin
(let _53_455 = (tc_ghost_exp env e)
in (match (_53_455) with
| (e, _53_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _155_250 FStar_List.unzip))
in (match (_53_459) with
| (flags, guards) -> begin
(let _155_252 = (FStar_Absyn_Syntax.mk_Comp (let _53_460 = c
in {FStar_Absyn_Syntax.effect_name = _53_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _53_460.FStar_Absyn_Syntax.flags}))
in (let _155_251 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_155_252, _155_251)))
end))
end))
end))
end)))))
end))
and tc_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.guard_t) = (fun env t -> (let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (let w = (fun k -> (FStar_Absyn_Syntax.syn t.FStar_Absyn_Syntax.pos (Some (k))))
in (let t = (FStar_Absyn_Util.compress_typ t)
in (let top = t
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let k = (FStar_Tc_Env.lookup_btvar env a)
in (let a = (let _53_472 = a
in {FStar_Absyn_Syntax.v = _53_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_472.FStar_Absyn_Syntax.p})
in (let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _53_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_53_479) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.eqT_k k)
in (let i = (let _53_484 = i
in {FStar_Absyn_Syntax.v = _53_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _53_484.FStar_Absyn_Syntax.p})
in (let _155_275 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_155_275, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.allT_k k)
in (let i = (let _53_491 = i
in {FStar_Absyn_Syntax.v = _53_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _53_491.FStar_Absyn_Syntax.p})
in (let _155_276 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_155_276, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _53_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (let i = (let _53_501 = i
in {FStar_Absyn_Syntax.v = _53_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_501.FStar_Absyn_Syntax.p})
in (let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (let _53_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_53_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(let _53_516 = (tc_binders env bs)
in (match (_53_516) with
| (bs, env, g) -> begin
(let _53_519 = (tc_comp env cod)
in (match (_53_519) with
| (cod, f) -> begin
(let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _53_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _53_542; FStar_Absyn_Syntax.result_typ = _53_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _53_536)::(FStar_Util.Inl (post), _53_531)::(FStar_Util.Inr (pats), _53_526)::[]; FStar_Absyn_Syntax.flags = _53_522}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _155_281 = (FStar_Absyn_Util.compress_exp pats)
in _155_281.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _53_557); FStar_Absyn_Syntax.tk = _53_554; FStar_Absyn_Syntax.pos = _53_552; FStar_Absyn_Syntax.fvs = _53_550; FStar_Absyn_Syntax.uvs = _53_548}, _53_572::(FStar_Util.Inr (hd), _53_569)::(FStar_Util.Inr (tl), _53_564)::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _53_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_53_578) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _53_585 -> begin
[]
end)
in (let _155_282 = (extract_pats tl)
in (FStar_List.append pat _155_282)))
end))
end
| _53_588 -> begin
[]
end))
in (let pats = (let _155_283 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _155_283))
in (let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _53_594 -> (match (_53_594) with
| (b, _53_593) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(not ((FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)))
end
| FStar_Util.Inr (x) -> begin
(not ((FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)))
end)
end))))) with
| None -> begin
()
end
| Some (b) -> begin
(let _155_286 = (let _155_285 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _155_285))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _155_286))
end))))
end
| _53_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _155_288 = (let _155_287 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _155_287))
in (t, FStar_Absyn_Syntax.ktype, _155_288))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _53_613 = (tc_binders env bs)
in (match (_53_613) with
| (bs, env, g) -> begin
(let _53_617 = (tc_typ env t)
in (match (_53_617) with
| (t, k, f) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _155_293 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _155_292 = (let _155_291 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _155_291))
in (_155_293, k, _155_292))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let _53_626 = (tc_vbinder env x)
in (match (_53_626) with
| (x, env, f1) -> begin
(let _53_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_296 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _155_295 = (FStar_Absyn_Print.typ_to_string phi)
in (let _155_294 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _155_296 _155_295 _155_294))))
end else begin
()
end
in (let _53_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_53_634) with
| (phi, f2) -> begin
(let _155_301 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _155_300 = (let _155_299 = (FStar_Tc_Rel.close_guard (((FStar_Absyn_Syntax.v_binder x))::[]) f2)
in (FStar_Tc_Rel.conj_guard f1 _155_299))
in (_155_301, FStar_Absyn_Syntax.ktype, _155_300)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _53_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_304 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _155_303 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _155_302 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _155_304 _155_303 _155_302))))
end else begin
()
end
in (let _53_644 = (tc_typ (no_inst env) head)
in (match (_53_644) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _53_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_308 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _155_307 = (FStar_Absyn_Print.typ_to_string head)
in (let _155_306 = (FStar_Absyn_Print.kind_to_string k1')
in (let _155_305 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _155_308 _155_307 _155_306 _155_305)))))
end else begin
()
end
in (let check_app = (fun _53_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_53_652) -> begin
(let _53_656 = (tc_args env args)
in (match (_53_656) with
| (args, g) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _155_311 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _155_311 Prims.fst))
in (let bs = (let _155_312 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _155_312))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (let _53_662 = (let _155_313 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _155_313))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _155_324 = (FStar_Absyn_Util.subst_kind subst kres)
in (_155_324, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) -> begin
(let _155_328 = (let _155_327 = (let _155_326 = (let _155_325 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _155_325))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _155_326))
in FStar_Absyn_Syntax.Error (_155_327))
in (Prims.raise _155_328))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _53_743 = (let _155_329 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _155_329))
in (match (_53_743) with
| (t, u) -> begin
(let targ = (let _155_331 = (FStar_All.pipe_left (fun _155_330 -> Some (_155_330)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _155_331))
in (let g = (add_implicit (FStar_Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, (_, None)::_)) | (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _53_776 = (let _155_332 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _155_332))
in (match (_53_776) with
| (e, u) -> begin
(let varg = (let _155_334 = (FStar_All.pipe_left (fun _155_333 -> Some (_155_333)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (e), _155_334))
in (let g = (add_implicit (FStar_Util.Inr (u)) g)
in (let subst = (maybe_extend_subst subst formal varg)
in (check_args ((varg)::outargs) subst g rest args))))
end)))
end
| (formal::formals, actual::actuals) -> begin
(match ((formal, actual)) with
| ((FStar_Util.Inl (a), aqual), (FStar_Util.Inl (t), imp)) -> begin
(let formal_k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _53_797 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_336 = (FStar_Absyn_Print.arg_to_string actual)
in (let _155_335 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _155_336 _155_335)))
end else begin
()
end
in (let _53_803 = (tc_typ_check (let _53_799 = env
in {FStar_Tc_Env.solver = _53_799.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_799.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_799.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_799.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_799.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_799.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_799.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_799.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_799.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_799.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_799.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_799.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_799.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_799.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_799.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_799.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _53_799.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_799.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_799.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_53_803) with
| (t, g') -> begin
(let _53_804 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_337 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _155_337))
end else begin
()
end
in (let actual = (FStar_Util.Inl (t), imp)
in (let g' = (let _155_339 = (let _155_338 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _155_338))
in (FStar_Tc_Rel.imp_guard _155_339 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _155_340 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _155_340 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _53_820 = env'
in {FStar_Tc_Env.solver = _53_820.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_820.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_820.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_820.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_820.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_820.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_820.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_820.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_820.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_820.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_820.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_820.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_820.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_820.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_820.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_820.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _53_820.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_820.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_820.FStar_Tc_Env.default_effects})
in (let _53_823 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_342 = (FStar_Absyn_Print.arg_to_string actual)
in (let _155_341 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _155_342 _155_341)))
end else begin
()
end
in (let _53_829 = (tc_ghost_exp env' v)
in (match (_53_829) with
| (v, _53_827, g') -> begin
(let actual = (FStar_Util.Inr (v), imp)
in (let g' = (let _155_344 = (let _155_343 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _155_343))
in (FStar_Tc_Rel.imp_guard _155_344 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _155_345 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _155_345 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _53_836), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (FStar_Absyn_Util.b2t v)
in (check_args outargs subst g ((formal)::formals) (((FStar_Absyn_Syntax.targ tv))::actuals)))
end
| _53_846 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_53_848), _53_851), (FStar_Util.Inl (_53_854), _53_857)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_53_861, []) -> begin
(let _155_347 = (let _155_346 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _155_346))
in (_155_347, (FStar_List.rev outargs), g))
end
| ([], _53_866) -> begin
(let _155_355 = (let _155_354 = (let _155_353 = (let _155_352 = (let _155_350 = (let _155_349 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _53_4 -> (match (_53_4) with
| (_53_870, Some (FStar_Absyn_Syntax.Implicit (_53_872))) -> begin
false
end
| _53_877 -> begin
true
end))))
in (FStar_List.length _155_349))
in (FStar_All.pipe_right _155_350 FStar_Util.string_of_int))
in (let _155_351 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _155_352 _155_351)))
in (_155_353, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_354))
in (Prims.raise _155_355))
end))
in (check_args [] [] f1 formals args))
end
| _53_879 -> begin
(let _155_358 = (let _155_357 = (let _155_356 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_155_356, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_357))
in (Prims.raise _155_358))
end)
end))
in (match ((let _155_362 = (let _155_359 = (FStar_Absyn_Util.compress_typ head)
in _155_359.FStar_Absyn_Syntax.n)
in (let _155_361 = (let _155_360 = (FStar_Absyn_Util.compress_kind k1)
in _155_360.FStar_Absyn_Syntax.n)
in (_155_362, _155_361)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_53_881), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(let result_k = (let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in (t, result_k, FStar_Tc_Rel.trivial_guard)))
end
| _53_892 -> begin
(let _53_896 = (check_app ())
in (match (_53_896) with
| (k, args, g) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(let _53_904 = (tc_kind env k1)
in (match (_53_904) with
| (k1, f1) -> begin
(let _53_907 = (tc_typ_check env t1 k1)
in (match (_53_907) with
| (t1, f2) -> begin
(let _155_366 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _155_365 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_155_366, k1, _155_365)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_53_909, k1) -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _53_918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _155_368 = (FStar_Absyn_Print.typ_to_string s)
in (let _155_367 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _155_368 _155_367)))
end else begin
()
end
in (let _155_371 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_155_371, k1, FStar_Tc_Rel.trivial_guard)))
end
| _53_921 -> begin
(let _53_922 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _155_373 = (FStar_Absyn_Print.typ_to_string s)
in (let _155_372 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _155_373 _155_372)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(let _53_933 = (tc_typ env t)
in (match (_53_933) with
| (t, k, f) -> begin
(let _155_374 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_155_374, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(let _53_944 = (tc_typ env t)
in (match (_53_944) with
| (t, k, f) -> begin
(let _155_375 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_155_375, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(let _53_953 = (tc_typ env t)
in (match (_53_953) with
| (t, k, f) -> begin
(let _155_376 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_155_376, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(let _53_961 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_53_961) with
| (quant, f) -> begin
(let _53_964 = (tc_pats env pats)
in (match (_53_964) with
| (pats, g) -> begin
(let g = (let _53_965 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _53_965.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _53_965.FStar_Tc_Rel.implicits})
in (let _155_379 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _155_378 = (FStar_Tc_Util.force_tk quant)
in (let _155_377 = (FStar_Tc_Rel.conj_guard f g)
in (_155_379, _155_378, _155_377)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let t = (FStar_Tc_Util.new_tvar env k)
in (t, k, FStar_Tc_Rel.trivial_guard)))
end
| _53_972 -> begin
(let _155_381 = (let _155_380 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _155_380))
in (FStar_All.failwith _155_381))
end))))))
and tc_typ_check : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env t k -> (let _53_979 = (tc_typ env t)
in (match (_53_979) with
| (t, k', f) -> begin
(let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (let f' = if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.keq env (Some (t)) k' k)
end else begin
(FStar_Tc_Rel.subkind env k' k)
end
in (let f = (FStar_Tc_Rel.conj_guard f f')
in (t, f))))
end)))
and tc_value : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (_53_988, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (FStar_Tc_Env.lookup_bvar env x)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar (let _53_995 = x
in {FStar_Absyn_Syntax.v = _53_995.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_995.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _53_1001 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_53_1001) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _155_388 = (let _155_387 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _155_387))
in FStar_Util.Inr (_155_388))
end
in (let _155_389 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _155_389)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (let e = (FStar_Absyn_Syntax.mk_Exp_fvar ((let _53_1008 = v
in {FStar_Absyn_Syntax.v = _53_1008.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_1008.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _53_1014 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_53_1014) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _155_391 = (let _155_390 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _155_390))
in FStar_Util.Inr (_155_391))
end
in (let is_data_ctor = (fun _53_5 -> (match (_53_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _53_1024 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _155_396 = (let _155_395 = (let _155_394 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (_155_394, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_155_395))
in (Prims.raise _155_396))
end else begin
(let _155_397 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _155_397))
end))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fail = (fun msg t -> (let _155_402 = (let _155_401 = (let _155_400 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_155_400, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_401))
in (Prims.raise _155_402)))
in (let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(let _53_1045 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _53_1044 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _53_1050 = (tc_binders env bs)
in (match (_53_1050) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun norm t -> (match ((let _155_411 = (FStar_Absyn_Util.compress_typ t)
in _155_411.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _53_1079 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _53_1078 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _53_1084 = (tc_binders env bs)
in (match (_53_1084) with
| (bs, envbody, g) -> begin
(let _53_1088 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_53_1088) with
| (envbody, _53_1087) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let rec tc_binders = (fun _53_1098 bs_annot c bs -> (match (_53_1098) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _155_420 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _155_420))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_53_1113), _53_1116), (FStar_Util.Inr (_53_1119), _53_1122)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _53_1129), (FStar_Util.Inl (b), imp)) -> begin
(let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _53_1147 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _53_1139 -> begin
(let _53_1142 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_53_1142) with
| (k, g1) -> begin
(let g2 = (FStar_Tc_Rel.keq env None ka k)
in (let g = (let _155_421 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _155_421))
in (k, g)))
end))
end)
in (match (_53_1147) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _53_1148 = b
in {FStar_Absyn_Syntax.v = _53_1148.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_1148.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _53_1156), (FStar_Util.Inr (y), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _53_1178 = (match ((let _155_422 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _155_422.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _53_1166 -> begin
(let _53_1167 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_423 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _155_423))
end else begin
()
end
in (let _53_1173 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_53_1173) with
| (t, _53_1171, g1) -> begin
(let g2 = (FStar_Tc_Rel.teq env tx t)
in (let g = (let _155_424 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _155_424))
in (t, g)))
end)))
end)
in (match (_53_1178) with
| (t, g) -> begin
(let b = (FStar_Util.Inr ((let _53_1179 = y
in {FStar_Absyn_Syntax.v = _53_1179.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_1179.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _53_1185 -> begin
(let _155_427 = (let _155_426 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _155_425 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _155_426 _155_425)))
in (fail _155_427 t))
end)
end
| ([], _53_1188) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _53_1197; FStar_Absyn_Syntax.pos = _53_1195; FStar_Absyn_Syntax.fvs = _53_1193; FStar_Absyn_Syntax.uvs = _53_1191} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _155_429 = (let _155_428 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _155_428))
in (fail _155_429 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_53_1205, []) -> begin
(let c = (let _155_430 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _155_430 c.FStar_Absyn_Syntax.pos))
in (let _155_431 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _155_431)))
end)
end))
in (let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _53_1214 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_436 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _155_436))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let env = (let _53_1217 = env
in {FStar_Tc_Env.solver = _53_1217.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_1217.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_1217.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_1217.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_1217.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_1217.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_1217.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_1217.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_1217.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_1217.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_1217.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_1217.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_1217.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _53_1217.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_1217.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_1217.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_1217.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_1217.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_1217.FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_53_1224), _53_1227) -> begin
[]
end
| (FStar_Util.Inr (x), _53_1232) -> begin
(match ((let _155_442 = (let _155_441 = (let _155_440 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _155_440))
in (FStar_Absyn_Util.unrefine _155_441))
in _155_442.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_53_1235) -> begin
[]
end
| _53_1238 -> begin
(let _155_443 = (FStar_Absyn_Util.bvar_to_exp x)
in (_155_443)::[])
end)
end)))))
in (let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun dec -> (let _53_1245 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_53_1245) with
| (head, _53_1244) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1248) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _53_1252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _53_6 -> (match (_53_6) with
| FStar_Absyn_Syntax.DECREASES (_53_1256) -> begin
true
end
| _53_1259 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _53_1263 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _155_451 = (let _155_450 = (let _155_449 = (let _155_448 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _155_447 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _155_448 _155_447)))
in (_155_449, (FStar_Tc_Env.get_range env)))
in FStar_Absyn_Syntax.Error (_155_450))
in (Prims.raise _155_451))
end else begin
()
end
in (let dec = (as_lex_list dec)
in (let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _53_1271), (FStar_Util.Inl (actual), _53_1276)) -> begin
(let _155_455 = (let _155_454 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _155_454))
in FStar_Util.Inl (_155_455))
end
| ((FStar_Util.Inr (formal), _53_1282), (FStar_Util.Inr (actual), _53_1287)) -> begin
(let _155_457 = (let _155_456 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _155_456))
in FStar_Util.Inr (_155_457))
end
| _53_1291 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _53_1294 -> begin
(let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _53_1299 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _53_1303 -> (match (_53_1303) with
| (l, t0) -> begin
(let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _155_459 = (FStar_Absyn_Util.compress_typ t)
in _155_459.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _53_7 -> (match (_53_7) with
| FStar_Absyn_Syntax.DECREASES (_53_1319) -> begin
true
end
| _53_1322 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _155_463 = (let _155_462 = (let _155_461 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _155_461))
in FStar_Util.Inr (_155_462))
in (_155_463)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (FStar_Absyn_Syntax.mk_Typ_app (precedes, ((FStar_Absyn_Syntax.varg dec))::((FStar_Absyn_Syntax.varg prev_dec))::[]) None r)))
end
| _53_1330 -> begin
(let formal_args = (FStar_All.pipe_right (FStar_List.append bs (((FStar_Absyn_Syntax.v_binder y))::[])) filter_types_and_functions)
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _53_1335 -> begin
(mk_lex_list formal_args)
end)
in (FStar_Absyn_Syntax.mk_Typ_app (precedes, ((FStar_Absyn_Syntax.varg lhs))::((FStar_Absyn_Syntax.varg prev_dec))::[]) None r)))
end)
in (let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (FStar_List.append bs (((FStar_Util.Inr ((let _53_1339 = x
in {FStar_Absyn_Syntax.v = _53_1339.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _53_1339.FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _53_1343 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_466 = (FStar_Absyn_Print.lbname_to_string l)
in (let _155_465 = (FStar_Absyn_Print.typ_to_string t)
in (let _155_464 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _155_466 _155_465 _155_464))))
end else begin
()
end
in (let _53_1350 = (let _155_467 = (FStar_All.pipe_right (FStar_Tc_Env.clear_expected_typ env) Prims.fst)
in (tc_typ _155_467 t'))
in (match (_53_1350) with
| (t', _53_1347, _53_1349) -> begin
(l, t')
end)))))))))
end
| _53_1352 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _53_1354 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _155_472 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _53_1359 -> (match (_53_1359) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _155_471 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _53_8 -> (match (_53_8) with
| (FStar_Util.Inl (x), t) -> begin
((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::[]
end
| _53_1366 -> begin
[]
end))))
in (_155_472, _155_471)))))))))))
end))
in (let _53_1371 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_53_1371) with
| (bs, envbody, g, c) -> begin
(let _53_1374 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_53_1374) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _53_1378) -> begin
(let _53_1388 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_53_1388) with
| (_53_1382, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _53_1390 -> begin
if (not (norm)) then begin
(let _155_473 = (whnf env t)
in (as_function_typ true _155_473))
end else begin
(let _53_1399 = (expected_function_typ env None)
in (match (_53_1399) with
| (_53_1392, bs, _53_1395, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_Tc_Env.use_eq
in (let _53_1403 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_53_1403) with
| (env, topt) -> begin
(let _53_1410 = (expected_function_typ env topt)
in (match (_53_1410) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _53_1416 = (tc_exp (let _53_1411 = envbody
in {FStar_Tc_Env.solver = _53_1411.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_1411.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_1411.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_1411.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_1411.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_1411.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_1411.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_1411.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_1411.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_1411.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_1411.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_1411.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_1411.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_1411.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _53_1411.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _53_1411.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_1411.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_1411.FStar_Tc_Env.default_effects}) body)
in (match (_53_1416) with
| (body, cbody, guard_body) -> begin
(let _53_1417 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _155_476 = (FStar_Absyn_Print.exp_to_string body)
in (let _155_475 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _155_474 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _155_476 _155_475 _155_474))))
end else begin
()
end
in (let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _53_1420 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _155_477 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _155_477))
end else begin
()
end
in (let _53_1427 = (let _155_479 = (let _155_478 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _155_478))
in (check_expected_effect (let _53_1422 = envbody
in {FStar_Tc_Env.solver = _53_1422.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_1422.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_1422.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_1422.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_1422.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_1422.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_1422.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_1422.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_1422.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_1422.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_1422.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_1422.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_1422.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_1422.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_1422.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_1422.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _53_1422.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_1422.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_1422.FStar_Tc_Env.default_effects}) c_opt _155_479))
in (match (_53_1427) with
| (body, cbody, guard) -> begin
(let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(let _53_1429 = (let _155_480 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _155_480))
in (let _53_1431 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _53_1431.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _53_1431.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (let e = (let _155_482 = (let _155_481 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_155_481, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _155_482 None top.FStar_Absyn_Syntax.pos))
in (let _53_1454 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_1443) -> begin
(let _155_485 = (let _155_484 = (let _155_483 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_155_483, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _155_484 None top.FStar_Absyn_Syntax.pos))
in (_155_485, t, guard))
end
| _53_1446 -> begin
(let _53_1449 = if use_teq then begin
(let _155_486 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _155_486))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_53_1449) with
| (e, guard') -> begin
(let _155_488 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _155_487 = (FStar_Tc_Rel.conj_guard guard guard')
in (_155_488, t, _155_487)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_53_1454) with
| (e, tfun, guard) -> begin
(let _53_1455 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_491 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _155_490 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _155_489 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _155_491 _155_490 _155_489))))
end else begin
()
end
in (let c = if env.FStar_Tc_Env.top_level then begin
(FStar_Absyn_Syntax.mk_Total tfun)
end else begin
(FStar_Tc_Util.return_value env tfun e)
end
in (let _53_1460 = (FStar_Tc_Util.strengthen_precondition None env e (FStar_Tc_Util.lcomp_of_comp c) guard)
in (match (_53_1460) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _53_1462 -> begin
(let _155_494 = (let _155_493 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _155_493))
in (FStar_All.failwith _155_494))
end))))
and tc_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (let _53_1466 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_498 = (FStar_All.pipe_left FStar_Range.string_of_range (FStar_Tc_Env.get_range env))
in (let _155_497 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _155_498 _155_497)))
end else begin
()
end
in (let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1472) -> begin
(let _155_522 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _155_522))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _53_1492) -> begin
(let _53_1497 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_53_1497) with
| (t1, f) -> begin
(let _53_1501 = (let _155_523 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _155_523 e1))
in (match (_53_1501) with
| (e1, c, g) -> begin
(let _53_1505 = (FStar_Tc_Util.strengthen_precondition (Some ((fun _53_1502 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos) e1 c f)
in (match (_53_1505) with
| (c, f) -> begin
(let _53_1509 = (let _155_530 = (let _155_529 = (w c)
in (FStar_All.pipe_left _155_529 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _155_530 c))
in (match (_53_1509) with
| (e, c, f2) -> begin
(let _155_532 = (let _155_531 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _155_531))
in (e, c, _155_532))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(let pats_t = (let _155_538 = (let _155_537 = (let _155_533 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _155_533))
in (let _155_536 = (let _155_535 = (let _155_534 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _155_534))
in (_155_535)::[])
in (_155_537, _155_536)))
in (FStar_Absyn_Syntax.mk_Typ_app _155_538 None FStar_Absyn_Syntax.dummyRange))
in (let _53_1519 = (let _155_539 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _155_539 e))
in (match (_53_1519) with
| (e, t, g) -> begin
(let g = (let _53_1520 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _53_1520.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _53_1520.FStar_Tc_Rel.implicits})
in (let c = (let _155_540 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _155_540 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _155_541 = (FStar_Absyn_Util.compress_exp e)
in _155_541.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_53_1530, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _53_1535; FStar_Absyn_Syntax.lbeff = _53_1533; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _53_1546 = (let _155_542 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _155_542 e1))
in (match (_53_1546) with
| (e1, c1, g1) -> begin
(let _53_1550 = (tc_exp env e2)
in (match (_53_1550) with
| (e2, c2, g2) -> begin
(let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _155_550 = (let _155_548 = (let _155_547 = (let _155_546 = (let _155_545 = (w c)
in (FStar_All.pipe_left _155_545 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1)))::[]), e2))))
in (_155_546, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_155_547))
in (FStar_Absyn_Syntax.mk_Exp_meta _155_548))
in (let _155_549 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_155_550, c, _155_549))))
end))
end))
end
| _53_1553 -> begin
(let _53_1557 = (tc_exp env e)
in (match (_53_1557) with
| (e, c, g) -> begin
(let _155_551 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_155_551, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(let _53_1566 = (tc_exp env e)
in (match (_53_1566) with
| (e, c, g) -> begin
(let _155_552 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_155_552, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let env0 = env
in (let env = (let _155_553 = (FStar_All.pipe_right (FStar_Tc_Env.clear_expected_typ env) Prims.fst)
in (FStar_All.pipe_right _155_553 instantiate_both))
in (let _53_1573 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_555 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _155_554 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _155_555 _155_554)))
end else begin
()
end
in (let _53_1578 = (tc_exp (no_inst env) head)
in (match (_53_1578) with
| (head, chead, g_head) -> begin
(let aux = (fun _53_1580 -> (match (()) with
| () -> begin
(let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1584) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _53_1596)::(FStar_Util.Inr (e2), _53_1591)::[] -> begin
(let _53_1602 = (tc_exp env e1)
in (match (_53_1602) with
| (e1, c1, g1) -> begin
(let _53_1606 = (tc_exp env e2)
in (match (_53_1606) with
| (e2, c2, g2) -> begin
(let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _155_561 = (let _155_558 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _155_558))
in (let _155_560 = (let _155_559 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _155_559 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _155_561 c2 _155_560)))
end else begin
(let _155_565 = (let _155_562 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _155_562))
in (let _155_564 = (let _155_563 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _155_563 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _155_565 _155_564 c2)))
end
in (let c = (let _155_568 = (let _155_567 = (FStar_All.pipe_left (fun _155_566 -> Some (_155_566)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_155_567, c2))
in (FStar_Tc_Util.bind env None c1 _155_568))
in (let e = (FStar_Absyn_Syntax.mk_Exp_app (head, ((FStar_Absyn_Syntax.varg e1))::((FStar_Absyn_Syntax.varg e2))::[]) (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos)
in (let _155_570 = (let _155_569 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _155_569))
in (e, c, _155_570)))))))
end))
end))
end
| _53_1613 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _53_1615 -> begin
(let thead = chead.FStar_Absyn_Syntax.res_typ
in (let _53_1617 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_572 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _155_571 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _155_572 _155_571)))
end else begin
()
end
in (let rec check_function_app = (fun norm tf -> (match ((let _155_577 = (FStar_Absyn_Util.unrefine tf)
in _155_577.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _53_1650)::_53_1646 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(let _53_1662 = (tc_exp env e)
in (match (_53_1662) with
| (e, c, g_e) -> begin
(let _53_1666 = (tc_args env tl)
in (match (_53_1666) with
| (args, comps, g_rest) -> begin
(let _155_582 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _155_582))
end))
end))
end))
in (let _53_1670 = (tc_args env args)
in (match (_53_1670) with
| (args, comps, g_args) -> begin
(let bs = (let _155_583 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _155_583))
in (let cres = (let _155_584 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _155_584 top.FStar_Absyn_Syntax.pos))
in (let _53_1673 = (let _155_586 = (let _155_585 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _155_585))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _155_586))
in (let comp = (let _155_589 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _155_589))
in (let _155_591 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _155_590 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_155_591, comp, _155_590)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let vars = (FStar_Tc_Env.binders env)
in (let rec tc_args = (fun _53_1690 bs cres args -> (match (_53_1690) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_53_1698)))::rest, (_53_1706, None)::_53_1704) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _53_1712 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _53_1716 = (let _155_627 = (let _155_626 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _155_626))
in (FStar_Tc_Rel.new_tvar _155_627 vars k))
in (match (_53_1716) with
| (targ, u) -> begin
(let _53_1717 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_629 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _155_628 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _155_629 _155_628)))
end else begin
()
end
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (FStar_Util.Inl (targ), (FStar_Absyn_Syntax.as_implicit true))
in (let _155_638 = (let _155_637 = (let _155_636 = (let _155_635 = (let _155_634 = (FStar_Tc_Util.as_uvar_t u)
in (_155_634, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_155_635))
in (add_implicit _155_636 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _155_637, fvs))
in (tc_args _155_638 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_53_1725)))::rest, (_53_1733, None)::_53_1731) -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _53_1739 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (let _53_1743 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_53_1743) with
| (varg, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (FStar_Util.Inr (varg), (FStar_Absyn_Syntax.as_implicit true))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(let _53_1759 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_644 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _155_643 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _155_644 _155_643)))
end else begin
()
end
in (let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _53_1762 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _53_1768 = (tc_typ_check (let _53_1764 = env
in {FStar_Tc_Env.solver = _53_1764.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_1764.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_1764.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_1764.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_1764.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_1764.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_1764.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_1764.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_1764.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_1764.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_1764.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_1764.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_1764.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_1764.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_1764.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_1764.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _53_1764.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_1764.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_1764.FStar_Tc_Env.default_effects}) t k)
in (match (_53_1768) with
| (t, g') -> begin
(let f = (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos (FStar_Tc_Rel.guard_form g'))
in (let g' = (let _53_1770 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _53_1770.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _53_1770.FStar_Tc_Rel.implicits})
in (let arg = (FStar_Util.Inl (t), aq)
in (let subst = (let _155_645 = (FStar_List.hd bs)
in (maybe_extend_subst subst _155_645 arg))
in (let _155_651 = (let _155_650 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _155_650, fvs))
in (tc_args _155_651 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(let _53_1788 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_653 = (FStar_Absyn_Print.subst_to_string subst)
in (let _155_652 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _155_653 _155_652)))
end else begin
()
end
in (let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _53_1791 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_654 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _155_654))
end else begin
()
end
in (let _53_1793 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (let env = (FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _53_1796 = env
in {FStar_Tc_Env.solver = _53_1796.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_1796.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_1796.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_1796.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_1796.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_1796.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_1796.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_1796.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_1796.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_1796.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_1796.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_1796.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_1796.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_1796.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_1796.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_1796.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _53_1796.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_1796.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_1796.FStar_Tc_Env.default_effects})
in (let _53_1799 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _155_656 = (FStar_Absyn_Print.exp_to_string e)
in (let _155_655 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _155_656 _155_655)))
end else begin
()
end
in (let _53_1801 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_659 = (FStar_Absyn_Print.tag_of_exp e)
in (let _155_658 = (FStar_Absyn_Print.exp_to_string e)
in (let _155_657 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _155_659 _155_658 _155_657))))
end else begin
()
end
in (let _53_1806 = (tc_exp env e)
in (match (_53_1806) with
| (e, c, g_e) -> begin
(let g = (FStar_Tc_Rel.conj_guard g g_e)
in (let _53_1808 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_661 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _155_660 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _155_661 _155_660)))
end else begin
()
end
in (let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(let subst = (let _155_662 = (FStar_List.hd bs)
in (maybe_extend_subst subst _155_662 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(let subst = (let _155_667 = (FStar_List.hd bs)
in (maybe_extend_subst subst _155_667 arg))
in (let _53_1815 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_53_1815) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _155_672 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _155_672)) then begin
(let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _155_673 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _155_673))
in (let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _155_686 = (let _155_685 = (let _155_679 = (let _155_678 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _155_678))
in (_155_679)::arg_rets)
in (let _155_684 = (let _155_682 = (let _155_681 = (FStar_All.pipe_left (fun _155_680 -> Some (_155_680)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_155_681, c))
in (_155_682)::comps)
in (let _155_683 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _155_685, _155_684, g, _155_683))))
in (tc_args _155_686 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_53_1822), _53_1825)::_53_1820, (FStar_Util.Inl (_53_1831), _53_1834)::_53_1829) -> begin
(let _155_690 = (let _155_689 = (let _155_688 = (let _155_687 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _155_687))
in ("Expected an expression; got a type", _155_688))
in FStar_Absyn_Syntax.Error (_155_689))
in (Prims.raise _155_690))
end
| ((FStar_Util.Inl (_53_1841), _53_1844)::_53_1839, (FStar_Util.Inr (_53_1850), _53_1853)::_53_1848) -> begin
(let _155_694 = (let _155_693 = (let _155_692 = (let _155_691 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _155_691))
in ("Expected a type; got an expression", _155_692))
in FStar_Absyn_Syntax.Error (_155_693))
in (Prims.raise _155_694))
end
| (_53_1858, []) -> begin
(let _53_1861 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (let _53_1879 = (match (bs) with
| [] -> begin
(let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _53_1869 -> (match (_53_1869) with
| (_53_1867, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = if refine_with_equality then begin
(let _155_696 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _155_696 cres))
end else begin
(let _53_1871 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_699 = (FStar_Absyn_Print.exp_to_string head)
in (let _155_698 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _155_697 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _155_699 _155_698 _155_697))))
end else begin
()
end
in cres)
end
in ((FStar_Tc_Util.refresh_comp_label env false cres), g)))))
end
| _53_1875 -> begin
(let g = (let _155_700 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _155_700 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _155_706 = (let _155_705 = (let _155_704 = (let _155_703 = (let _155_702 = (let _155_701 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _155_701))
in (FStar_Absyn_Syntax.mk_Typ_fun _155_702 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _155_703))
in (FStar_Absyn_Syntax.mk_Total _155_704))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _155_705))
in (_155_706, g)))
end)
in (match (_53_1879) with
| (cres, g) -> begin
(let _53_1880 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_707 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _155_707))
end else begin
()
end
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev outargs)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _53_1889 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_53_1889) with
| (comp, g) -> begin
(let _53_1890 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_713 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _155_712 = (let _155_711 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _155_711))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _155_713 _155_712)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_53_1894) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _155_718 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _155_718 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(let _53_1906 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_719 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _155_719))
end else begin
()
end
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs (FStar_Tc_Util.lcomp_of_comp cres') args))
end
| _53_1909 when (not (norm)) -> begin
(let _155_724 = (whnf env tres)
in (aux true _155_724))
end
| _53_1911 -> begin
(let _155_729 = (let _155_728 = (let _155_727 = (let _155_726 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _155_725 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _155_726 _155_725)))
in (_155_727, (FStar_Absyn_Syntax.argpos arg)))
in FStar_Absyn_Syntax.Error (_155_728))
in (Prims.raise _155_729))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs (FStar_Tc_Util.lcomp_of_comp c) args)))
end
| _53_1913 -> begin
if (not (norm)) then begin
(let _155_730 = (whnf env tf)
in (check_function_app true _155_730))
end else begin
(let _155_733 = (let _155_732 = (let _155_731 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_155_731, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_732))
in (Prims.raise _155_733))
end
end))
in (let _155_734 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _155_734)))))
end))
end))
in (let _53_1917 = (aux ())
in (match (_53_1917) with
| (e, c, g) -> begin
(let _53_1918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _155_735 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _155_735))
end else begin
()
end
in (let c = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (let _53_1925 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_739 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _155_738 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _155_737 = (FStar_All.pipe_right (FStar_Tc_Env.expected_typ env0) (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _155_739 _155_738 _155_737))))
end else begin
()
end
in (let _53_1930 = (comp_check_expected_typ env0 e c)
in (match (_53_1930) with
| (e, c, g') -> begin
(let _155_740 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _155_740))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let _53_1937 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_53_1937) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _53_1942 = (tc_exp env1 e1)
in (match (_53_1942) with
| (e1, c1, g1) -> begin
(let _53_1949 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _155_741 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_155_741, res_t)))
end)
in (match (_53_1949) with
| (env_branches, res_t) -> begin
(let guard_x = (let _155_743 = (FStar_All.pipe_left (fun _155_742 -> Some (_155_742)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _155_743))
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (let _53_1966 = (let _53_1963 = (FStar_List.fold_right (fun _53_1957 _53_1960 -> (match ((_53_1957, _53_1960)) with
| ((_53_1953, f, c, g), (caccum, gaccum)) -> begin
(let _155_746 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _155_746))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_53_1963) with
| (cases, g) -> begin
(let _155_747 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_155_747, g))
end))
in (match (_53_1966) with
| (c_branches, g_branches) -> begin
(let _53_1967 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_751 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _155_750 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _155_749 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _155_748 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _155_751 _155_750 _155_749 _155_748)))))
end else begin
()
end
in (let cres = (let _155_754 = (let _155_753 = (FStar_All.pipe_left (fun _155_752 -> Some (_155_752)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_155_753, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _155_754))
in (let e = (let _155_761 = (w cres)
in (let _155_760 = (let _155_759 = (let _155_758 = (FStar_List.map (fun _53_1977 -> (match (_53_1977) with
| (f, _53_1972, _53_1974, _53_1976) -> begin
f
end)) t_eqns)
in (e1, _155_758))
in (FStar_Absyn_Syntax.mk_Exp_match _155_759))
in (FStar_All.pipe_left _155_761 _155_760)))
in (let _155_763 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _155_762 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_155_763, cres, _155_762))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _53_1982; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| FStar_Util.Inr (_53_1995) -> begin
true
end
| _53_1998 -> begin
false
end)
in (let _53_2003 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_53_2003) with
| (env1, _53_2002) -> begin
(let _53_2016 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _53_2006 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _155_764 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _155_764))
end else begin
(let _53_2009 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_53_2009) with
| (t, f) -> begin
(let _53_2010 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _155_766 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _155_765 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _155_766 _155_765)))
end else begin
()
end
in (let t = (norm_t env1 t)
in (let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end
end)
in (match (_53_2016) with
| (f, env1) -> begin
(let _53_2022 = (tc_exp (let _53_2017 = env1
in {FStar_Tc_Env.solver = _53_2017.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_2017.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_2017.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_2017.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_2017.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_2017.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_2017.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_2017.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_2017.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_2017.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_2017.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_2017.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_2017.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_2017.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _53_2017.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_2017.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_2017.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_2017.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_2017.FStar_Tc_Env.default_effects}) e1)
in (match (_53_2022) with
| (e1, c1, g1) -> begin
(let _53_2026 = (FStar_Tc_Util.strengthen_precondition (Some ((fun _53_2023 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos) e1 c1 f)
in (match (_53_2026) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_53_2028) -> begin
(let _53_2039 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(let _53_2032 = (let _155_770 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _155_770 c1))
in (match (_53_2032) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(let _53_2033 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(FStar_Tc_Errors.warn (FStar_Tc_Env.get_range env) FStar_Tc_Errors.top_level_effect)
end else begin
()
end
in (let _155_771 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_155_771, c1)))
end
end))
end else begin
(let _53_2035 = (let _155_772 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.discharge_guard env _155_772))
in (let _155_773 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _155_773)))
end
in (match (_53_2039) with
| (e2, c1) -> begin
(let _53_2044 = if env.FStar_Tc_Env.generalize then begin
(let _155_774 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _155_774))
end else begin
(x, e1, c1)
end
in (match (_53_2044) with
| (_53_2041, e1, c1) -> begin
(let cres = (let _155_775 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _155_775))
in (let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(FStar_Tc_Util.bind env None (FStar_Tc_Util.lcomp_of_comp c1) (None, cres))
end
in (let _53_2047 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _155_779 = (let _155_778 = (w cres)
in (FStar_All.pipe_left _155_778 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1)))::[]), e2))))
in (_155_779, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (let _53_2055 = (tc_exp (FStar_Tc_Env.push_local_binding env b) e2)
in (match (_53_2055) with
| (e2, c2, g2) -> begin
(let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _155_782 = (w cres)
in (FStar_All.pipe_left _155_782 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1)))::[]), e2))))
in (let g2 = (let _155_788 = (let _155_787 = (let _155_786 = (let _155_785 = (let _155_784 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _155_784 e1))
in (FStar_All.pipe_left (fun _155_783 -> FStar_Tc_Rel.NonTrivial (_155_783)) _155_785))
in (FStar_Tc_Rel.guard_of_guard_formula _155_786))
in (FStar_Tc_Rel.imp_guard _155_787 g2))
in (FStar_All.pipe_left (FStar_Tc_Rel.close_guard (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ)))::[])) _155_788))
in (let guard = (let _155_789 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _155_789))
in (match (topt) with
| None -> begin
(let tres = cres.FStar_Absyn_Syntax.res_typ
in (let fvs = (FStar_Absyn_Util.freevars_typ tres)
in if (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs) then begin
(let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _53_2064 = (let _155_790 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _155_790))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _53_2067 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _53_2070), _53_2073) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(let env = (instantiate_both env)
in (let _53_2085 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_53_2085) with
| (env0, topt) -> begin
(let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _53_9 -> (match (_53_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_53_2094); FStar_Absyn_Syntax.lbtyp = _53_2092; FStar_Absyn_Syntax.lbeff = _53_2090; FStar_Absyn_Syntax.lbdef = _53_2088} -> begin
true
end
| _53_2098 -> begin
false
end))))
in (let _53_2123 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _53_2102 _53_2108 -> (match ((_53_2102, _53_2108)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _53_2105; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _53_2113 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_53_2113) with
| (_53_2110, t, check_t) -> begin
(let e = (FStar_Absyn_Util.unascribe e)
in (let t = if (not (check_t)) then begin
t
end else begin
(let _155_794 = (tc_typ_check_trivial (let _53_2115 = env0
in {FStar_Tc_Env.solver = _53_2115.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_2115.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_2115.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_2115.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_2115.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_2115.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_2115.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_2115.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_2115.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_2115.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_2115.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_2115.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_2115.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_2115.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_2115.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _53_2115.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_2115.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_2115.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_2115.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _155_794 (norm_t env)))
end
in (let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(let _53_2118 = env
in {FStar_Tc_Env.solver = _53_2118.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_2118.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_2118.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_2118.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_2118.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_2118.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_2118.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_2118.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_2118.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_2118.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_2118.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_2118.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_2118.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_2118.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_2118.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_2118.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_2118.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_2118.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_2118.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_53_2123) with
| (lbs, env') -> begin
(let _53_2138 = (let _155_800 = (let _155_799 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _155_799 (FStar_List.map (fun _53_2127 -> (match (_53_2127) with
| (x, t, e) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (let _53_2129 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_798 = (FStar_Absyn_Print.lbname_to_string x)
in (let _155_797 = (FStar_Absyn_Print.exp_to_string e)
in (let _155_796 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _155_798 _155_797 _155_796))))
end else begin
()
end
in (let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (let _53_2135 = (tc_total_exp env' e)
in (match (_53_2135) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _155_800 FStar_List.unzip))
in (match (_53_2138) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (let _53_2157 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _155_802 = (FStar_List.map (fun _53_2143 -> (match (_53_2143) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_155_802, g_lbs))
end else begin
(let _53_2144 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _155_805 = (FStar_All.pipe_right lbs (FStar_List.map (fun _53_2149 -> (match (_53_2149) with
| (x, t, e) -> begin
(let _155_804 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb (x, t, e)))
in (x, e, _155_804))
end))))
in (FStar_Tc_Util.generalize true env _155_805))
in (let _155_807 = (FStar_List.map (fun _53_2154 -> (match (_53_2154) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_155_807, FStar_Tc_Rel.trivial_guard))))
end
in (match (_53_2157) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(let cres = (let _155_808 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _155_808))
in (let _53_2159 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let _53_2161 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _155_812 = (let _155_811 = (w cres)
in (FStar_All.pipe_left _155_811 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_155_812, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(let _53_2177 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _53_2165 _53_2172 -> (match ((_53_2165, _53_2172)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _53_2169; FStar_Absyn_Syntax.lbdef = _53_2167}) -> begin
(let b = (binding_of_lb x t)
in (let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_53_2177) with
| (bindings, env) -> begin
(let _53_2181 = (tc_exp env e1)
in (match (_53_2181) with
| (e1, cres, g1) -> begin
(let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (let cres = (let _53_2185 = cres
in {FStar_Absyn_Syntax.eff_name = _53_2185.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _53_2185.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _53_2185.FStar_Absyn_Syntax.comp})
in (let e = (let _155_817 = (w cres)
in (FStar_All.pipe_left _155_817 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_53_2190) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _53_10 -> (match (_53_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_53_2202); FStar_Absyn_Syntax.lbtyp = _53_2200; FStar_Absyn_Syntax.lbeff = _53_2198; FStar_Absyn_Syntax.lbdef = _53_2196} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _53_2210; FStar_Absyn_Syntax.lbeff = _53_2208; FStar_Absyn_Syntax.lbdef = _53_2206} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _53_2219; FStar_Absyn_Syntax.lbeff = _53_2217; FStar_Absyn_Syntax.lbdef = _53_2215}) -> begin
(let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _53_2225 = (let _155_819 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _155_819))
in (e, cres, guard)))
end
| _53_2228 -> begin
(e, cres, guard)
end))
end))))))
end))
end))
end
end)))
end))
end)))
end)))
end))))))
and tc_eqn : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp)  ->  ((FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) * FStar_Absyn_Syntax.formula * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun scrutinee_x pat_t env _53_2235 -> (match (_53_2235) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _53_2243 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_53_2243) with
| (bindings, exps, p) -> begin
(let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (let _53_2252 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _53_11 -> (match (_53_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _155_832 = (FStar_Absyn_Print.strBvd x)
in (let _155_831 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _155_832 _155_831)))
end
| _53_2251 -> begin
()
end))))
end else begin
()
end
in (let _53_2257 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_53_2257) with
| (env1, _53_2256) -> begin
(let env1 = (let _53_2258 = env1
in {FStar_Tc_Env.solver = _53_2258.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_2258.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_2258.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_2258.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_2258.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_2258.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_2258.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_2258.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _53_2258.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_2258.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_2258.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_2258.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_2258.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_2258.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_2258.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_2258.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_2258.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_2258.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_2258.FStar_Tc_Env.default_effects})
in (let expected_pat_t = (FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _53_2263 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_835 = (FStar_Absyn_Print.exp_to_string e)
in (let _155_834 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _155_835 _155_834)))
end else begin
()
end
in (let _53_2268 = (tc_exp env1 e)
in (match (_53_2268) with
| (e, lc, g) -> begin
(let _53_2269 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_837 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _155_836 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _155_837 _155_836)))
end else begin
()
end
in (let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (FStar_Tc_Rel.conj_guard g g')
in (let _53_2273 = (let _155_838 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _155_838))
in (let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (let _53_2276 = if (let _155_841 = (let _155_840 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _155_839 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _155_840 _155_839)))
in (FStar_All.pipe_left Prims.op_Negation _155_841)) then begin
(let _155_846 = (let _155_845 = (let _155_844 = (let _155_843 = (FStar_Absyn_Print.exp_to_string e')
in (let _155_842 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _155_843 _155_842)))
in (_155_844, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_155_845))
in (Prims.raise _155_846))
end else begin
()
end
in (let _53_2278 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_847 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _155_847))
end else begin
()
end
in e)))))))
end))))))
in (let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (let _53_2289 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _53_12 -> (match (_53_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _155_850 = (FStar_Absyn_Print.strBvd x)
in (let _155_849 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _155_850 _155_849)))
end
| _53_2288 -> begin
()
end))))
end else begin
()
end
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _53_2296 = (tc_pat true pat_t pattern)
in (match (_53_2296) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _53_2306 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(let _53_2303 = (let _155_851 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _155_851 e))
in (match (_53_2303) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_53_2306) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _155_853 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _155_852 -> Some (_155_852)) _155_853))
end)
in (let _53_2314 = (tc_exp pat_env branch)
in (match (_53_2314) with
| (branch, c, g_branch) -> begin
(let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _53_2319 = (FStar_All.pipe_right (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t)))) FStar_Tc_Env.clear_expected_typ)
in (match (_53_2319) with
| (scrutinee_env, _53_2318) -> begin
(let c = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _53_2333 -> begin
(let clause = (let _155_857 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _155_856 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _155_857 _155_856 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _155_859 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _155_858 -> Some (_155_858)) _155_859))
end))
end))) None))
in (let c = (match ((eqs, when_condition)) with
| (None, None) -> begin
c
end
| (Some (f), None) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (f)))
end
| (Some (f), Some (w)) -> begin
(let _155_862 = (let _155_861 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _155_860 -> FStar_Tc_Rel.NonTrivial (_155_860)) _155_861))
in (FStar_Tc_Util.weaken_precondition env c _155_862))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun scrutinee f -> (let disc = (let _155_868 = (let _155_867 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _155_867))
in (FStar_All.pipe_left _155_868 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (let disc = (let _155_871 = (let _155_870 = (let _155_869 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_155_869)::[])
in (disc, _155_870))
in (FStar_Absyn_Syntax.mk_Exp_app _155_871 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun scrutinee pat_exp -> (let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_53_2391) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (FStar_Absyn_Util.teq, ((FStar_Absyn_Syntax.varg scrutinee))::((FStar_Absyn_Syntax.varg pat_exp))::[]) None scrutinee.FStar_Absyn_Syntax.pos)
end
| FStar_Absyn_Syntax.Exp_fvar (f, _53_2395) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _53_2408); FStar_Absyn_Syntax.tk = _53_2405; FStar_Absyn_Syntax.pos = _53_2403; FStar_Absyn_Syntax.fvs = _53_2401; FStar_Absyn_Syntax.uvs = _53_2399}, args) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _155_881 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_53_2419) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in (let sub_term = (let _155_879 = (let _155_878 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (_155_878, ((FStar_Absyn_Syntax.varg scrutinee))::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _155_879 None f.FStar_Absyn_Syntax.p))
in (let _155_880 = (mk_guard sub_term ei)
in (_155_880)::[])))
end))))
in (FStar_All.pipe_right _155_881 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _53_2427 -> begin
(let _155_884 = (let _155_883 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _155_882 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _155_883 _155_882)))
in (FStar_All.failwith _155_884))
end)))
in (let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(let t = (mk_guard s pat)
in (let _53_2436 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_53_2436) with
| (t, _53_2435) -> begin
t
end)))
end)
in (let path_guard = (let _155_893 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _155_892 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _155_892)))))
in (FStar_All.pipe_right _155_893 FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _155_894 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _155_894))
in (let _53_2444 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _155_895 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _155_895))
end else begin
()
end
in (let _155_897 = (let _155_896 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _155_896))
in ((pattern, when_clause, branch), path_guard, c, _155_897))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let _53_2450 = (tc_kind env k)
in (match (_53_2450) with
| (k, g) -> begin
(let _53_2451 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd) = (fun env t -> (let _53_2458 = (tc_typ env t)
in (match (_53_2458) with
| (t, k, g) -> begin
(let _53_2459 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env t k -> (let _53_2466 = (tc_typ_check env t k)
in (match (_53_2466) with
| (t, f) -> begin
(let _53_2467 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (let _53_2474 = (tc_exp env e)
in (match (_53_2474) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _155_907 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _155_907 (norm_c env)))
in (match ((let _155_908 = (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) (FStar_Tc_Env.get_range env))
in (FStar_Tc_Rel.sub_comp env c _155_908))) with
| Some (g') -> begin
(let _155_909 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _155_909))
end
| _53_2480 -> begin
(let _155_912 = (let _155_911 = (let _155_910 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_155_910, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_911))
in (Prims.raise _155_912))
end)))
end
end)))
and tc_ghost_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (let _53_2486 = (tc_exp env e)
in (match (_53_2486) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let c = (let _155_915 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _155_915 (norm_c env)))
in (let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (let _53_2490 = env
in {FStar_Tc_Env.solver = _53_2490.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_2490.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_2490.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_2490.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_2490.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_2490.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_2490.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_2490.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_2490.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_2490.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_2490.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_2490.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_2490.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_2490.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_2490.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_2490.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _53_2490.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_2490.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_2490.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _155_916 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _155_916))
end
| _53_2495 -> begin
(let _155_919 = (let _155_918 = (let _155_917 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_155_917, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_155_918))
in (Prims.raise _155_919))
end))))
end
end)))

# 1393 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let tc_tparams : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env) = (fun env tps -> (let _53_2501 = (tc_binders env tps)
in (match (_53_2501) with
| (tps, env, g) -> begin
(let _53_2502 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

# 1400 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let a_kwp_a : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _53_2521)::(FStar_Util.Inl (wp), _53_2516)::(FStar_Util.Inl (_53_2508), _53_2511)::[], _53_2525) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _53_2529 -> begin
(let _155_932 = (let _155_931 = (let _155_930 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (_155_930, (FStar_Ident.range_of_lid m)))
in FStar_Absyn_Syntax.Error (_155_931))
in (Prims.raise _155_932))
end))

# 1406 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let rec tc_eff_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.eff_decl = (fun env m -> (let _53_2535 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_53_2535) with
| (binders, env, g) -> begin
(let _53_2536 = (FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (let _53_2541 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_53_2541) with
| (a, kwp_a) -> begin
(let a_typ = (FStar_Absyn_Util.btvar_to_typ a)
in (let b = (FStar_Absyn_Util.gen_bvar_p (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname) FStar_Absyn_Syntax.ktype)
in (let b_typ = (FStar_Absyn_Util.btvar_to_typ b)
in (let kwp_b = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (let kwlp_a = kwp_a
in (let kwlp_b = kwp_b
in (let a_kwp_b = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_v_binder a_typ))::[], kwp_b) a_typ.FStar_Absyn_Syntax.pos)
in (let a_kwlp_b = a_kwp_b
in (let w = (fun k -> (k (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname)))
in (let ret = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_v_binder a_typ))::[], kwp_a)))
in (let _155_951 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _155_951 (norm_t env))))
in (let bind_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder a_kwp_b))::((FStar_Absyn_Syntax.null_t_binder a_kwlp_b))::[], kwp_b)))
in (let _155_953 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _155_953 (norm_t env))))
in (let bind_wlp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder a_kwlp_b))::[], kwlp_b)))
in (let _155_955 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _155_955 (norm_t env))))
in (let if_then_else = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _155_957 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _155_957 (norm_t env))))
in (let ite_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _155_959 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _155_959 (norm_t env))))
in (let ite_wlp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::[], kwlp_a)))
in (let _155_961 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _155_961 (norm_t env))))
in (let wp_binop = (let expected_k = (let _155_969 = (let _155_968 = (let _155_967 = (let _155_966 = (let _155_965 = (let _155_964 = (let _155_963 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _155_963))
in (_155_964)::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[])
in ((FStar_Absyn_Syntax.null_t_binder kwp_a))::_155_965)
in ((FStar_Absyn_Syntax.t_binder a))::_155_966)
in (_155_967, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _155_968))
in (FStar_All.pipe_left w _155_969))
in (let _155_970 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _155_970 (norm_t env))))
in (let wp_as_type = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], FStar_Absyn_Syntax.ktype)))
in (let _155_972 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _155_972 (norm_t env))))
in (let close_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder a_kwp_b))::[], kwp_b)))
in (let _155_974 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _155_974 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _155_982 = (let _155_981 = (let _155_980 = (let _155_979 = (let _155_978 = (let _155_977 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype))::[], kwp_a)))
in (FStar_Absyn_Syntax.null_t_binder _155_977))
in (_155_978)::[])
in ((FStar_Absyn_Syntax.t_binder a))::_155_979)
in (_155_980, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _155_981))
in (FStar_All.pipe_left w _155_982))
in (let _155_983 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _155_983 (norm_t env))))
in (let _53_2575 = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _155_988 = (let _155_985 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _155_985 (norm_t env)))
in (let _155_987 = (let _155_986 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _155_986 (norm_t env)))
in (_155_988, _155_987))))
in (match (_53_2575) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::[], kwp_a)))
in (let _155_990 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _155_990 (norm_t env))))
in (let trivial_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], FStar_Absyn_Syntax.ktype)))
in (let _155_992 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _155_992 (norm_t env))))
in {FStar_Absyn_Syntax.mname = m.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = m.FStar_Absyn_Syntax.qualifiers; FStar_Absyn_Syntax.signature = mk; FStar_Absyn_Syntax.ret = ret; FStar_Absyn_Syntax.bind_wp = bind_wp; FStar_Absyn_Syntax.bind_wlp = bind_wlp; FStar_Absyn_Syntax.if_then_else = if_then_else; FStar_Absyn_Syntax.ite_wp = ite_wp; FStar_Absyn_Syntax.ite_wlp = ite_wlp; FStar_Absyn_Syntax.wp_binop = wp_binop; FStar_Absyn_Syntax.wp_as_type = wp_as_type; FStar_Absyn_Syntax.close_wp = close_wp; FStar_Absyn_Syntax.close_wp_t = close_wp_t; FStar_Absyn_Syntax.assert_p = assert_p; FStar_Absyn_Syntax.assume_p = assume_p; FStar_Absyn_Syntax.null_wp = null_wp; FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.bool  ->  (FStar_Absyn_Syntax.sigelt * FStar_Tc_Env.env) = (fun env se deserialized -> (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (p, r) -> begin
(match (p) with
| FStar_Absyn_Syntax.SetOptions (o) -> begin
(match ((FStar_Options.set_options o)) with
| FStar_Getopt.GoOn -> begin
(se, env)
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end)
end
| FStar_Absyn_Syntax.ResetOptions -> begin
(let _53_2594 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _53_2596 = (let _155_996 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _155_996 Prims.ignore))
in (se, env)))
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, r) -> begin
(let ne = (tc_eff_decl env ne)
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ne, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, r) -> begin
(let _53_2611 = (let _155_997 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _155_997))
in (match (_53_2611) with
| (a, kwp_a_src) -> begin
(let _53_2614 = (let _155_998 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _155_998))
in (match (_53_2614) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _155_1002 = (let _155_1001 = (let _155_1000 = (let _155_999 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _155_999))
in FStar_Util.Inl (_155_1000))
in (_155_1001)::[])
in (FStar_Absyn_Util.subst_kind _155_1002 kwp_b_tgt))
in (let expected_k = (FStar_All.pipe_right r (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a_src))::[], kwp_a_tgt)))
in (let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _53_2618 = sub
in {FStar_Absyn_Syntax.source = _53_2618.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _53_2618.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _53_2635 = (tc_tparams env tps)
in (match (_53_2635) with
| (tps, env) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _53_2638 -> begin
(tc_kind_trivial env k)
end)
in (let _53_2640 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _155_1005 = (FStar_Absyn_Print.sli lid)
in (let _155_1004 = (let _155_1003 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _155_1003))
in (FStar_Util.print2 "Checked %s at kind %s\n" _155_1005 _155_1004)))
end else begin
()
end
in (let k = (norm_k env k)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _53_2658 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_53_2653); FStar_Absyn_Syntax.tk = _53_2651; FStar_Absyn_Syntax.pos = _53_2649; FStar_Absyn_Syntax.fvs = _53_2647; FStar_Absyn_Syntax.uvs = _53_2645} -> begin
(let _155_1006 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _155_1006))
end
| _53_2657 -> begin
()
end)
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _53_2671 = (tc_tparams env tps)
in (match (_53_2671) with
| (tps, env) -> begin
(let k = (tc_kind_trivial env k)
in (let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r))
in (let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, tps, c, tags, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _53_2686 = (tc_tparams env tps)
in (match (_53_2686) with
| (tps, env) -> begin
(let _53_2689 = (tc_comp env c)
in (match (_53_2689) with
| (c, g) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _53_13 -> (match (_53_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _155_1009 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _155_1008 -> Some (_155_1008)))
in FStar_Absyn_Syntax.DefaultEffect (_155_1009)))
end
| t -> begin
t
end))))
in (let se = FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, tps, c, tags, r))
in (let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))
end))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _53_2709 = (tc_tparams env tps)
in (match (_53_2709) with
| (tps, env') -> begin
(let _53_2715 = (let _155_1013 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _155_1013 (fun _53_2712 -> (match (_53_2712) with
| (t, k) -> begin
(let _155_1012 = (norm_t env' t)
in (let _155_1011 = (norm_k env' k)
in (_155_1012, _155_1011)))
end))))
in (match (_53_2715) with
| (t, k1) -> begin
(let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _53_2718 -> begin
(let k2 = (let _155_1014 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _155_1014 (norm_k env)))
in (let _53_2720 = (let _155_1015 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _155_1015))
in k2))
end)
in (let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k2, t, tags, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end))
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, (tname, tps, k), quals, mutuals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _53_2740 = (tc_binders env tps)
in (match (_53_2740) with
| (tps, env, g) -> begin
(let tycon = (tname, tps, k)
in (let _53_2742 = (FStar_Tc_Util.discharge_guard env g)
in (let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _53_2754 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _53_2751 -> begin
([], t)
end)
in (match (_53_2754) with
| (formals, result_t) -> begin
(let cardinality_and_positivity_check = (fun formal -> (let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _53_2762 -> (match (_53_2762) with
| (a, _53_2761) -> begin
(match (a) with
| FStar_Util.Inl (_53_2764) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _155_1023 = (FStar_Absyn_Util.compress_typ t)
in _155_1023.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _155_1027 = (let _155_1026 = (let _155_1025 = (let _155_1024 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _155_1024 tname))
in (_155_1025, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_155_1026))
in (Prims.raise _155_1027))
end)
end
| _53_2777 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(let _53_2780 = if (FStar_Options.warn_cardinality ()) then begin
(let _155_1028 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _155_1028))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _155_1031 = (let _155_1030 = (let _155_1029 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_155_1029, r))
in FStar_Absyn_Syntax.Error (_155_1030))
in (Prims.raise _155_1031))
end else begin
()
end
end
in (let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_53_2784) -> begin
(let _53_2789 = (FStar_Absyn_Util.kind_formals k)
in (match (_53_2789) with
| (formals, _53_2788) -> begin
(check_positivity formals)
end))
end
| _53_2791 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(let _53_2798 = (let _155_1032 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _155_1032 FStar_Util.must))
in (match (_53_2798) with
| (formals, _53_2797) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (let _53_2799 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (let _53_2853 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _155_1036 = (let _155_1035 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _155_1035 Prims.fst))
in (FStar_List.forall2 (fun _53_2806 _53_2810 -> (match ((_53_2806, _53_2810)) with
| ((a, _53_2805), (b, _53_2809)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _53_2818; FStar_Absyn_Syntax.pos = _53_2816; FStar_Absyn_Syntax.fvs = _53_2814; FStar_Absyn_Syntax.uvs = _53_2812}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _53_2833; FStar_Absyn_Syntax.pos = _53_2831; FStar_Absyn_Syntax.fvs = _53_2829; FStar_Absyn_Syntax.uvs = _53_2827}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _53_2842 -> begin
false
end)
end)) _155_1036 tps))))) then begin
(let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _53_2845 -> begin
(let _53_2849 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_53_2849) with
| (_53_2847, expected_args) -> begin
(let _155_1037 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _155_1037 expected_args))
end))
end)
in (let _155_1041 = (let _155_1040 = (let _155_1039 = (let _155_1038 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _155_1038 result_t expected_t))
in (_155_1039, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_155_1040))
in (Prims.raise _155_1041)))
end else begin
()
end
end
| _53_2852 -> begin
(let _155_1046 = (let _155_1045 = (let _155_1044 = (let _155_1043 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _155_1042 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _155_1043 result_t _155_1042)))
in (_155_1044, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_155_1045))
in (Prims.raise _155_1046))
end)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _53_2857 = if (log env) then begin
(let _155_1048 = (let _155_1047 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _155_1047))
in (FStar_All.pipe_left FStar_Util.print_string _155_1048))
end else begin
()
end
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let t = (let _155_1049 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _155_1049 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _53_2867 = (FStar_Tc_Util.check_uvars r t)
in (let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _53_2871 = if (log env) then begin
(let _155_1051 = (let _155_1050 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _155_1050))
in (FStar_All.pipe_left FStar_Util.print_string _155_1051))
end else begin
()
end
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let phi = (let _155_1052 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _155_1052 (norm_t env)))
in (let _53_2881 = (FStar_Tc_Util.check_uvars r phi)
in (let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _53_2934 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _53_2894 lb -> (match (_53_2894) with
| (gen, lbs) -> begin
(let _53_2931 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_53_2903); FStar_Absyn_Syntax.lbtyp = _53_2901; FStar_Absyn_Syntax.lbeff = _53_2899; FStar_Absyn_Syntax.lbdef = _53_2897} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _53_2908; FStar_Absyn_Syntax.lbdef = e} -> begin
(let _53_2928 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _53_2916) -> begin
(let _53_2919 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _155_1055 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _155_1055 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(false, (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e)))
end
| _53_2923 -> begin
(let _53_2924 = if (not (deserialized)) then begin
(let _155_1057 = (let _155_1056 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _155_1056))
in (FStar_All.pipe_left FStar_Util.print_string _155_1057))
end else begin
()
end
in (false, (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))))
end))
end)
in (match (_53_2928) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_53_2931) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_53_2934) with
| (generalize, lbs') -> begin
(let lbs' = (FStar_List.rev lbs')
in (let e = (let _155_1061 = (let _155_1060 = (FStar_All.pipe_left (syn' env FStar_Tc_Recheck.t_unit) (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit))
in (((Prims.fst lbs), lbs'), _155_1060))
in (FStar_Absyn_Syntax.mk_Exp_let _155_1061 None r))
in (let _53_2969 = (match ((tc_exp (let _53_2937 = env
in {FStar_Tc_Env.solver = _53_2937.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_2937.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_2937.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_2937.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_2937.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_2937.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_2937.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_2937.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_2937.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_2937.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_2937.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_2937.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _53_2937.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_2937.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_2937.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_2937.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _53_2937.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _53_2937.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _53_2937.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _53_2946; FStar_Absyn_Syntax.pos = _53_2944; FStar_Absyn_Syntax.fvs = _53_2942; FStar_Absyn_Syntax.uvs = _53_2940}, _53_2953, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_53_2957, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _53_2963 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _53_2966 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_2969) with
| (se, lbs) -> begin
(let _53_2975 = if (log env) then begin
(let _155_1067 = (let _155_1066 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _155_1063 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _155_1063))) with
| None -> begin
true
end
| _53_2973 -> begin
false
end)
in if should_log then begin
(let _155_1065 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _155_1064 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _155_1065 _155_1064)))
end else begin
""
end))))
in (FStar_All.pipe_right _155_1066 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _155_1067))
end else begin
()
end
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))
end))))
end)))
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let env = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (let _53_2987 = (tc_exp env e)
in (match (_53_2987) with
| (e, c, g1) -> begin
(let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _53_2993 = (let _155_1071 = (let _155_1068 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_155_1068))
in (let _155_1070 = (let _155_1069 = (c.FStar_Absyn_Syntax.comp ())
in (e, _155_1069))
in (check_expected_effect env _155_1071 _155_1070)))
in (match (_53_2993) with
| (e, _53_2991, g) -> begin
(let _53_2994 = (let _155_1072 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _155_1072))
in (let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _53_3013 = (FStar_All.pipe_right ses (FStar_List.partition (fun _53_14 -> (match (_53_14) with
| FStar_Absyn_Syntax.Sig_tycon (_53_3007) -> begin
true
end
| _53_3010 -> begin
false
end))))
in (match (_53_3013) with
| (tycons, rest) -> begin
(let _53_3022 = (FStar_All.pipe_right rest (FStar_List.partition (fun _53_15 -> (match (_53_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_53_3016) -> begin
true
end
| _53_3019 -> begin
false
end))))
in (match (_53_3022) with
| (abbrevs, rest) -> begin
(let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _53_16 -> (match (_53_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _155_1076 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _155_1076 Prims.fst))
end
| _53_3034 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _53_3037 -> begin
(FStar_All.failwith "impossible")
end))))
in (let _53_3041 = (FStar_List.split recs)
in (match (_53_3041) with
| (recs, abbrev_defs) -> begin
(let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _155_1077 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _155_1077))
end else begin
""
end
in (let _53_3043 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (let _53_3048 = (tc_decls env tycons deserialized)
in (match (_53_3048) with
| (tycons, _53_3047) -> begin
(let _53_3052 = (tc_decls env recs deserialized)
in (match (_53_3052) with
| (recs, _53_3051) -> begin
(let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (let _53_3057 = (tc_decls env1 rest deserialized)
in (match (_53_3057) with
| (rest, _53_3056) -> begin
(let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(let tt = (let _155_1080 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _155_1080))
in (let _53_3073 = (tc_typ_trivial env1 tt)
in (match (_53_3073) with
| (tt, _53_3072) -> begin
(let _53_3082 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _53_3079 -> begin
([], tt)
end)
in (match (_53_3082) with
| (tps, t) -> begin
(let _155_1082 = (let _155_1081 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _155_1081, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_155_1082))
end))
end)))
end
| _53_3084 -> begin
(let _155_1084 = (let _155_1083 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _155_1083))
in (FStar_All.failwith _155_1084))
end)) recs abbrev_defs)
in (let _53_3086 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
in (let se = FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append (FStar_List.append tycons abbrevs) rest), quals, lids, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))
end)))
end))
end))))
end)))
end))
end)))
end))
and tc_decls : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.bool  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Tc_Env.env) = (fun env ses deserialized -> (let time_tc_decl = (fun env se ds -> (let start = (FStar_Util.now ())
in (let res = (tc_decl env se ds)
in (let stop = (FStar_Util.now ())
in (let diff = (FStar_Util.time_diff start stop)
in (let _53_3101 = (let _155_1094 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _155_1094))
in res))))))
in (let _53_3116 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _53_3105 se -> (match (_53_3105) with
| (ses, env) -> begin
(let _53_3107 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _155_1098 = (let _155_1097 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _155_1097))
in (FStar_Util.print_string _155_1098))
end else begin
()
end
in (let _53_3111 = if (FStar_ST.read FStar_Options.timing) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_53_3111) with
| (se, env) -> begin
(let _53_3112 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in ((se)::ses, env))
end)))
end)) ([], env)))
in (match (_53_3116) with
| (ses, env) -> begin
((FStar_List.rev ses), env)
end))))

# 1785 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let rec for_export : FStar_Tc_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_17 -> (match (_53_17) with
| FStar_Absyn_Syntax.Abstract -> begin
true
end
| _53_3125 -> begin
false
end)))))
in (let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Absyn_Syntax.Projector (l, _)) | (FStar_Absyn_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _53_3135 -> begin
false
end))
in (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (_53_3137) -> begin
([], hidden)
end
| FStar_Absyn_Syntax.Sig_datacon (_53_3140) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, binders, knd, def, quals, r) -> begin
if (is_abstract quals) then begin
(let se = FStar_Absyn_Syntax.Sig_tycon ((lid, binders, knd, [], [], (FStar_Absyn_Syntax.Assumption)::quals, r))
in ((se)::[], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _53_3160, _53_3162) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _53_3168 -> (match (_53_3168) with
| (out, hidden) -> begin
(match (se) with
| FStar_Absyn_Syntax.Sig_tycon (l, bs, t, _53_3173, _53_3175, quals, r) -> begin
(let dec = FStar_Absyn_Syntax.Sig_tycon ((l, bs, t, [], [], quals, r))
in ((dec)::out, hidden))
end
| FStar_Absyn_Syntax.Sig_datacon (l, t, _tc, quals, _mutuals, r) -> begin
(let t = (FStar_Tc_Env.lookup_datacon env l)
in (let dec = FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden)))
end
| se -> begin
(for_export env hidden se)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Absyn_Syntax.Sig_assume (_53_3193, _53_3195, quals, _53_3198) -> begin
if (is_abstract quals) then begin
([], hidden)
end else begin
((se)::[], hidden)
end
end
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
((FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::[], r)))::[], (l)::hidden)
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_18 -> (match (_53_18) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _53_3216 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Absyn_Syntax.Sig_main (_53_3218) -> begin
([], hidden)
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_let ((false, lb::[]), _53_3234, _53_3236, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(let lid = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(let dec = FStar_Absyn_Syntax.Sig_val_decl ((lid, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _155_1116 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _155_1115 = (let _155_1114 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_155_1114, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::quals, r))
in FStar_Absyn_Syntax.Sig_val_decl (_155_1115)))))
in (_155_1116, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 1876 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let get_exports : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env modul -> (let _53_3261 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.fold_left (fun _53_3253 se -> (match (_53_3253) with
| (exports, hidden) -> begin
(let _53_3257 = (for_export env hidden se)
in (match (_53_3257) with
| (exports', hidden) -> begin
((exports')::exports, hidden)
end))
end)) ([], [])))
in (match (_53_3261) with
| (exports, _53_3260) -> begin
(FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
end)))

# 1964 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let tc_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (let msg = (Prims.strcat "Internals for " name)
in (let env = (let _53_3266 = env
in (let _155_1127 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _53_3266.FStar_Tc_Env.solver; FStar_Tc_Env.range = _53_3266.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _53_3266.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _53_3266.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _53_3266.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _53_3266.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _53_3266.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _53_3266.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _53_3266.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _53_3266.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _53_3266.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _53_3266.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _53_3266.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _53_3266.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _53_3266.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _53_3266.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _53_3266.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _155_1127; FStar_Tc_Env.default_effects = _53_3266.FStar_Tc_Env.default_effects}))
in (let _53_3269 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (let _53_3274 = (tc_decls env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_53_3274) with
| (ses, env) -> begin
((let _53_3275 = modul
in {FStar_Absyn_Syntax.name = _53_3275.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _53_3275.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _53_3275.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _53_3275.FStar_Absyn_Syntax.is_deserialized}), env)
end))))))))

# 1973 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let tc_more_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul decls -> (let _53_3282 = (tc_decls env decls false)
in (match (_53_3282) with
| (ses, env) -> begin
(let modul = (let _53_3283 = modul
in {FStar_Absyn_Syntax.name = _53_3283.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _53_3283.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _53_3283.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _53_3283.FStar_Absyn_Syntax.is_deserialized})
in (modul, env))
end)))

# 1978 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let finish_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (let exports = (get_exports env modul)
in (let modul = (let _53_3289 = modul
in {FStar_Absyn_Syntax.name = _53_3289.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _53_3289.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (let env = (FStar_Tc_Env.finish_module env modul)
in (let _53_3299 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(let _53_3293 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (let _53_3295 = if ((not (modul.FStar_Absyn_Syntax.is_interface)) || (let _155_1138 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Absyn_Syntax.name.FStar_Ident.str _155_1138))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
end else begin
()
end
in (let _53_3297 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _155_1139 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _155_1139 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

# 1993 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let tc_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (let _53_3305 = (tc_partial_modul env modul)
in (match (_53_3305) with
| (modul, env) -> begin
(finish_partial_modul env modul)
end)))

# 1997 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let add_modul_to_tcenv : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Tc_Env.env = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_Tc_Env.push_sigelt en elt)
in (let _53_3312 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _155_1152 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _155_1152 m)))))

# 2006 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\tc\\tc.fs"

let check_module : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env) = (fun env m -> (let _53_3317 = if ((let _155_1157 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _155_1157)) <> 0) then begin
(let _155_1158 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _155_1158))
end else begin
()
end
in (let _53_3330 = if m.FStar_Absyn_Syntax.is_deserialized then begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end else begin
(let _53_3322 = (tc_modul env m)
in (match (_53_3322) with
| (m, env) -> begin
(let _53_3326 = if (FStar_ST.read FStar_Options.serialize_mods) then begin
(let c_file_name = (let _155_1163 = (let _155_1162 = (let _155_1161 = (let _155_1160 = (let _155_1159 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _155_1159 "/"))
in (Prims.strcat _155_1160 FStar_Options.cache_dir))
in (Prims.strcat _155_1161 "/"))
in (Prims.strcat _155_1162 (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)))
in (Prims.strcat _155_1163 ".cache"))
in (let _53_3324 = (FStar_Util.print_string (Prims.strcat (Prims.strcat "Serializing module " (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)) "\n"))
in (let _155_1164 = (FStar_Util.get_owriter c_file_name)
in (FStar_Absyn_SSyntax.serialize_modul _155_1164 m))))
end else begin
()
end
in (m, env))
end))
end
in (match (_53_3330) with
| (m, env) -> begin
(let _53_3331 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _155_1165 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _155_1165))
end else begin
()
end
in ((m)::[], env))
end))))




