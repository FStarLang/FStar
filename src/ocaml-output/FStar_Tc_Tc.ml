
open Prims
# 30 "FStar.Tc.Tc.fst"
let syn' = (fun env k -> (let _115_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _115_11 (Some (k)))))

# 31 "FStar.Tc.Tc.fst"
let log : FStar_Tc_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _115_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _115_14))))))

# 32 "FStar.Tc.Tc.fst"
let rng : FStar_Tc_Env.env  ->  FStar_Range.range = (fun env -> (FStar_Tc_Env.get_range env))

# 33 "FStar.Tc.Tc.fst"
let instantiate_both : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (
# 33 "FStar.Tc.Tc.fst"
let _36_24 = env
in {FStar_Tc_Env.solver = _36_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _36_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_24.FStar_Tc_Env.default_effects}))

# 34 "FStar.Tc.Tc.fst"
let no_inst : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (
# 34 "FStar.Tc.Tc.fst"
let _36_27 = env
in {FStar_Tc_Env.solver = _36_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _36_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_27.FStar_Tc_Env.default_effects}))

# 35 "FStar.Tc.Tc.fst"
let mk_lex_list : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 37 "FStar.Tc.Tc.fst"
let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _115_34 = (let _115_33 = (let _115_32 = (let _115_27 = (let _115_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _115_25 -> FStar_Util.Inl (_115_25)) _115_26))
in (_115_27, Some (FStar_Absyn_Syntax.Implicit (false))))
in (let _115_31 = (let _115_30 = (FStar_Absyn_Syntax.varg v)
in (let _115_29 = (let _115_28 = (FStar_Absyn_Syntax.varg tl)
in (_115_28)::[])
in (_115_30)::_115_29))
in (_115_32)::_115_31))
in (FStar_Absyn_Util.lex_pair, _115_33))
in (FStar_Absyn_Syntax.mk_Exp_app _115_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

# 39 "FStar.Tc.Tc.fst"
let is_eq : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _36_1 -> (match (_36_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _36_37 -> begin
false
end))

# 42 "FStar.Tc.Tc.fst"
let steps : FStar_Tc_Env.env  ->  FStar_Tc_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)

# 46 "FStar.Tc.Tc.fst"
let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))

# 47 "FStar.Tc.Tc.fst"
let norm_t : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _115_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _115_47 env t)))

# 48 "FStar.Tc.Tc.fst"
let norm_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let _115_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _115_52 env k)))

# 49 "FStar.Tc.Tc.fst"
let norm_c : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun env c -> (let _115_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _115_57 env c)))

# 50 "FStar.Tc.Tc.fst"
let fxv_check : FStar_Absyn_Syntax.exp  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either  ->  (FStar_Absyn_Syntax.bvvar Prims.list * (FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.bvvar  ->  Prims.bool))  ->  Prims.unit = (fun head env kt fvs -> (
# 51 "FStar.Tc.Tc.fst"
let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(
# 53 "FStar.Tc.Tc.fst"
let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _115_76 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _115_76))
end
| FStar_Util.Inr (t) -> begin
(let _115_77 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _115_77))
end)
in (
# 56 "FStar.Tc.Tc.fst"
let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (norm)) then begin
(aux true kt)
end else begin
(
# 61 "FStar.Tc.Tc.fst"
let fail = (fun _36_61 -> (match (()) with
| () -> begin
(
# 62 "FStar.Tc.Tc.fst"
let escaping = (let _115_82 = (let _115_81 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _115_81 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _115_82 (FStar_String.concat ", ")))
in (
# 63 "FStar.Tc.Tc.fst"
let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _115_83 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _115_83))
end else begin
(let _115_84 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _115_84))
end
in (let _115_87 = (let _115_86 = (let _115_85 = (FStar_Tc_Env.get_range env)
in (msg, _115_85))
in FStar_Absyn_Syntax.Error (_115_86))
in (Prims.raise _115_87))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(
# 69 "FStar.Tc.Tc.fst"
let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _36_71 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(
# 76 "FStar.Tc.Tc.fst"
let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _36_78 -> begin
(fail ())
end))
end))
end
end))
end)
in (aux false kt)))

# 84 "FStar.Tc.Tc.fst"
let maybe_push_binding : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binder  ->  FStar_Tc_Env.env = (fun env b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
env
end else begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(
# 88 "FStar.Tc.Tc.fst"
let b = FStar_Tc_Env.Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
in (FStar_Tc_Env.push_local_binding env b))
end
| FStar_Util.Inr (x) -> begin
(
# 91 "FStar.Tc.Tc.fst"
let b = FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
in (FStar_Tc_Env.push_local_binding env b))
end)
end)

# 94 "FStar.Tc.Tc.fst"
let maybe_make_subst = (fun _36_2 -> (match (_36_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _36_99 -> begin
[]
end))

# 99 "FStar.Tc.Tc.fst"
let maybe_alpha_subst = (fun s b1 b2 -> if (FStar_Absyn_Syntax.is_null_binder b1) then begin
s
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (FStar_Absyn_Util.bvar_eq a b) then begin
s
end else begin
(let _115_98 = (let _115_97 = (let _115_96 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _115_96))
in FStar_Util.Inl (_115_97))
in (_115_98)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _115_101 = (let _115_100 = (let _115_99 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _115_99))
in FStar_Util.Inr (_115_100))
in (_115_101)::s)
end
end
| _36_114 -> begin
(FStar_All.failwith "impossible")
end)
end)

# 106 "FStar.Tc.Tc.fst"
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
| _36_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

# 113 "FStar.Tc.Tc.fst"
let set_lcomp_result : FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.lcomp = (fun lc t -> (
# 114 "FStar.Tc.Tc.fst"
let _36_132 = lc
in {FStar_Absyn_Syntax.eff_name = _36_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _36_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _36_134 -> (match (()) with
| () -> begin
(let _115_110 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _115_110 t))
end))}))

# 116 "FStar.Tc.Tc.fst"
let value_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, FStar_Absyn_Syntax.lcomp) FStar_Util.either  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e tlc -> (
# 117 "FStar.Tc.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _115_117 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _115_117))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 122 "FStar.Tc.Tc.fst"
let t = lc.FStar_Absyn_Syntax.res_typ
in (
# 123 "FStar.Tc.Tc.fst"
let _36_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(
# 126 "FStar.Tc.Tc.fst"
let _36_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_119 = (FStar_Absyn_Print.typ_to_string t)
in (let _115_118 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _115_119 _115_118)))
end else begin
()
end
in (
# 128 "FStar.Tc.Tc.fst"
let _36_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_36_151) with
| (e, g) -> begin
(
# 129 "FStar.Tc.Tc.fst"
let _36_154 = (let _115_125 = (FStar_All.pipe_left (fun _115_124 -> Some (_115_124)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _115_125 env e lc g))
in (match (_36_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_36_158) with
| (e, lc, g) -> begin
(
# 131 "FStar.Tc.Tc.fst"
let _36_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_126 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _115_126))
end else begin
()
end
in (e, lc, g))
end)))))

# 135 "FStar.Tc.Tc.fst"
let comp_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t) -> begin
(FStar_Tc_Util.weaken_result_typ env e lc t)
end))

# 140 "FStar.Tc.Tc.fst"
let check_expected_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp Prims.option  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp)  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env copt _36_171 -> (match (_36_171) with
| (e, c) -> begin
(
# 141 "FStar.Tc.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_36_173) -> begin
copt
end
| None -> begin
(
# 144 "FStar.Tc.Tc.fst"
let c1 = (FStar_Tc_Normalize.weak_norm_comp env c)
in (
# 145 "FStar.Tc.Tc.fst"
let md = (FStar_Tc_Env.get_effect_decl env c1.FStar_Absyn_Syntax.effect_name)
in (match ((FStar_Tc_Env.default_effect env md.FStar_Absyn_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(
# 149 "FStar.Tc.Tc.fst"
let flags = if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_Tot_lid) then begin
(FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals l FStar_Absyn_Const.effect_ML_lid) then begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
in (
# 153 "FStar.Tc.Tc.fst"
let def = (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = flags})
in Some (def)))
end)))
end)
in (match (expected_c_opt) with
| None -> begin
(let _115_139 = (norm_c env c)
in (e, _115_139, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 162 "FStar.Tc.Tc.fst"
let _36_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_142 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _115_141 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _115_140 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _115_142 _115_141 _115_140))))
end else begin
()
end
in (
# 164 "FStar.Tc.Tc.fst"
let c = (norm_c env c)
in (
# 165 "FStar.Tc.Tc.fst"
let expected_c' = (let _115_143 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _115_143))
in (
# 166 "FStar.Tc.Tc.fst"
let _36_195 = (let _115_144 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _115_144))
in (match (_36_195) with
| (e, _36_193, g) -> begin
(
# 167 "FStar.Tc.Tc.fst"
let _36_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_146 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _115_145 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _115_146 _115_145)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

# 170 "FStar.Tc.Tc.fst"
let no_logical_guard = (fun env _36_202 -> (match (_36_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _115_152 = (let _115_151 = (let _115_150 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _115_149 = (FStar_Tc_Env.get_range env)
in (_115_150, _115_149)))
in FStar_Absyn_Syntax.Error (_115_151))
in (Prims.raise _115_152))
end)
end))

# 175 "FStar.Tc.Tc.fst"
let binding_of_lb : (FStar_Absyn_Syntax.bvvdef, FStar_Ident.lident) FStar_Util.either  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.binding = (fun x t -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
FStar_Tc_Env.Binding_var ((bvd, t))
end
| FStar_Util.Inr (lid) -> begin
FStar_Tc_Env.Binding_lid ((lid, t))
end))

# 179 "FStar.Tc.Tc.fst"
let print_expected_ty : FStar_Tc_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _115_159 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _115_159))
end))

# 182 "FStar.Tc.Tc.fst"
let with_implicits = (fun imps _36_220 -> (match (_36_220) with
| (e, l, g) -> begin
(e, l, (
# 182 "FStar.Tc.Tc.fst"
let _36_221 = g
in {FStar_Tc_Rel.guard_f = _36_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _36_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

# 183 "FStar.Tc.Tc.fst"
let add_implicit : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * Prims.int64), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * Prims.int64)) FStar_Util.either  ->  FStar_Tc_Rel.guard_t  ->  FStar_Tc_Rel.guard_t = (fun u g -> (
# 183 "FStar.Tc.Tc.fst"
let _36_225 = g
in {FStar_Tc_Rel.guard_f = _36_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _36_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

# 184 "FStar.Tc.Tc.fst"
let rec tc_kind : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd * FStar_Tc_Rel.guard_t) = (fun env k -> (
# 185 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.compress_kind k)
in (
# 186 "FStar.Tc.Tc.fst"
let w = (fun f -> (f k.FStar_Absyn_Syntax.pos))
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(k, FStar_Tc_Rel.trivial_guard)
end
| FStar_Absyn_Syntax.Kind_uvar (u, args) -> begin
(
# 194 "FStar.Tc.Tc.fst"
let _36_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _115_212 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _115_211 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _115_212 _115_211)))
end else begin
()
end
in (
# 195 "FStar.Tc.Tc.fst"
let _36_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_36_249) with
| (env, _36_248) -> begin
(
# 196 "FStar.Tc.Tc.fst"
let _36_252 = (tc_args env args)
in (match (_36_252) with
| (args, g) -> begin
(let _115_214 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_115_214, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _36_263; FStar_Absyn_Syntax.pos = _36_261; FStar_Absyn_Syntax.fvs = _36_259; FStar_Absyn_Syntax.uvs = _36_257}) -> begin
(
# 200 "FStar.Tc.Tc.fst"
let _36_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_36_272) with
| (_36_269, binders, body) -> begin
(
# 201 "FStar.Tc.Tc.fst"
let _36_275 = (tc_args env args)
in (match (_36_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _115_218 = (let _115_217 = (let _115_216 = (let _115_215 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _115_215))
in (_115_216, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_217))
in (Prims.raise _115_218))
end else begin
(
# 204 "FStar.Tc.Tc.fst"
let _36_308 = (FStar_List.fold_left2 (fun _36_279 b a -> (match (_36_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(
# 207 "FStar.Tc.Tc.fst"
let _36_289 = (let _115_222 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _115_222))
in (match (_36_289) with
| (t, g) -> begin
(
# 208 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _115_224 = (let _115_223 = (FStar_Absyn_Syntax.targ t)
in (_115_223)::args)
in (subst, _115_224, (g)::guards)))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(
# 211 "FStar.Tc.Tc.fst"
let env = (let _115_225 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _115_225))
in (
# 212 "FStar.Tc.Tc.fst"
let _36_301 = (tc_ghost_exp env e)
in (match (_36_301) with
| (e, _36_299, g) -> begin
(
# 213 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (let _115_227 = (let _115_226 = (FStar_Absyn_Syntax.varg e)
in (_115_226)::args)
in (subst, _115_227, (g)::guards)))
end)))
end
| _36_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_36_308) with
| (subst, args, guards) -> begin
(
# 217 "FStar.Tc.Tc.fst"
let args = (FStar_List.rev args)
in (
# 218 "FStar.Tc.Tc.fst"
let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown)))
in (
# 219 "FStar.Tc.Tc.fst"
let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (
# 220 "FStar.Tc.Tc.fst"
let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _115_230 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _115_230))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(
# 224 "FStar.Tc.Tc.fst"
let _36_319 = (tc_kind env k)
in (match (_36_319) with
| (k, f) -> begin
(
# 225 "FStar.Tc.Tc.fst"
let _36_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_36_322) with
| (args, g) -> begin
(
# 226 "FStar.Tc.Tc.fst"
let kabr = ((Prims.fst kabr), args)
in (
# 227 "FStar.Tc.Tc.fst"
let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _115_232 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _115_232))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 231 "FStar.Tc.Tc.fst"
let _36_332 = (tc_binders env bs)
in (match (_36_332) with
| (bs, env, g) -> begin
(
# 232 "FStar.Tc.Tc.fst"
let _36_335 = (tc_kind env k)
in (match (_36_335) with
| (k, f) -> begin
(
# 233 "FStar.Tc.Tc.fst"
let f = (FStar_Tc_Rel.close_guard bs f)
in (let _115_235 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _115_234 = (FStar_Tc_Rel.conj_guard g f)
in (_115_235, _115_234))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _115_236 = (FStar_Tc_Util.new_kvar env)
in (_115_236, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder : FStar_Tc_Env.env  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env x -> (
# 240 "FStar.Tc.Tc.fst"
let _36_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_36_342) with
| (t, g) -> begin
(
# 241 "FStar.Tc.Tc.fst"
let x = (
# 241 "FStar.Tc.Tc.fst"
let _36_343 = x
in {FStar_Absyn_Syntax.v = _36_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _36_343.FStar_Absyn_Syntax.p})
in (
# 242 "FStar.Tc.Tc.fst"
let env' = (let _115_239 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _115_239))
in (x, env', g)))
end)))
and tc_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env bs -> (
# 246 "FStar.Tc.Tc.fst"
let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(
# 251 "FStar.Tc.Tc.fst"
let _36_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_36_362) with
| (k, g) -> begin
(
# 252 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inl ((
# 252 "FStar.Tc.Tc.fst"
let _36_363 = a
in {FStar_Absyn_Syntax.v = _36_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _36_363.FStar_Absyn_Syntax.p})), imp)
in (
# 253 "FStar.Tc.Tc.fst"
let env' = (maybe_push_binding env b)
in (
# 254 "FStar.Tc.Tc.fst"
let _36_370 = (aux env' bs)
in (match (_36_370) with
| (bs, env', g') -> begin
(let _115_247 = (let _115_246 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _115_246))
in ((b)::bs, env', _115_247))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(
# 258 "FStar.Tc.Tc.fst"
let _36_376 = (tc_vbinder env x)
in (match (_36_376) with
| (x, env', g) -> begin
(
# 259 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inr (x), imp)
in (
# 260 "FStar.Tc.Tc.fst"
let _36_381 = (aux env' bs)
in (match (_36_381) with
| (bs, env', g') -> begin
(let _115_249 = (let _115_248 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _115_248))
in ((b)::bs, env', _115_249))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.args * FStar_Tc_Rel.guard_t) = (fun env args -> (FStar_List.fold_right (fun _36_386 _36_389 -> (match ((_36_386, _36_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(
# 268 "FStar.Tc.Tc.fst"
let _36_396 = (tc_typ env t)
in (match (_36_396) with
| (t, _36_394, g') -> begin
(let _115_254 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _115_254))
end))
end
| FStar_Util.Inr (e) -> begin
(
# 271 "FStar.Tc.Tc.fst"
let _36_403 = (tc_ghost_exp env e)
in (match (_36_403) with
| (e, _36_401, g') -> begin
(let _115_255 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _115_255))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list Prims.list  ->  (FStar_Absyn_Syntax.args Prims.list * FStar_Tc_Rel.guard_t) = (fun env pats -> (FStar_List.fold_right (fun p _36_409 -> (match (_36_409) with
| (pats, g) -> begin
(
# 275 "FStar.Tc.Tc.fst"
let _36_412 = (tc_args env p)
in (match (_36_412) with
| (args, g') -> begin
(let _115_260 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _115_260))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 280 "FStar.Tc.Tc.fst"
let _36_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_36_419) with
| (t, g) -> begin
(let _115_263 = (FStar_Absyn_Syntax.mk_Total t)
in (_115_263, g))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(
# 284 "FStar.Tc.Tc.fst"
let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (
# 285 "FStar.Tc.Tc.fst"
let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (
# 286 "FStar.Tc.Tc.fst"
let tc = (let _115_266 = (let _115_265 = (let _115_264 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_115_264)::c.FStar_Absyn_Syntax.effect_args)
in (head, _115_265))
in (FStar_Absyn_Syntax.mk_Typ_app _115_266 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (
# 287 "FStar.Tc.Tc.fst"
let _36_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_36_427) with
| (tc, f) -> begin
(
# 288 "FStar.Tc.Tc.fst"
let _36_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_36_431) with
| (_36_429, args) -> begin
(
# 289 "FStar.Tc.Tc.fst"
let _36_443 = (match (args) with
| (FStar_Util.Inl (res), _36_436)::args -> begin
(res, args)
end
| _36_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_36_443) with
| (res, args) -> begin
(
# 292 "FStar.Tc.Tc.fst"
let _36_459 = (let _115_268 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _36_3 -> (match (_36_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(
# 294 "FStar.Tc.Tc.fst"
let _36_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_36_450) with
| (env, _36_449) -> begin
(
# 295 "FStar.Tc.Tc.fst"
let _36_455 = (tc_ghost_exp env e)
in (match (_36_455) with
| (e, _36_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _115_268 FStar_List.unzip))
in (match (_36_459) with
| (flags, guards) -> begin
(let _115_270 = (FStar_Absyn_Syntax.mk_Comp (
# 298 "FStar.Tc.Tc.fst"
let _36_460 = c
in {FStar_Absyn_Syntax.effect_name = _36_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _36_460.FStar_Absyn_Syntax.flags}))
in (let _115_269 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_115_270, _115_269)))
end))
end))
end))
end)))))
end))
and tc_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.guard_t) = (fun env t -> (
# 303 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (
# 304 "FStar.Tc.Tc.fst"
let w = (fun k -> (FStar_Absyn_Syntax.syn t.FStar_Absyn_Syntax.pos (Some (k))))
in (
# 305 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (
# 306 "FStar.Tc.Tc.fst"
let top = t
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(
# 309 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Env.lookup_btvar env a)
in (
# 310 "FStar.Tc.Tc.fst"
let a = (
# 310 "FStar.Tc.Tc.fst"
let _36_472 = a
in {FStar_Absyn_Syntax.v = _36_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _36_472.FStar_Absyn_Syntax.p})
in (
# 311 "FStar.Tc.Tc.fst"
let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (
# 312 "FStar.Tc.Tc.fst"
let _36_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_36_479) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(
# 317 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Util.new_kvar env)
in (
# 318 "FStar.Tc.Tc.fst"
let qk = (FStar_Absyn_Util.eqT_k k)
in (
# 319 "FStar.Tc.Tc.fst"
let i = (
# 319 "FStar.Tc.Tc.fst"
let _36_484 = i
in {FStar_Absyn_Syntax.v = _36_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _36_484.FStar_Absyn_Syntax.p})
in (let _115_293 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_115_293, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(
# 323 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Util.new_kvar env)
in (
# 324 "FStar.Tc.Tc.fst"
let qk = (FStar_Absyn_Util.allT_k k)
in (
# 325 "FStar.Tc.Tc.fst"
let i = (
# 325 "FStar.Tc.Tc.fst"
let _36_491 = i
in {FStar_Absyn_Syntax.v = _36_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _36_491.FStar_Absyn_Syntax.p})
in (let _115_294 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_115_294, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(
# 329 "FStar.Tc.Tc.fst"
let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _36_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (
# 332 "FStar.Tc.Tc.fst"
let i = (
# 332 "FStar.Tc.Tc.fst"
let _36_501 = i
in {FStar_Absyn_Syntax.v = _36_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _36_501.FStar_Absyn_Syntax.p})
in (
# 333 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (
# 334 "FStar.Tc.Tc.fst"
let _36_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_36_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(
# 338 "FStar.Tc.Tc.fst"
let _36_516 = (tc_binders env bs)
in (match (_36_516) with
| (bs, env, g) -> begin
(
# 339 "FStar.Tc.Tc.fst"
let _36_519 = (tc_comp env cod)
in (match (_36_519) with
| (cod, f) -> begin
(
# 340 "FStar.Tc.Tc.fst"
let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (
# 341 "FStar.Tc.Tc.fst"
let _36_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _36_542; FStar_Absyn_Syntax.result_typ = _36_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _36_536)::(FStar_Util.Inl (post), _36_531)::(FStar_Util.Inr (pats), _36_526)::[]; FStar_Absyn_Syntax.flags = _36_522}) -> begin
(
# 345 "FStar.Tc.Tc.fst"
let rec extract_pats = (fun pats -> (match ((let _115_299 = (FStar_Absyn_Util.compress_exp pats)
in _115_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _36_557); FStar_Absyn_Syntax.tk = _36_554; FStar_Absyn_Syntax.pos = _36_552; FStar_Absyn_Syntax.fvs = _36_550; FStar_Absyn_Syntax.uvs = _36_548}, _36_572::(FStar_Util.Inr (hd), _36_569)::(FStar_Util.Inr (tl), _36_564)::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(
# 347 "FStar.Tc.Tc.fst"
let _36_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_36_578) with
| (head, args) -> begin
(
# 348 "FStar.Tc.Tc.fst"
let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _36_585 -> begin
[]
end)
in (let _115_300 = (extract_pats tl)
in (FStar_List.append pat _115_300)))
end))
end
| _36_588 -> begin
[]
end))
in (
# 354 "FStar.Tc.Tc.fst"
let pats = (let _115_301 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _115_301))
in (
# 355 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _36_594 -> (match (_36_594) with
| (b, _36_593) -> begin
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
(let _115_304 = (let _115_303 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _115_303))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _115_304))
end))))
end
| _36_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _115_306 = (let _115_305 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _115_305))
in (t, FStar_Absyn_Syntax.ktype, _115_306))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(
# 368 "FStar.Tc.Tc.fst"
let _36_613 = (tc_binders env bs)
in (match (_36_613) with
| (bs, env, g) -> begin
(
# 369 "FStar.Tc.Tc.fst"
let _36_617 = (tc_typ env t)
in (match (_36_617) with
| (t, k, f) -> begin
(
# 370 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _115_311 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _115_310 = (let _115_309 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _115_309))
in (_115_311, k, _115_310))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(
# 374 "FStar.Tc.Tc.fst"
let _36_626 = (tc_vbinder env x)
in (match (_36_626) with
| (x, env, f1) -> begin
(
# 375 "FStar.Tc.Tc.fst"
let _36_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_314 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _115_313 = (FStar_Absyn_Print.typ_to_string phi)
in (let _115_312 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _115_314 _115_313 _115_312))))
end else begin
()
end
in (
# 380 "FStar.Tc.Tc.fst"
let _36_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_36_634) with
| (phi, f2) -> begin
(let _115_321 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _115_320 = (let _115_319 = (let _115_318 = (let _115_317 = (FStar_Absyn_Syntax.v_binder x)
in (_115_317)::[])
in (FStar_Tc_Rel.close_guard _115_318 f2))
in (FStar_Tc_Rel.conj_guard f1 _115_319))
in (_115_321, FStar_Absyn_Syntax.ktype, _115_320)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(
# 384 "FStar.Tc.Tc.fst"
let _36_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_324 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _115_323 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _115_322 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _115_324 _115_323 _115_322))))
end else begin
()
end
in (
# 388 "FStar.Tc.Tc.fst"
let _36_644 = (tc_typ (no_inst env) head)
in (match (_36_644) with
| (head, k1', f1) -> begin
(
# 389 "FStar.Tc.Tc.fst"
let args0 = args
in (
# 390 "FStar.Tc.Tc.fst"
let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (
# 392 "FStar.Tc.Tc.fst"
let _36_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_328 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _115_327 = (FStar_Absyn_Print.typ_to_string head)
in (let _115_326 = (FStar_Absyn_Print.kind_to_string k1')
in (let _115_325 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _115_328 _115_327 _115_326 _115_325)))))
end else begin
()
end
in (
# 398 "FStar.Tc.Tc.fst"
let check_app = (fun _36_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_36_652) -> begin
(
# 400 "FStar.Tc.Tc.fst"
let _36_656 = (tc_args env args)
in (match (_36_656) with
| (args, g) -> begin
(
# 401 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (
# 402 "FStar.Tc.Tc.fst"
let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (
# 403 "FStar.Tc.Tc.fst"
let kres = (let _115_331 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _115_331 Prims.fst))
in (
# 404 "FStar.Tc.Tc.fst"
let bs = (let _115_332 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _115_332))
in (
# 405 "FStar.Tc.Tc.fst"
let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (
# 406 "FStar.Tc.Tc.fst"
let _36_662 = (let _115_333 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _115_333))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(
# 410 "FStar.Tc.Tc.fst"
let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _115_344 = (FStar_Absyn_Util.subst_kind subst kres)
in (_115_344, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) -> begin
(let _115_348 = (let _115_347 = (let _115_346 = (let _115_345 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _115_345))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _115_346))
in FStar_Absyn_Syntax.Error (_115_347))
in (Prims.raise _115_348))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, [])) -> begin
(
# 418 "FStar.Tc.Tc.fst"
let formal = (FStar_List.hd formals)
in (
# 419 "FStar.Tc.Tc.fst"
let _36_743 = (let _115_349 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _115_349))
in (match (_36_743) with
| (t, u) -> begin
(
# 420 "FStar.Tc.Tc.fst"
let targ = (let _115_351 = (FStar_All.pipe_left (fun _115_350 -> Some (_115_350)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _115_351))
in (
# 421 "FStar.Tc.Tc.fst"
let g = (add_implicit (FStar_Util.Inl (u)) g)
in (
# 422 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, (_, None)::_)) | (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, [])) -> begin
(
# 427 "FStar.Tc.Tc.fst"
let formal = (FStar_List.hd formals)
in (
# 428 "FStar.Tc.Tc.fst"
let _36_776 = (let _115_352 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _115_352))
in (match (_36_776) with
| (e, u) -> begin
(
# 429 "FStar.Tc.Tc.fst"
let varg = (let _115_354 = (FStar_All.pipe_left (fun _115_353 -> Some (_115_353)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (e), _115_354))
in (
# 430 "FStar.Tc.Tc.fst"
let g = (add_implicit (FStar_Util.Inr (u)) g)
in (
# 431 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal varg)
in (check_args ((varg)::outargs) subst g rest args))))
end)))
end
| (formal::formals, actual::actuals) -> begin
(match ((formal, actual)) with
| ((FStar_Util.Inl (a), aqual), (FStar_Util.Inl (t), imp)) -> begin
(
# 437 "FStar.Tc.Tc.fst"
let formal_k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 438 "FStar.Tc.Tc.fst"
let _36_797 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_356 = (FStar_Absyn_Print.arg_to_string actual)
in (let _115_355 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _115_356 _115_355)))
end else begin
()
end
in (
# 441 "FStar.Tc.Tc.fst"
let _36_803 = (tc_typ_check (
# 441 "FStar.Tc.Tc.fst"
let _36_799 = env
in {FStar_Tc_Env.solver = _36_799.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_799.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_799.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_799.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_799.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_799.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_799.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_799.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_799.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_799.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_799.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_799.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_799.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_799.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_799.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_799.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _36_799.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_799.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_799.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_36_803) with
| (t, g') -> begin
(
# 442 "FStar.Tc.Tc.fst"
let _36_804 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_357 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _115_357))
end else begin
()
end
in (
# 444 "FStar.Tc.Tc.fst"
let actual = (FStar_Util.Inl (t), imp)
in (
# 445 "FStar.Tc.Tc.fst"
let g' = (let _115_359 = (let _115_358 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _115_358))
in (FStar_Tc_Rel.imp_guard _115_359 g'))
in (
# 446 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal actual)
in (let _115_360 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _115_360 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(
# 450 "FStar.Tc.Tc.fst"
let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 451 "FStar.Tc.Tc.fst"
let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (
# 452 "FStar.Tc.Tc.fst"
let env' = (
# 452 "FStar.Tc.Tc.fst"
let _36_820 = env'
in {FStar_Tc_Env.solver = _36_820.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_820.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_820.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_820.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_820.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_820.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_820.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_820.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_820.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_820.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_820.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_820.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_820.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_820.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_820.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_820.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _36_820.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_820.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_820.FStar_Tc_Env.default_effects})
in (
# 453 "FStar.Tc.Tc.fst"
let _36_823 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_362 = (FStar_Absyn_Print.arg_to_string actual)
in (let _115_361 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _115_362 _115_361)))
end else begin
()
end
in (
# 454 "FStar.Tc.Tc.fst"
let _36_829 = (tc_ghost_exp env' v)
in (match (_36_829) with
| (v, _36_827, g') -> begin
(
# 455 "FStar.Tc.Tc.fst"
let actual = (FStar_Util.Inr (v), imp)
in (
# 456 "FStar.Tc.Tc.fst"
let g' = (let _115_364 = (let _115_363 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _115_363))
in (FStar_Tc_Rel.imp_guard _115_364 g'))
in (
# 457 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal actual)
in (let _115_365 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _115_365 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _36_836), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(
# 463 "FStar.Tc.Tc.fst"
let tv = (FStar_Absyn_Util.b2t v)
in (let _115_367 = (let _115_366 = (FStar_Absyn_Syntax.targ tv)
in (_115_366)::actuals)
in (check_args outargs subst g ((formal)::formals) _115_367)))
end
| _36_846 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_36_848), _36_851), (FStar_Util.Inl (_36_854), _36_857)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_36_861, []) -> begin
(let _115_369 = (let _115_368 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _115_368))
in (_115_369, (FStar_List.rev outargs), g))
end
| ([], _36_866) -> begin
(let _115_377 = (let _115_376 = (let _115_375 = (let _115_374 = (let _115_372 = (let _115_371 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _36_4 -> (match (_36_4) with
| (_36_870, Some (FStar_Absyn_Syntax.Implicit (_36_872))) -> begin
false
end
| _36_877 -> begin
true
end))))
in (FStar_List.length _115_371))
in (FStar_All.pipe_right _115_372 FStar_Util.string_of_int))
in (let _115_373 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _115_374 _115_373)))
in (_115_375, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_376))
in (Prims.raise _115_377))
end))
in (check_args [] [] f1 formals args))
end
| _36_879 -> begin
(let _115_380 = (let _115_379 = (let _115_378 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_115_378, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_379))
in (Prims.raise _115_380))
end)
end))
in (match ((let _115_384 = (let _115_381 = (FStar_Absyn_Util.compress_typ head)
in _115_381.FStar_Absyn_Syntax.n)
in (let _115_383 = (let _115_382 = (FStar_Absyn_Util.compress_kind k1)
in _115_382.FStar_Absyn_Syntax.n)
in (_115_384, _115_383)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_36_881), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(
# 489 "FStar.Tc.Tc.fst"
let result_k = (
# 490 "FStar.Tc.Tc.fst"
let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (
# 492 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in (t, result_k, FStar_Tc_Rel.trivial_guard)))
end
| _36_892 -> begin
(
# 496 "FStar.Tc.Tc.fst"
let _36_896 = (check_app ())
in (match (_36_896) with
| (k, args, g) -> begin
(
# 498 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(
# 503 "FStar.Tc.Tc.fst"
let _36_904 = (tc_kind env k1)
in (match (_36_904) with
| (k1, f1) -> begin
(
# 504 "FStar.Tc.Tc.fst"
let _36_907 = (tc_typ_check env t1 k1)
in (match (_36_907) with
| (t1, f2) -> begin
(let _115_388 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _115_387 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_115_388, k1, _115_387)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_36_909, k1) -> begin
(
# 508 "FStar.Tc.Tc.fst"
let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(
# 511 "FStar.Tc.Tc.fst"
let _36_918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _115_390 = (FStar_Absyn_Print.typ_to_string s)
in (let _115_389 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _115_390 _115_389)))
end else begin
()
end
in (let _115_393 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_115_393, k1, FStar_Tc_Rel.trivial_guard)))
end
| _36_921 -> begin
(
# 515 "FStar.Tc.Tc.fst"
let _36_922 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _115_395 = (FStar_Absyn_Print.typ_to_string s)
in (let _115_394 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _115_395 _115_394)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(
# 520 "FStar.Tc.Tc.fst"
let _36_933 = (tc_typ env t)
in (match (_36_933) with
| (t, k, f) -> begin
(let _115_396 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_115_396, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(
# 524 "FStar.Tc.Tc.fst"
let _36_944 = (tc_typ env t)
in (match (_36_944) with
| (t, k, f) -> begin
(let _115_397 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_115_397, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(
# 528 "FStar.Tc.Tc.fst"
let _36_953 = (tc_typ env t)
in (match (_36_953) with
| (t, k, f) -> begin
(let _115_398 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_115_398, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(
# 532 "FStar.Tc.Tc.fst"
let _36_961 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_36_961) with
| (quant, f) -> begin
(
# 533 "FStar.Tc.Tc.fst"
let _36_964 = (tc_pats env pats)
in (match (_36_964) with
| (pats, g) -> begin
(
# 534 "FStar.Tc.Tc.fst"
let g = (
# 534 "FStar.Tc.Tc.fst"
let _36_965 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _36_965.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _36_965.FStar_Tc_Rel.implicits})
in (let _115_401 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _115_400 = (FStar_Tc_Util.force_tk quant)
in (let _115_399 = (FStar_Tc_Rel.conj_guard f g)
in (_115_401, _115_400, _115_399)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(
# 538 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Util.new_kvar env)
in (
# 539 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Util.new_tvar env k)
in (t, k, FStar_Tc_Rel.trivial_guard)))
end
| _36_972 -> begin
(let _115_403 = (let _115_402 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _115_402))
in (FStar_All.failwith _115_403))
end))))))
and tc_typ_check : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env t k -> (
# 545 "FStar.Tc.Tc.fst"
let _36_979 = (tc_typ env t)
in (match (_36_979) with
| (t, k', f) -> begin
(
# 546 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (
# 547 "FStar.Tc.Tc.fst"
let f' = if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.keq env (Some (t)) k' k)
end else begin
(FStar_Tc_Rel.subkind env k' k)
end
in (
# 550 "FStar.Tc.Tc.fst"
let f = (FStar_Tc_Rel.conj_guard f f')
in (t, f))))
end)))
and tc_value : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 554 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (
# 555 "FStar.Tc.Tc.fst"
let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (_36_988, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(
# 561 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Env.lookup_bvar env x)
in (
# 562 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_bvar (
# 562 "FStar.Tc.Tc.fst"
let _36_995 = x
in {FStar_Absyn_Syntax.v = _36_995.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _36_995.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (
# 563 "FStar.Tc.Tc.fst"
let _36_1001 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_36_1001) with
| (e, t, implicits) -> begin
(
# 564 "FStar.Tc.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _115_410 = (let _115_409 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _115_409))
in FStar_Util.Inr (_115_410))
end
in (let _115_411 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _115_411)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(
# 568 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (
# 569 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_fvar ((
# 569 "FStar.Tc.Tc.fst"
let _36_1008 = v
in {FStar_Absyn_Syntax.v = _36_1008.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _36_1008.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (
# 570 "FStar.Tc.Tc.fst"
let _36_1014 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_36_1014) with
| (e, t, implicits) -> begin
(
# 572 "FStar.Tc.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _115_413 = (let _115_412 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _115_412))
in FStar_Util.Inr (_115_413))
end
in (
# 573 "FStar.Tc.Tc.fst"
let is_data_ctor = (fun _36_5 -> (match (_36_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _36_1024 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _115_419 = (let _115_418 = (let _115_417 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _115_416 = (FStar_Tc_Env.get_range env)
in (_115_417, _115_416)))
in FStar_Absyn_Syntax.Error (_115_418))
in (Prims.raise _115_419))
end else begin
(let _115_420 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _115_420))
end))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(
# 582 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (
# 583 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 587 "FStar.Tc.Tc.fst"
let fail = (fun msg t -> (let _115_425 = (let _115_424 = (let _115_423 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_115_423, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_424))
in (Prims.raise _115_425)))
in (
# 588 "FStar.Tc.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 596 "FStar.Tc.Tc.fst"
let _36_1045 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _36_1044 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 597 "FStar.Tc.Tc.fst"
let _36_1050 = (tc_binders env bs)
in (match (_36_1050) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(
# 601 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (
# 602 "FStar.Tc.Tc.fst"
let rec as_function_typ = (fun norm t -> (match ((let _115_434 = (FStar_Absyn_Util.compress_typ t)
in _115_434.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(
# 606 "FStar.Tc.Tc.fst"
let _36_1079 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _36_1078 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 607 "FStar.Tc.Tc.fst"
let _36_1084 = (tc_binders env bs)
in (match (_36_1084) with
| (bs, envbody, g) -> begin
(
# 608 "FStar.Tc.Tc.fst"
let _36_1088 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_36_1088) with
| (envbody, _36_1087) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(
# 620 "FStar.Tc.Tc.fst"
let rec tc_binders = (fun _36_1098 bs_annot c bs -> (match (_36_1098) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _115_443 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _115_443))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_36_1113), _36_1116), (FStar_Util.Inr (_36_1119), _36_1122)) -> begin
(
# 626 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _36_1129), (FStar_Util.Inl (b), imp)) -> begin
(
# 630 "FStar.Tc.Tc.fst"
let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 631 "FStar.Tc.Tc.fst"
let _36_1147 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _36_1139 -> begin
(
# 634 "FStar.Tc.Tc.fst"
let _36_1142 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_36_1142) with
| (k, g1) -> begin
(
# 635 "FStar.Tc.Tc.fst"
let g2 = (FStar_Tc_Rel.keq env None ka k)
in (
# 636 "FStar.Tc.Tc.fst"
let g = (let _115_444 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _115_444))
in (k, g)))
end))
end)
in (match (_36_1147) with
| (k, g) -> begin
(
# 638 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inl ((
# 638 "FStar.Tc.Tc.fst"
let _36_1148 = b
in {FStar_Absyn_Syntax.v = _36_1148.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _36_1148.FStar_Absyn_Syntax.p})), imp)
in (
# 639 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 640 "FStar.Tc.Tc.fst"
let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _36_1156), (FStar_Util.Inr (y), imp)) -> begin
(
# 644 "FStar.Tc.Tc.fst"
let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 645 "FStar.Tc.Tc.fst"
let _36_1178 = (match ((let _115_445 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _115_445.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _36_1166 -> begin
(
# 648 "FStar.Tc.Tc.fst"
let _36_1167 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_446 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _115_446))
end else begin
()
end
in (
# 649 "FStar.Tc.Tc.fst"
let _36_1173 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_36_1173) with
| (t, _36_1171, g1) -> begin
(
# 650 "FStar.Tc.Tc.fst"
let g2 = (FStar_Tc_Rel.teq env tx t)
in (
# 651 "FStar.Tc.Tc.fst"
let g = (let _115_447 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _115_447))
in (t, g)))
end)))
end)
in (match (_36_1178) with
| (t, g) -> begin
(
# 653 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inr ((
# 653 "FStar.Tc.Tc.fst"
let _36_1179 = y
in {FStar_Absyn_Syntax.v = _36_1179.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _36_1179.FStar_Absyn_Syntax.p})), imp)
in (
# 654 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 655 "FStar.Tc.Tc.fst"
let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _36_1185 -> begin
(let _115_450 = (let _115_449 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _115_448 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _115_449 _115_448)))
in (fail _115_450 t))
end)
end
| ([], _36_1188) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _36_1197; FStar_Absyn_Syntax.pos = _36_1195; FStar_Absyn_Syntax.fvs = _36_1193; FStar_Absyn_Syntax.uvs = _36_1191} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _115_452 = (let _115_451 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _115_451))
in (fail _115_452 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_36_1205, []) -> begin
(
# 669 "FStar.Tc.Tc.fst"
let c = (let _115_453 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _115_453 c.FStar_Absyn_Syntax.pos))
in (let _115_454 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _115_454)))
end)
end))
in (
# 672 "FStar.Tc.Tc.fst"
let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(
# 675 "FStar.Tc.Tc.fst"
let _36_1214 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_459 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _115_459))
end else begin
()
end
in (
# 676 "FStar.Tc.Tc.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 677 "FStar.Tc.Tc.fst"
let env = (
# 677 "FStar.Tc.Tc.fst"
let _36_1217 = env
in {FStar_Tc_Env.solver = _36_1217.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_1217.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_1217.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_1217.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_1217.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_1217.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_1217.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_1217.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_1217.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_1217.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_1217.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_1217.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_1217.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _36_1217.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_1217.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_1217.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_1217.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_1217.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_1217.FStar_Tc_Env.default_effects})
in (
# 679 "FStar.Tc.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_36_1224), _36_1227) -> begin
[]
end
| (FStar_Util.Inr (x), _36_1232) -> begin
(match ((let _115_465 = (let _115_464 = (let _115_463 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _115_463))
in (FStar_Absyn_Util.unrefine _115_464))
in _115_465.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_36_1235) -> begin
[]
end
| _36_1238 -> begin
(let _115_466 = (FStar_Absyn_Util.bvar_to_exp x)
in (_115_466)::[])
end)
end)))))
in (
# 687 "FStar.Tc.Tc.fst"
let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (
# 688 "FStar.Tc.Tc.fst"
let as_lex_list = (fun dec -> (
# 689 "FStar.Tc.Tc.fst"
let _36_1245 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_36_1245) with
| (head, _36_1244) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _36_1248) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _36_1252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 693 "FStar.Tc.Tc.fst"
let prev_dec = (
# 694 "FStar.Tc.Tc.fst"
let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _36_6 -> (match (_36_6) with
| FStar_Absyn_Syntax.DECREASES (_36_1256) -> begin
true
end
| _36_1259 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(
# 697 "FStar.Tc.Tc.fst"
let _36_1263 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _115_475 = (let _115_474 = (let _115_473 = (let _115_471 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _115_470 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _115_471 _115_470)))
in (let _115_472 = (FStar_Tc_Env.get_range env)
in (_115_473, _115_472)))
in FStar_Absyn_Syntax.Error (_115_474))
in (Prims.raise _115_475))
end else begin
()
end
in (
# 701 "FStar.Tc.Tc.fst"
let dec = (as_lex_list dec)
in (
# 702 "FStar.Tc.Tc.fst"
let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _36_1271), (FStar_Util.Inl (actual), _36_1276)) -> begin
(let _115_479 = (let _115_478 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _115_478))
in FStar_Util.Inl (_115_479))
end
| ((FStar_Util.Inr (formal), _36_1282), (FStar_Util.Inr (actual), _36_1287)) -> begin
(let _115_481 = (let _115_480 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _115_480))
in FStar_Util.Inr (_115_481))
end
| _36_1291 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _36_1294 -> begin
(
# 709 "FStar.Tc.Tc.fst"
let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _36_1299 -> begin
(mk_lex_list actual_args)
end))
end))
in (
# 714 "FStar.Tc.Tc.fst"
let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _36_1303 -> (match (_36_1303) with
| (l, t0) -> begin
(
# 715 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _115_483 = (FStar_Absyn_Util.compress_typ t)
in _115_483.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(
# 720 "FStar.Tc.Tc.fst"
let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (
# 721 "FStar.Tc.Tc.fst"
let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (
# 722 "FStar.Tc.Tc.fst"
let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _36_7 -> (match (_36_7) with
| FStar_Absyn_Syntax.DECREASES (_36_1319) -> begin
true
end
| _36_1322 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(
# 724 "FStar.Tc.Tc.fst"
let dec = (as_lex_list dec)
in (
# 725 "FStar.Tc.Tc.fst"
let dec = (
# 726 "FStar.Tc.Tc.fst"
let subst = (let _115_487 = (let _115_486 = (let _115_485 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _115_485))
in FStar_Util.Inr (_115_486))
in (_115_487)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _115_492 = (let _115_491 = (let _115_490 = (FStar_Absyn_Syntax.varg dec)
in (let _115_489 = (let _115_488 = (FStar_Absyn_Syntax.varg prev_dec)
in (_115_488)::[])
in (_115_490)::_115_489))
in (precedes, _115_491))
in (FStar_Absyn_Syntax.mk_Typ_app _115_492 None r))))
end
| _36_1330 -> begin
(
# 731 "FStar.Tc.Tc.fst"
let formal_args = (let _115_495 = (let _115_494 = (let _115_493 = (FStar_Absyn_Syntax.v_binder y)
in (_115_493)::[])
in (FStar_List.append bs _115_494))
in (FStar_All.pipe_right _115_495 filter_types_and_functions))
in (
# 732 "FStar.Tc.Tc.fst"
let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _36_1335 -> begin
(mk_lex_list formal_args)
end)
in (let _115_500 = (let _115_499 = (let _115_498 = (FStar_Absyn_Syntax.varg lhs)
in (let _115_497 = (let _115_496 = (FStar_Absyn_Syntax.varg prev_dec)
in (_115_496)::[])
in (_115_498)::_115_497))
in (precedes, _115_499))
in (FStar_Absyn_Syntax.mk_Typ_app _115_500 None r))))
end)
in (
# 737 "FStar.Tc.Tc.fst"
let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (
# 738 "FStar.Tc.Tc.fst"
let bs = (FStar_List.append bs (((FStar_Util.Inr ((
# 738 "FStar.Tc.Tc.fst"
let _36_1339 = x
in {FStar_Absyn_Syntax.v = _36_1339.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _36_1339.FStar_Absyn_Syntax.p})), imp))::[]))
in (
# 739 "FStar.Tc.Tc.fst"
let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (
# 740 "FStar.Tc.Tc.fst"
let _36_1343 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_503 = (FStar_Absyn_Print.lbname_to_string l)
in (let _115_502 = (FStar_Absyn_Print.typ_to_string t)
in (let _115_501 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _115_503 _115_502 _115_501))))
end else begin
()
end
in (
# 743 "FStar.Tc.Tc.fst"
let _36_1350 = (let _115_505 = (let _115_504 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _115_504 Prims.fst))
in (tc_typ _115_505 t'))
in (match (_36_1350) with
| (t', _36_1347, _36_1349) -> begin
(l, t')
end)))))))))
end
| _36_1352 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _36_1354 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _115_511 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _36_1359 -> (match (_36_1359) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _115_510 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _36_8 -> (match (_36_8) with
| (FStar_Util.Inl (x), t) -> begin
(let _115_509 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_115_509)::[])
end
| _36_1366 -> begin
[]
end))))
in (_115_511, _115_510)))))))))))
end))
in (
# 755 "FStar.Tc.Tc.fst"
let _36_1371 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_36_1371) with
| (bs, envbody, g, c) -> begin
(
# 756 "FStar.Tc.Tc.fst"
let _36_1374 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_36_1374) with
| (envbody, letrecs) -> begin
(
# 757 "FStar.Tc.Tc.fst"
let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _36_1378) -> begin
(
# 763 "FStar.Tc.Tc.fst"
let _36_1388 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_36_1388) with
| (_36_1382, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _36_1390 -> begin
if (not (norm)) then begin
(let _115_512 = (whnf env t)
in (as_function_typ true _115_512))
end else begin
(
# 771 "FStar.Tc.Tc.fst"
let _36_1399 = (expected_function_typ env None)
in (match (_36_1399) with
| (_36_1392, bs, _36_1395, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (
# 775 "FStar.Tc.Tc.fst"
let use_eq = env.FStar_Tc_Env.use_eq
in (
# 776 "FStar.Tc.Tc.fst"
let _36_1403 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_36_1403) with
| (env, topt) -> begin
(
# 777 "FStar.Tc.Tc.fst"
let _36_1410 = (expected_function_typ env topt)
in (match (_36_1410) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 778 "FStar.Tc.Tc.fst"
let _36_1416 = (tc_exp (
# 778 "FStar.Tc.Tc.fst"
let _36_1411 = envbody
in {FStar_Tc_Env.solver = _36_1411.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_1411.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_1411.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_1411.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_1411.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_1411.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_1411.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_1411.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_1411.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_1411.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_1411.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_1411.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_1411.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_1411.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _36_1411.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _36_1411.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_1411.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_1411.FStar_Tc_Env.default_effects}) body)
in (match (_36_1416) with
| (body, cbody, guard_body) -> begin
(
# 779 "FStar.Tc.Tc.fst"
let _36_1417 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _115_515 = (FStar_Absyn_Print.exp_to_string body)
in (let _115_514 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _115_513 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _115_515 _115_514 _115_513))))
end else begin
()
end
in (
# 781 "FStar.Tc.Tc.fst"
let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (
# 782 "FStar.Tc.Tc.fst"
let _36_1420 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _115_516 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _115_516))
end else begin
()
end
in (
# 784 "FStar.Tc.Tc.fst"
let _36_1427 = (let _115_518 = (let _115_517 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _115_517))
in (check_expected_effect (
# 784 "FStar.Tc.Tc.fst"
let _36_1422 = envbody
in {FStar_Tc_Env.solver = _36_1422.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_1422.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_1422.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_1422.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_1422.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_1422.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_1422.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_1422.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_1422.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_1422.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_1422.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_1422.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_1422.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_1422.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_1422.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_1422.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _36_1422.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_1422.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_1422.FStar_Tc_Env.default_effects}) c_opt _115_518))
in (match (_36_1427) with
| (body, cbody, guard) -> begin
(
# 785 "FStar.Tc.Tc.fst"
let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (
# 786 "FStar.Tc.Tc.fst"
let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(
# 787 "FStar.Tc.Tc.fst"
let _36_1429 = (let _115_519 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _115_519))
in (
# 787 "FStar.Tc.Tc.fst"
let _36_1431 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _36_1431.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _36_1431.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(
# 788 "FStar.Tc.Tc.fst"
let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (
# 790 "FStar.Tc.Tc.fst"
let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (
# 792 "FStar.Tc.Tc.fst"
let e = (let _115_521 = (let _115_520 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_115_520, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _115_521 None top.FStar_Absyn_Syntax.pos))
in (
# 794 "FStar.Tc.Tc.fst"
let _36_1454 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 796 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_36_1443) -> begin
(let _115_524 = (let _115_523 = (let _115_522 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_115_522, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _115_523 None top.FStar_Absyn_Syntax.pos))
in (_115_524, t, guard))
end
| _36_1446 -> begin
(
# 805 "FStar.Tc.Tc.fst"
let _36_1449 = if use_teq then begin
(let _115_525 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _115_525))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_36_1449) with
| (e, guard') -> begin
(let _115_527 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _115_526 = (FStar_Tc_Rel.conj_guard guard guard')
in (_115_527, t, _115_526)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_36_1454) with
| (e, tfun, guard) -> begin
(
# 813 "FStar.Tc.Tc.fst"
let _36_1455 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_530 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _115_529 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _115_528 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _115_530 _115_529 _115_528))))
end else begin
()
end
in (
# 816 "FStar.Tc.Tc.fst"
let c = if env.FStar_Tc_Env.top_level then begin
(FStar_Absyn_Syntax.mk_Total tfun)
end else begin
(FStar_Tc_Util.return_value env tfun e)
end
in (
# 817 "FStar.Tc.Tc.fst"
let _36_1460 = (let _115_532 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _115_532 guard))
in (match (_36_1460) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _36_1462 -> begin
(let _115_534 = (let _115_533 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _115_533))
in (FStar_All.failwith _115_534))
end))))
and tc_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 825 "FStar.Tc.Tc.fst"
let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (
# 826 "FStar.Tc.Tc.fst"
let _36_1466 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_539 = (let _115_537 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _115_537))
in (let _115_538 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _115_539 _115_538)))
end else begin
()
end
in (
# 827 "FStar.Tc.Tc.fst"
let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (
# 828 "FStar.Tc.Tc.fst"
let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_36_1472) -> begin
(let _115_563 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _115_563))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _36_1492) -> begin
(
# 839 "FStar.Tc.Tc.fst"
let _36_1497 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_36_1497) with
| (t1, f) -> begin
(
# 840 "FStar.Tc.Tc.fst"
let _36_1501 = (let _115_564 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _115_564 e1))
in (match (_36_1501) with
| (e1, c, g) -> begin
(
# 841 "FStar.Tc.Tc.fst"
let _36_1505 = (let _115_568 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _36_1502 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _115_568 e1 c f))
in (match (_36_1505) with
| (c, f) -> begin
(
# 842 "FStar.Tc.Tc.fst"
let _36_1509 = (let _115_572 = (let _115_571 = (w c)
in (FStar_All.pipe_left _115_571 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _115_572 c))
in (match (_36_1509) with
| (e, c, f2) -> begin
(let _115_574 = (let _115_573 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _115_573))
in (e, c, _115_574))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(
# 846 "FStar.Tc.Tc.fst"
let pats_t = (let _115_580 = (let _115_579 = (let _115_575 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _115_575))
in (let _115_578 = (let _115_577 = (let _115_576 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _115_576))
in (_115_577)::[])
in (_115_579, _115_578)))
in (FStar_Absyn_Syntax.mk_Typ_app _115_580 None FStar_Absyn_Syntax.dummyRange))
in (
# 847 "FStar.Tc.Tc.fst"
let _36_1519 = (let _115_581 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _115_581 e))
in (match (_36_1519) with
| (e, t, g) -> begin
(
# 848 "FStar.Tc.Tc.fst"
let g = (
# 848 "FStar.Tc.Tc.fst"
let _36_1520 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _36_1520.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _36_1520.FStar_Tc_Rel.implicits})
in (
# 849 "FStar.Tc.Tc.fst"
let c = (let _115_582 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _115_582 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _115_583 = (FStar_Absyn_Util.compress_exp e)
in _115_583.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_36_1530, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _36_1535; FStar_Absyn_Syntax.lbeff = _36_1533; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 855 "FStar.Tc.Tc.fst"
let _36_1546 = (let _115_584 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _115_584 e1))
in (match (_36_1546) with
| (e1, c1, g1) -> begin
(
# 856 "FStar.Tc.Tc.fst"
let _36_1550 = (tc_exp env e2)
in (match (_36_1550) with
| (e2, c2, g2) -> begin
(
# 857 "FStar.Tc.Tc.fst"
let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _115_597 = (let _115_595 = (let _115_594 = (let _115_593 = (let _115_592 = (w c)
in (let _115_591 = (let _115_590 = (let _115_589 = (let _115_588 = (let _115_587 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1))
in (_115_587)::[])
in (false, _115_588))
in (_115_589, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _115_590))
in (FStar_All.pipe_left _115_592 _115_591)))
in (_115_593, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_115_594))
in (FStar_Absyn_Syntax.mk_Exp_meta _115_595))
in (let _115_596 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_115_597, c, _115_596))))
end))
end))
end
| _36_1553 -> begin
(
# 860 "FStar.Tc.Tc.fst"
let _36_1557 = (tc_exp env e)
in (match (_36_1557) with
| (e, c, g) -> begin
(let _115_598 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_115_598, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(
# 865 "FStar.Tc.Tc.fst"
let _36_1566 = (tc_exp env e)
in (match (_36_1566) with
| (e, c, g) -> begin
(let _115_599 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_115_599, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 869 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 870 "FStar.Tc.Tc.fst"
let env = (let _115_601 = (let _115_600 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _115_600 Prims.fst))
in (FStar_All.pipe_right _115_601 instantiate_both))
in (
# 871 "FStar.Tc.Tc.fst"
let _36_1573 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_603 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _115_602 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _115_603 _115_602)))
end else begin
()
end
in (
# 872 "FStar.Tc.Tc.fst"
let _36_1578 = (tc_exp (no_inst env) head)
in (match (_36_1578) with
| (head, chead, g_head) -> begin
(
# 873 "FStar.Tc.Tc.fst"
let aux = (fun _36_1580 -> (match (()) with
| () -> begin
(
# 874 "FStar.Tc.Tc.fst"
let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _36_1584) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(
# 877 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _36_1596)::(FStar_Util.Inr (e2), _36_1591)::[] -> begin
(
# 880 "FStar.Tc.Tc.fst"
let _36_1602 = (tc_exp env e1)
in (match (_36_1602) with
| (e1, c1, g1) -> begin
(
# 881 "FStar.Tc.Tc.fst"
let _36_1606 = (tc_exp env e2)
in (match (_36_1606) with
| (e2, c2, g2) -> begin
(
# 882 "FStar.Tc.Tc.fst"
let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (
# 883 "FStar.Tc.Tc.fst"
let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (
# 884 "FStar.Tc.Tc.fst"
let c2 = if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _115_609 = (let _115_606 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _115_606))
in (let _115_608 = (let _115_607 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _115_607 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _115_609 c2 _115_608)))
end else begin
(let _115_613 = (let _115_610 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _115_610))
in (let _115_612 = (let _115_611 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _115_611 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _115_613 _115_612 c2)))
end
in (
# 888 "FStar.Tc.Tc.fst"
let c = (let _115_616 = (let _115_615 = (FStar_All.pipe_left (fun _115_614 -> Some (_115_614)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_115_615, c2))
in (FStar_Tc_Util.bind env None c1 _115_616))
in (
# 889 "FStar.Tc.Tc.fst"
let e = (let _115_621 = (let _115_620 = (let _115_619 = (FStar_Absyn_Syntax.varg e1)
in (let _115_618 = (let _115_617 = (FStar_Absyn_Syntax.varg e2)
in (_115_617)::[])
in (_115_619)::_115_618))
in (head, _115_620))
in (FStar_Absyn_Syntax.mk_Exp_app _115_621 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _115_623 = (let _115_622 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _115_622))
in (e, c, _115_623)))))))
end))
end))
end
| _36_1613 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _36_1615 -> begin
(
# 896 "FStar.Tc.Tc.fst"
let thead = chead.FStar_Absyn_Syntax.res_typ
in (
# 897 "FStar.Tc.Tc.fst"
let _36_1617 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_625 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _115_624 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _115_625 _115_624)))
end else begin
()
end
in (
# 898 "FStar.Tc.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _115_630 = (FStar_Absyn_Util.unrefine tf)
in _115_630.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(
# 901 "FStar.Tc.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _36_1650)::_36_1646 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(
# 906 "FStar.Tc.Tc.fst"
let _36_1662 = (tc_exp env e)
in (match (_36_1662) with
| (e, c, g_e) -> begin
(
# 907 "FStar.Tc.Tc.fst"
let _36_1666 = (tc_args env tl)
in (match (_36_1666) with
| (args, comps, g_rest) -> begin
(let _115_635 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _115_635))
end))
end))
end))
in (
# 912 "FStar.Tc.Tc.fst"
let _36_1670 = (tc_args env args)
in (match (_36_1670) with
| (args, comps, g_args) -> begin
(
# 913 "FStar.Tc.Tc.fst"
let bs = (let _115_636 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _115_636))
in (
# 914 "FStar.Tc.Tc.fst"
let cres = (let _115_637 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _115_637 top.FStar_Absyn_Syntax.pos))
in (
# 915 "FStar.Tc.Tc.fst"
let _36_1673 = (let _115_639 = (let _115_638 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _115_638))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _115_639))
in (
# 916 "FStar.Tc.Tc.fst"
let comp = (let _115_642 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _115_642))
in (let _115_644 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _115_643 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_115_644, comp, _115_643)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 920 "FStar.Tc.Tc.fst"
let vars = (FStar_Tc_Env.binders env)
in (
# 922 "FStar.Tc.Tc.fst"
let rec tc_args = (fun _36_1690 bs cres args -> (match (_36_1690) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_36_1698)))::rest, (_36_1706, None)::_36_1704) -> begin
(
# 933 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 934 "FStar.Tc.Tc.fst"
let _36_1712 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (
# 935 "FStar.Tc.Tc.fst"
let _36_1716 = (let _115_680 = (let _115_679 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _115_679))
in (FStar_Tc_Rel.new_tvar _115_680 vars k))
in (match (_36_1716) with
| (targ, u) -> begin
(
# 936 "FStar.Tc.Tc.fst"
let _36_1717 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_682 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _115_681 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _115_682 _115_681)))
end else begin
()
end
in (
# 937 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (
# 938 "FStar.Tc.Tc.fst"
let arg = (let _115_683 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (targ), _115_683))
in (let _115_692 = (let _115_691 = (let _115_690 = (let _115_689 = (let _115_688 = (FStar_Tc_Util.as_uvar_t u)
in (_115_688, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_115_689))
in (add_implicit _115_690 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _115_691, fvs))
in (tc_args _115_692 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_36_1725)))::rest, (_36_1733, None)::_36_1731) -> begin
(
# 942 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 943 "FStar.Tc.Tc.fst"
let _36_1739 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (
# 944 "FStar.Tc.Tc.fst"
let _36_1743 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_36_1743) with
| (varg, u) -> begin
(
# 945 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (
# 946 "FStar.Tc.Tc.fst"
let arg = (let _115_693 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (varg), _115_693))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(
# 950 "FStar.Tc.Tc.fst"
let _36_1759 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_699 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _115_698 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _115_699 _115_698)))
end else begin
()
end
in (
# 951 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 952 "FStar.Tc.Tc.fst"
let _36_1762 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (
# 953 "FStar.Tc.Tc.fst"
let _36_1768 = (tc_typ_check (
# 953 "FStar.Tc.Tc.fst"
let _36_1764 = env
in {FStar_Tc_Env.solver = _36_1764.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_1764.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_1764.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_1764.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_1764.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_1764.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_1764.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_1764.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_1764.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_1764.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_1764.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_1764.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_1764.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_1764.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_1764.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_1764.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _36_1764.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_1764.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_1764.FStar_Tc_Env.default_effects}) t k)
in (match (_36_1768) with
| (t, g') -> begin
(
# 954 "FStar.Tc.Tc.fst"
let f = (let _115_700 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _115_700))
in (
# 955 "FStar.Tc.Tc.fst"
let g' = (
# 955 "FStar.Tc.Tc.fst"
let _36_1770 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _36_1770.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _36_1770.FStar_Tc_Rel.implicits})
in (
# 956 "FStar.Tc.Tc.fst"
let arg = (FStar_Util.Inl (t), aq)
in (
# 957 "FStar.Tc.Tc.fst"
let subst = (let _115_701 = (FStar_List.hd bs)
in (maybe_extend_subst subst _115_701 arg))
in (let _115_707 = (let _115_706 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _115_706, fvs))
in (tc_args _115_707 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(
# 961 "FStar.Tc.Tc.fst"
let _36_1788 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_709 = (FStar_Absyn_Print.subst_to_string subst)
in (let _115_708 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _115_709 _115_708)))
end else begin
()
end
in (
# 962 "FStar.Tc.Tc.fst"
let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 963 "FStar.Tc.Tc.fst"
let _36_1791 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_710 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _115_710))
end else begin
()
end
in (
# 964 "FStar.Tc.Tc.fst"
let _36_1793 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (
# 965 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env targ)
in (
# 966 "FStar.Tc.Tc.fst"
let env = (
# 966 "FStar.Tc.Tc.fst"
let _36_1796 = env
in {FStar_Tc_Env.solver = _36_1796.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_1796.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_1796.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_1796.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_1796.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_1796.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_1796.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_1796.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_1796.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_1796.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_1796.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_1796.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_1796.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_1796.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_1796.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_1796.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _36_1796.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_1796.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_1796.FStar_Tc_Env.default_effects})
in (
# 967 "FStar.Tc.Tc.fst"
let _36_1799 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _115_712 = (FStar_Absyn_Print.exp_to_string e)
in (let _115_711 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _115_712 _115_711)))
end else begin
()
end
in (
# 968 "FStar.Tc.Tc.fst"
let _36_1801 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_715 = (FStar_Absyn_Print.tag_of_exp e)
in (let _115_714 = (FStar_Absyn_Print.exp_to_string e)
in (let _115_713 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _115_715 _115_714 _115_713))))
end else begin
()
end
in (
# 969 "FStar.Tc.Tc.fst"
let _36_1806 = (tc_exp env e)
in (match (_36_1806) with
| (e, c, g_e) -> begin
(
# 970 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g g_e)
in (
# 971 "FStar.Tc.Tc.fst"
let _36_1808 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_717 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _115_716 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _115_717 _115_716)))
end else begin
()
end
in (
# 972 "FStar.Tc.Tc.fst"
let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(
# 974 "FStar.Tc.Tc.fst"
let subst = (let _115_718 = (FStar_List.hd bs)
in (maybe_extend_subst subst _115_718 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(
# 977 "FStar.Tc.Tc.fst"
let subst = (let _115_723 = (FStar_List.hd bs)
in (maybe_extend_subst subst _115_723 arg))
in (
# 978 "FStar.Tc.Tc.fst"
let _36_1815 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_36_1815) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _115_728 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _115_728)) then begin
(
# 982 "FStar.Tc.Tc.fst"
let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (
# 983 "FStar.Tc.Tc.fst"
let arg' = (let _115_729 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _115_729))
in (
# 984 "FStar.Tc.Tc.fst"
let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _115_742 = (let _115_741 = (let _115_735 = (let _115_734 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _115_734))
in (_115_735)::arg_rets)
in (let _115_740 = (let _115_738 = (let _115_737 = (FStar_All.pipe_left (fun _115_736 -> Some (_115_736)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_115_737, c))
in (_115_738)::comps)
in (let _115_739 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _115_741, _115_740, g, _115_739))))
in (tc_args _115_742 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_36_1822), _36_1825)::_36_1820, (FStar_Util.Inl (_36_1831), _36_1834)::_36_1829) -> begin
(let _115_746 = (let _115_745 = (let _115_744 = (let _115_743 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _115_743))
in ("Expected an expression; got a type", _115_744))
in FStar_Absyn_Syntax.Error (_115_745))
in (Prims.raise _115_746))
end
| ((FStar_Util.Inl (_36_1841), _36_1844)::_36_1839, (FStar_Util.Inr (_36_1850), _36_1853)::_36_1848) -> begin
(let _115_750 = (let _115_749 = (let _115_748 = (let _115_747 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _115_747))
in ("Expected a type; got an expression", _115_748))
in FStar_Absyn_Syntax.Error (_115_749))
in (Prims.raise _115_750))
end
| (_36_1858, []) -> begin
(
# 995 "FStar.Tc.Tc.fst"
let _36_1861 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (
# 996 "FStar.Tc.Tc.fst"
let _36_1879 = (match (bs) with
| [] -> begin
(
# 998 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (
# 1004 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g_head g)
in (
# 1006 "FStar.Tc.Tc.fst"
let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _36_1869 -> (match (_36_1869) with
| (_36_1867, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 1012 "FStar.Tc.Tc.fst"
let cres = if refine_with_equality then begin
(let _115_752 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _115_752 cres))
end else begin
(
# 1015 "FStar.Tc.Tc.fst"
let _36_1871 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_755 = (FStar_Absyn_Print.exp_to_string head)
in (let _115_754 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _115_753 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _115_755 _115_754 _115_753))))
end else begin
()
end
in cres)
end
in (let _115_756 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_115_756, g))))))
end
| _36_1875 -> begin
(
# 1023 "FStar.Tc.Tc.fst"
let g = (let _115_757 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _115_757 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _115_763 = (let _115_762 = (let _115_761 = (let _115_760 = (let _115_759 = (let _115_758 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _115_758))
in (FStar_Absyn_Syntax.mk_Typ_fun _115_759 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _115_760))
in (FStar_Absyn_Syntax.mk_Total _115_761))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _115_762))
in (_115_763, g)))
end)
in (match (_36_1879) with
| (cres, g) -> begin
(
# 1026 "FStar.Tc.Tc.fst"
let _36_1880 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_764 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _115_764))
end else begin
()
end
in (
# 1027 "FStar.Tc.Tc.fst"
let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (
# 1028 "FStar.Tc.Tc.fst"
let comp = (FStar_Tc_Util.bind env None chead (None, comp))
in (
# 1029 "FStar.Tc.Tc.fst"
let app = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev outargs)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (
# 1030 "FStar.Tc.Tc.fst"
let _36_1889 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_36_1889) with
| (comp, g) -> begin
(
# 1031 "FStar.Tc.Tc.fst"
let _36_1890 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_770 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _115_769 = (let _115_768 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _115_768))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _115_770 _115_769)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_36_1894) -> begin
(
# 1036 "FStar.Tc.Tc.fst"
let rec aux = (fun norm tres -> (
# 1037 "FStar.Tc.Tc.fst"
let tres = (let _115_775 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _115_775 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(
# 1040 "FStar.Tc.Tc.fst"
let _36_1906 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_776 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _115_776))
end else begin
()
end
in (let _115_781 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _115_781 args)))
end
| _36_1909 when (not (norm)) -> begin
(let _115_782 = (whnf env tres)
in (aux true _115_782))
end
| _36_1911 -> begin
(let _115_788 = (let _115_787 = (let _115_786 = (let _115_784 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _115_783 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _115_784 _115_783)))
in (let _115_785 = (FStar_Absyn_Syntax.argpos arg)
in (_115_786, _115_785)))
in FStar_Absyn_Syntax.Error (_115_787))
in (Prims.raise _115_788))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _115_789 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _115_789 args))))
end
| _36_1913 -> begin
if (not (norm)) then begin
(let _115_790 = (whnf env tf)
in (check_function_app true _115_790))
end else begin
(let _115_793 = (let _115_792 = (let _115_791 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_115_791, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_792))
in (Prims.raise _115_793))
end
end))
in (let _115_794 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _115_794)))))
end))
end))
in (
# 1055 "FStar.Tc.Tc.fst"
let _36_1917 = (aux ())
in (match (_36_1917) with
| (e, c, g) -> begin
(
# 1056 "FStar.Tc.Tc.fst"
let _36_1918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _115_795 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _115_795))
end else begin
()
end
in (
# 1058 "FStar.Tc.Tc.fst"
let c = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (
# 1063 "FStar.Tc.Tc.fst"
let _36_1925 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_800 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _115_799 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _115_798 = (let _115_797 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _115_797 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _115_800 _115_799 _115_798))))
end else begin
()
end
in (
# 1067 "FStar.Tc.Tc.fst"
let _36_1930 = (comp_check_expected_typ env0 e c)
in (match (_36_1930) with
| (e, c, g') -> begin
(let _115_801 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _115_801))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(
# 1071 "FStar.Tc.Tc.fst"
let _36_1937 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_36_1937) with
| (env1, topt) -> begin
(
# 1072 "FStar.Tc.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 1073 "FStar.Tc.Tc.fst"
let _36_1942 = (tc_exp env1 e1)
in (match (_36_1942) with
| (e1, c1, g1) -> begin
(
# 1074 "FStar.Tc.Tc.fst"
let _36_1949 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 1077 "FStar.Tc.Tc.fst"
let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _115_802 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_115_802, res_t)))
end)
in (match (_36_1949) with
| (env_branches, res_t) -> begin
(
# 1079 "FStar.Tc.Tc.fst"
let guard_x = (let _115_804 = (FStar_All.pipe_left (fun _115_803 -> Some (_115_803)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _115_804))
in (
# 1080 "FStar.Tc.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (
# 1081 "FStar.Tc.Tc.fst"
let _36_1966 = (
# 1082 "FStar.Tc.Tc.fst"
let _36_1963 = (FStar_List.fold_right (fun _36_1957 _36_1960 -> (match ((_36_1957, _36_1960)) with
| ((_36_1953, f, c, g), (caccum, gaccum)) -> begin
(let _115_807 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _115_807))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_36_1963) with
| (cases, g) -> begin
(let _115_808 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_115_808, g))
end))
in (match (_36_1966) with
| (c_branches, g_branches) -> begin
(
# 1085 "FStar.Tc.Tc.fst"
let _36_1967 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_812 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _115_811 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _115_810 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _115_809 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _115_812 _115_811 _115_810 _115_809)))))
end else begin
()
end
in (
# 1088 "FStar.Tc.Tc.fst"
let cres = (let _115_815 = (let _115_814 = (FStar_All.pipe_left (fun _115_813 -> Some (_115_813)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_115_814, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _115_815))
in (
# 1090 "FStar.Tc.Tc.fst"
let e = (let _115_822 = (w cres)
in (let _115_821 = (let _115_820 = (let _115_819 = (FStar_List.map (fun _36_1977 -> (match (_36_1977) with
| (f, _36_1972, _36_1974, _36_1976) -> begin
f
end)) t_eqns)
in (e1, _115_819))
in (FStar_Absyn_Syntax.mk_Exp_match _115_820))
in (FStar_All.pipe_left _115_822 _115_821)))
in (let _115_824 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _115_823 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_115_824, cres, _115_823))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _36_1982; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 1095 "FStar.Tc.Tc.fst"
let env = (instantiate_both env)
in (
# 1096 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 1097 "FStar.Tc.Tc.fst"
let topt = (FStar_Tc_Env.expected_typ env)
in (
# 1098 "FStar.Tc.Tc.fst"
let top_level = (match (x) with
| FStar_Util.Inr (_36_1995) -> begin
true
end
| _36_1998 -> begin
false
end)
in (
# 1099 "FStar.Tc.Tc.fst"
let _36_2003 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_36_2003) with
| (env1, _36_2002) -> begin
(
# 1100 "FStar.Tc.Tc.fst"
let _36_2016 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _36_2006 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _115_825 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _115_825))
end else begin
(
# 1106 "FStar.Tc.Tc.fst"
let _36_2009 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_36_2009) with
| (t, f) -> begin
(
# 1107 "FStar.Tc.Tc.fst"
let _36_2010 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _115_827 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _115_826 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _115_827 _115_826)))
end else begin
()
end
in (
# 1108 "FStar.Tc.Tc.fst"
let t = (norm_t env1 t)
in (
# 1109 "FStar.Tc.Tc.fst"
let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end
end)
in (match (_36_2016) with
| (f, env1) -> begin
(
# 1112 "FStar.Tc.Tc.fst"
let _36_2022 = (tc_exp (
# 1112 "FStar.Tc.Tc.fst"
let _36_2017 = env1
in {FStar_Tc_Env.solver = _36_2017.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_2017.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_2017.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_2017.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_2017.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_2017.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_2017.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_2017.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_2017.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_2017.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_2017.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_2017.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_2017.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_2017.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _36_2017.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_2017.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_2017.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_2017.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_2017.FStar_Tc_Env.default_effects}) e1)
in (match (_36_2022) with
| (e1, c1, g1) -> begin
(
# 1113 "FStar.Tc.Tc.fst"
let _36_2026 = (let _115_831 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _36_2023 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _115_831 e1 c1 f))
in (match (_36_2026) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_36_2028) -> begin
(
# 1116 "FStar.Tc.Tc.fst"
let _36_2042 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(
# 1118 "FStar.Tc.Tc.fst"
let _36_2032 = (let _115_832 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _115_832 c1))
in (match (_36_2032) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1121 "FStar.Tc.Tc.fst"
let _36_2033 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _115_833 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _115_833 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _115_834 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_115_834, c1)))
end
end))
end else begin
(
# 1124 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (
# 1125 "FStar.Tc.Tc.fst"
let _36_2036 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1126 "FStar.Tc.Tc.fst"
let _36_2038 = (FStar_Tc_Util.check_unresolved_implicits g)
in (let _115_835 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _115_835)))))
end
in (match (_36_2042) with
| (e2, c1) -> begin
(
# 1128 "FStar.Tc.Tc.fst"
let _36_2047 = if env.FStar_Tc_Env.generalize then begin
(let _115_836 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _115_836))
end else begin
(x, e1, c1)
end
in (match (_36_2047) with
| (_36_2044, e1, c1) -> begin
(
# 1131 "FStar.Tc.Tc.fst"
let cres = (let _115_837 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _115_837))
in (
# 1132 "FStar.Tc.Tc.fst"
let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _115_838 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _115_838 (None, cres)))
end
in (
# 1135 "FStar.Tc.Tc.fst"
let _36_2050 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _115_847 = (let _115_846 = (w cres)
in (let _115_845 = (let _115_844 = (let _115_843 = (let _115_842 = (let _115_841 = (FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1))
in (_115_841)::[])
in (false, _115_842))
in (_115_843, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _115_844))
in (FStar_All.pipe_left _115_846 _115_845)))
in (_115_847, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(
# 1139 "FStar.Tc.Tc.fst"
let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (
# 1140 "FStar.Tc.Tc.fst"
let _36_2058 = (let _115_848 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _115_848 e2))
in (match (_36_2058) with
| (e2, c2, g2) -> begin
(
# 1141 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (
# 1142 "FStar.Tc.Tc.fst"
let e = (let _115_856 = (w cres)
in (let _115_855 = (let _115_854 = (let _115_853 = (let _115_852 = (let _115_851 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1))
in (_115_851)::[])
in (false, _115_852))
in (_115_853, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _115_854))
in (FStar_All.pipe_left _115_856 _115_855)))
in (
# 1143 "FStar.Tc.Tc.fst"
let g2 = (let _115_865 = (let _115_858 = (let _115_857 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_115_857)::[])
in (FStar_Tc_Rel.close_guard _115_858))
in (let _115_864 = (let _115_863 = (let _115_862 = (let _115_861 = (let _115_860 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _115_860 e1))
in (FStar_All.pipe_left (fun _115_859 -> FStar_Tc_Rel.NonTrivial (_115_859)) _115_861))
in (FStar_Tc_Rel.guard_of_guard_formula _115_862))
in (FStar_Tc_Rel.imp_guard _115_863 g2))
in (FStar_All.pipe_left _115_865 _115_864)))
in (
# 1145 "FStar.Tc.Tc.fst"
let guard = (let _115_866 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _115_866))
in (match (topt) with
| None -> begin
(
# 1148 "FStar.Tc.Tc.fst"
let tres = cres.FStar_Absyn_Syntax.res_typ
in (
# 1149 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_typ tres)
in if (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs) then begin
(
# 1151 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (
# 1152 "FStar.Tc.Tc.fst"
let _36_2067 = (let _115_867 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _115_867))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _36_2070 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _36_2073), _36_2076) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(
# 1162 "FStar.Tc.Tc.fst"
let env = (instantiate_both env)
in (
# 1163 "FStar.Tc.Tc.fst"
let _36_2088 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_36_2088) with
| (env0, topt) -> begin
(
# 1164 "FStar.Tc.Tc.fst"
let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _36_9 -> (match (_36_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_36_2097); FStar_Absyn_Syntax.lbtyp = _36_2095; FStar_Absyn_Syntax.lbeff = _36_2093; FStar_Absyn_Syntax.lbdef = _36_2091} -> begin
true
end
| _36_2101 -> begin
false
end))))
in (
# 1166 "FStar.Tc.Tc.fst"
let _36_2126 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _36_2105 _36_2111 -> (match ((_36_2105, _36_2111)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _36_2108; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 1167 "FStar.Tc.Tc.fst"
let _36_2116 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_36_2116) with
| (_36_2113, t, check_t) -> begin
(
# 1169 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Util.unascribe e)
in (
# 1170 "FStar.Tc.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
(let _115_871 = (tc_typ_check_trivial (
# 1183 "FStar.Tc.Tc.fst"
let _36_2118 = env0
in {FStar_Tc_Env.solver = _36_2118.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_2118.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_2118.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_2118.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_2118.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_2118.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_2118.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_2118.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_2118.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_2118.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_2118.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_2118.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_2118.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_2118.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_2118.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _36_2118.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_2118.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_2118.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_2118.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _115_871 (norm_t env)))
end
in (
# 1184 "FStar.Tc.Tc.fst"
let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(
# 1186 "FStar.Tc.Tc.fst"
let _36_2121 = env
in {FStar_Tc_Env.solver = _36_2121.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_2121.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_2121.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_2121.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_2121.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_2121.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_2121.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_2121.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_2121.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_2121.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_2121.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_2121.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_2121.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_2121.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_2121.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_2121.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_2121.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_2121.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_2121.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_36_2126) with
| (lbs, env') -> begin
(
# 1191 "FStar.Tc.Tc.fst"
let _36_2141 = (let _115_877 = (let _115_876 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _115_876 (FStar_List.map (fun _36_2130 -> (match (_36_2130) with
| (x, t, e) -> begin
(
# 1192 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (
# 1193 "FStar.Tc.Tc.fst"
let _36_2132 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_875 = (FStar_Absyn_Print.lbname_to_string x)
in (let _115_874 = (FStar_Absyn_Print.exp_to_string e)
in (let _115_873 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _115_875 _115_874 _115_873))))
end else begin
()
end
in (
# 1195 "FStar.Tc.Tc.fst"
let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (
# 1196 "FStar.Tc.Tc.fst"
let _36_2138 = (tc_total_exp env' e)
in (match (_36_2138) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _115_877 FStar_List.unzip))
in (match (_36_2141) with
| (lbs, gs) -> begin
(
# 1199 "FStar.Tc.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (
# 1201 "FStar.Tc.Tc.fst"
let _36_2160 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _115_879 = (FStar_List.map (fun _36_2146 -> (match (_36_2146) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_115_879, g_lbs))
end else begin
(
# 1205 "FStar.Tc.Tc.fst"
let _36_2147 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (
# 1206 "FStar.Tc.Tc.fst"
let ecs = (let _115_882 = (FStar_All.pipe_right lbs (FStar_List.map (fun _36_2152 -> (match (_36_2152) with
| (x, t, e) -> begin
(let _115_881 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb (x, t, e)))
in (x, e, _115_881))
end))))
in (FStar_Tc_Util.generalize true env _115_882))
in (let _115_884 = (FStar_List.map (fun _36_2157 -> (match (_36_2157) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_115_884, FStar_Tc_Rel.trivial_guard))))
end
in (match (_36_2160) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(
# 1211 "FStar.Tc.Tc.fst"
let cres = (let _115_885 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _115_885))
in (
# 1212 "FStar.Tc.Tc.fst"
let _36_2162 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (
# 1213 "FStar.Tc.Tc.fst"
let _36_2164 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _115_889 = (let _115_888 = (w cres)
in (FStar_All.pipe_left _115_888 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_115_889, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(
# 1215 "FStar.Tc.Tc.fst"
let _36_2180 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _36_2168 _36_2175 -> (match ((_36_2168, _36_2175)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _36_2172; FStar_Absyn_Syntax.lbdef = _36_2170}) -> begin
(
# 1216 "FStar.Tc.Tc.fst"
let b = (binding_of_lb x t)
in (
# 1217 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_36_2180) with
| (bindings, env) -> begin
(
# 1219 "FStar.Tc.Tc.fst"
let _36_2184 = (tc_exp env e1)
in (match (_36_2184) with
| (e1, cres, g1) -> begin
(
# 1220 "FStar.Tc.Tc.fst"
let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (
# 1221 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (
# 1222 "FStar.Tc.Tc.fst"
let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (
# 1223 "FStar.Tc.Tc.fst"
let cres = (
# 1223 "FStar.Tc.Tc.fst"
let _36_2188 = cres
in {FStar_Absyn_Syntax.eff_name = _36_2188.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _36_2188.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _36_2188.FStar_Absyn_Syntax.comp})
in (
# 1225 "FStar.Tc.Tc.fst"
let e = (let _115_894 = (w cres)
in (FStar_All.pipe_left _115_894 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_36_2193) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1229 "FStar.Tc.Tc.fst"
let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _36_10 -> (match (_36_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_36_2205); FStar_Absyn_Syntax.lbtyp = _36_2203; FStar_Absyn_Syntax.lbeff = _36_2201; FStar_Absyn_Syntax.lbdef = _36_2199} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _36_2213; FStar_Absyn_Syntax.lbeff = _36_2211; FStar_Absyn_Syntax.lbdef = _36_2209} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _36_2222; FStar_Absyn_Syntax.lbeff = _36_2220; FStar_Absyn_Syntax.lbdef = _36_2218}) -> begin
(
# 1234 "FStar.Tc.Tc.fst"
let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (
# 1235 "FStar.Tc.Tc.fst"
let _36_2228 = (let _115_896 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _115_896))
in (e, cres, guard)))
end
| _36_2231 -> begin
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
and tc_eqn : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp)  ->  ((FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun scrutinee_x pat_t env _36_2238 -> (match (_36_2238) with
| (pattern, when_clause, branch) -> begin
(
# 1249 "FStar.Tc.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1250 "FStar.Tc.Tc.fst"
let _36_2246 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_36_2246) with
| (bindings, exps, p) -> begin
(
# 1251 "FStar.Tc.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (
# 1252 "FStar.Tc.Tc.fst"
let _36_2255 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _36_11 -> (match (_36_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _115_909 = (FStar_Absyn_Print.strBvd x)
in (let _115_908 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _115_909 _115_908)))
end
| _36_2254 -> begin
()
end))))
end else begin
()
end
in (
# 1256 "FStar.Tc.Tc.fst"
let _36_2260 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_36_2260) with
| (env1, _36_2259) -> begin
(
# 1257 "FStar.Tc.Tc.fst"
let env1 = (
# 1257 "FStar.Tc.Tc.fst"
let _36_2261 = env1
in {FStar_Tc_Env.solver = _36_2261.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_2261.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_2261.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_2261.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_2261.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_2261.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_2261.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_2261.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _36_2261.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_2261.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_2261.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_2261.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_2261.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_2261.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_2261.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_2261.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_2261.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_2261.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_2261.FStar_Tc_Env.default_effects})
in (
# 1258 "FStar.Tc.Tc.fst"
let expected_pat_t = (let _115_910 = (FStar_Tc_Rel.unrefine env pat_t)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env _115_910))
in (
# 1259 "FStar.Tc.Tc.fst"
let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1260 "FStar.Tc.Tc.fst"
let _36_2266 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_913 = (FStar_Absyn_Print.exp_to_string e)
in (let _115_912 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _115_913 _115_912)))
end else begin
()
end
in (
# 1262 "FStar.Tc.Tc.fst"
let _36_2271 = (tc_exp env1 e)
in (match (_36_2271) with
| (e, lc, g) -> begin
(
# 1263 "FStar.Tc.Tc.fst"
let _36_2272 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_915 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _115_914 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _115_915 _115_914)))
end else begin
()
end
in (
# 1265 "FStar.Tc.Tc.fst"
let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (
# 1266 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g g')
in (
# 1267 "FStar.Tc.Tc.fst"
let _36_2276 = (let _115_916 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _115_916))
in (
# 1268 "FStar.Tc.Tc.fst"
let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (
# 1269 "FStar.Tc.Tc.fst"
let _36_2279 = if (let _115_919 = (let _115_918 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _115_917 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _115_918 _115_917)))
in (FStar_All.pipe_left Prims.op_Negation _115_919)) then begin
(let _115_924 = (let _115_923 = (let _115_922 = (let _115_921 = (FStar_Absyn_Print.exp_to_string e')
in (let _115_920 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _115_921 _115_920)))
in (_115_922, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_115_923))
in (Prims.raise _115_924))
end else begin
()
end
in e))))))
end))))))
in (
# 1273 "FStar.Tc.Tc.fst"
let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (
# 1274 "FStar.Tc.Tc.fst"
let _36_2290 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _36_12 -> (match (_36_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _115_927 = (FStar_Absyn_Print.strBvd x)
in (let _115_926 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _115_927 _115_926)))
end
| _36_2289 -> begin
()
end))))
end else begin
()
end
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (
# 1281 "FStar.Tc.Tc.fst"
let _36_2297 = (tc_pat true pat_t pattern)
in (match (_36_2297) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(
# 1282 "FStar.Tc.Tc.fst"
let _36_2307 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(
# 1289 "FStar.Tc.Tc.fst"
let _36_2304 = (let _115_928 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _115_928 e))
in (match (_36_2304) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_36_2307) with
| (when_clause, g_when) -> begin
(
# 1291 "FStar.Tc.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _115_930 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _115_929 -> Some (_115_929)) _115_930))
end)
in (
# 1294 "FStar.Tc.Tc.fst"
let _36_2315 = (tc_exp pat_env branch)
in (match (_36_2315) with
| (branch, c, g_branch) -> begin
(
# 1295 "FStar.Tc.Tc.fst"
let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (
# 1296 "FStar.Tc.Tc.fst"
let _36_2320 = (let _115_931 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _115_931 FStar_Tc_Env.clear_expected_typ))
in (match (_36_2320) with
| (scrutinee_env, _36_2319) -> begin
(
# 1297 "FStar.Tc.Tc.fst"
let c = (
# 1298 "FStar.Tc.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1299 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _36_2334 -> begin
(
# 1305 "FStar.Tc.Tc.fst"
let clause = (let _115_935 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _115_934 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _115_935 _115_934 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _115_937 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _115_936 -> Some (_115_936)) _115_937))
end))
end))) None))
in (
# 1309 "FStar.Tc.Tc.fst"
let c = (match ((eqs, when_condition)) with
| (None, None) -> begin
c
end
| (Some (f), None) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (f)))
end
| (Some (f), Some (w)) -> begin
(let _115_940 = (let _115_939 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _115_938 -> FStar_Tc_Rel.NonTrivial (_115_938)) _115_939))
in (FStar_Tc_Util.weaken_precondition env c _115_940))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (
# 1316 "FStar.Tc.Tc.fst"
let discriminate = (fun scrutinee f -> (
# 1317 "FStar.Tc.Tc.fst"
let disc = (let _115_946 = (let _115_945 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _115_945))
in (FStar_All.pipe_left _115_946 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (
# 1318 "FStar.Tc.Tc.fst"
let disc = (let _115_949 = (let _115_948 = (let _115_947 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_115_947)::[])
in (disc, _115_948))
in (FStar_Absyn_Syntax.mk_Exp_app _115_949 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (
# 1321 "FStar.Tc.Tc.fst"
let rec mk_guard = (fun scrutinee pat_exp -> (
# 1322 "FStar.Tc.Tc.fst"
let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_36_2392) -> begin
(let _115_958 = (let _115_957 = (let _115_956 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _115_955 = (let _115_954 = (FStar_Absyn_Syntax.varg pat_exp)
in (_115_954)::[])
in (_115_956)::_115_955))
in (FStar_Absyn_Util.teq, _115_957))
in (FStar_Absyn_Syntax.mk_Typ_app _115_958 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _36_2396) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _36_2409); FStar_Absyn_Syntax.tk = _36_2406; FStar_Absyn_Syntax.pos = _36_2404; FStar_Absyn_Syntax.fvs = _36_2402; FStar_Absyn_Syntax.uvs = _36_2400}, args) -> begin
(
# 1331 "FStar.Tc.Tc.fst"
let head = (discriminate scrutinee f)
in (
# 1332 "FStar.Tc.Tc.fst"
let sub_term_guards = (let _115_967 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_36_2420) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(
# 1335 "FStar.Tc.Tc.fst"
let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in if (let _115_961 = (FStar_Tc_Env.is_projector env projector)
in (FStar_All.pipe_left Prims.op_Negation _115_961)) then begin
[]
end else begin
(
# 1338 "FStar.Tc.Tc.fst"
let sub_term = (let _115_965 = (let _115_964 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _115_963 = (let _115_962 = (FStar_Absyn_Syntax.varg scrutinee)
in (_115_962)::[])
in (_115_964, _115_963)))
in (FStar_Absyn_Syntax.mk_Exp_app _115_965 None f.FStar_Absyn_Syntax.p))
in (let _115_966 = (mk_guard sub_term ei)
in (_115_966)::[]))
end)
end))))
in (FStar_All.pipe_right _115_967 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _36_2428 -> begin
(let _115_970 = (let _115_969 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _115_968 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _115_969 _115_968)))
in (FStar_All.failwith _115_970))
end)))
in (
# 1342 "FStar.Tc.Tc.fst"
let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(
# 1345 "FStar.Tc.Tc.fst"
let t = (mk_guard s pat)
in (
# 1346 "FStar.Tc.Tc.fst"
let _36_2437 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_36_2437) with
| (t, _36_2436) -> begin
t
end)))
end)
in (
# 1348 "FStar.Tc.Tc.fst"
let path_guard = (let _115_979 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _115_978 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _115_978)))))
in (FStar_All.pipe_right _115_979 FStar_Absyn_Util.mk_disj_l))
in (
# 1349 "FStar.Tc.Tc.fst"
let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (
# 1352 "FStar.Tc.Tc.fst"
let guard = (let _115_980 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _115_980))
in (
# 1353 "FStar.Tc.Tc.fst"
let _36_2445 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _115_981 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _115_981))
end else begin
()
end
in (let _115_983 = (let _115_982 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _115_982))
in ((pattern, when_clause, branch), path_guard, c, _115_983))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1358 "FStar.Tc.Tc.fst"
let _36_2451 = (tc_kind env k)
in (match (_36_2451) with
| (k, g) -> begin
(
# 1359 "FStar.Tc.Tc.fst"
let _36_2452 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd) = (fun env t -> (
# 1363 "FStar.Tc.Tc.fst"
let _36_2459 = (tc_typ env t)
in (match (_36_2459) with
| (t, k, g) -> begin
(
# 1364 "FStar.Tc.Tc.fst"
let _36_2460 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env t k -> (
# 1368 "FStar.Tc.Tc.fst"
let _36_2467 = (tc_typ_check env t k)
in (match (_36_2467) with
| (t, f) -> begin
(
# 1369 "FStar.Tc.Tc.fst"
let _36_2468 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 1373 "FStar.Tc.Tc.fst"
let _36_2475 = (tc_exp env e)
in (match (_36_2475) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(
# 1376 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (
# 1377 "FStar.Tc.Tc.fst"
let c = (let _115_993 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _115_993 (norm_c env)))
in (match ((let _115_995 = (let _115_994 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _115_994))
in (FStar_Tc_Rel.sub_comp env c _115_995))) with
| Some (g') -> begin
(let _115_996 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _115_996))
end
| _36_2481 -> begin
(let _115_999 = (let _115_998 = (let _115_997 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_115_997, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_998))
in (Prims.raise _115_999))
end)))
end
end)))
and tc_ghost_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 1383 "FStar.Tc.Tc.fst"
let _36_2487 = (tc_exp env e)
in (match (_36_2487) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(
# 1386 "FStar.Tc.Tc.fst"
let c = (let _115_1002 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _115_1002 (norm_c env)))
in (
# 1387 "FStar.Tc.Tc.fst"
let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (
# 1388 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (
# 1389 "FStar.Tc.Tc.fst"
let _36_2491 = env
in {FStar_Tc_Env.solver = _36_2491.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_2491.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_2491.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_2491.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_2491.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_2491.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_2491.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_2491.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_2491.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_2491.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_2491.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_2491.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_2491.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_2491.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_2491.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_2491.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _36_2491.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_2491.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_2491.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _115_1003 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _115_1003))
end
| _36_2496 -> begin
(let _115_1006 = (let _115_1005 = (let _115_1004 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_115_1004, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_115_1005))
in (Prims.raise _115_1006))
end))))
end
end)))

# 1395 "FStar.Tc.Tc.fst"
let tc_tparams : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env) = (fun env tps -> (
# 1396 "FStar.Tc.Tc.fst"
let _36_2502 = (tc_binders env tps)
in (match (_36_2502) with
| (tps, env, g) -> begin
(
# 1397 "FStar.Tc.Tc.fst"
let _36_2503 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

# 1400 "FStar.Tc.Tc.fst"
let a_kwp_a : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _36_2522)::(FStar_Util.Inl (wp), _36_2517)::(FStar_Util.Inl (_36_2509), _36_2512)::[], _36_2526) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _36_2530 -> begin
(let _115_1019 = (let _115_1018 = (let _115_1017 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (_115_1017, (FStar_Ident.range_of_lid m)))
in FStar_Absyn_Syntax.Error (_115_1018))
in (Prims.raise _115_1019))
end))

# 1406 "FStar.Tc.Tc.fst"
let rec tc_eff_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.eff_decl = (fun env m -> (
# 1407 "FStar.Tc.Tc.fst"
let _36_2536 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_36_2536) with
| (binders, env, g) -> begin
(
# 1408 "FStar.Tc.Tc.fst"
let _36_2537 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1409 "FStar.Tc.Tc.fst"
let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (
# 1410 "FStar.Tc.Tc.fst"
let _36_2542 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_36_2542) with
| (a, kwp_a) -> begin
(
# 1411 "FStar.Tc.Tc.fst"
let a_typ = (FStar_Absyn_Util.btvar_to_typ a)
in (
# 1412 "FStar.Tc.Tc.fst"
let b = (FStar_Absyn_Util.gen_bvar_p (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname) FStar_Absyn_Syntax.ktype)
in (
# 1413 "FStar.Tc.Tc.fst"
let b_typ = (FStar_Absyn_Util.btvar_to_typ b)
in (
# 1414 "FStar.Tc.Tc.fst"
let kwp_b = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (
# 1415 "FStar.Tc.Tc.fst"
let kwlp_a = kwp_a
in (
# 1416 "FStar.Tc.Tc.fst"
let kwlp_b = kwp_b
in (
# 1417 "FStar.Tc.Tc.fst"
let a_kwp_b = (let _115_1032 = (let _115_1031 = (let _115_1030 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_115_1030)::[])
in (_115_1031, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1032 a_typ.FStar_Absyn_Syntax.pos))
in (
# 1418 "FStar.Tc.Tc.fst"
let a_kwlp_b = a_kwp_b
in (
# 1419 "FStar.Tc.Tc.fst"
let w = (fun k -> (k (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname)))
in (
# 1420 "FStar.Tc.Tc.fst"
let ret = (
# 1421 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1046 = (let _115_1045 = (let _115_1044 = (let _115_1043 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1042 = (let _115_1041 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_115_1041)::[])
in (_115_1043)::_115_1042))
in (_115_1044, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1045))
in (FStar_All.pipe_left w _115_1046))
in (let _115_1047 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _115_1047 (norm_t env))))
in (
# 1423 "FStar.Tc.Tc.fst"
let bind_wp = (
# 1424 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1062 = (let _115_1061 = (let _115_1060 = (let _115_1059 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1058 = (let _115_1057 = (FStar_Absyn_Syntax.t_binder b)
in (let _115_1056 = (let _115_1055 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _115_1054 = (let _115_1053 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _115_1052 = (let _115_1051 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _115_1050 = (let _115_1049 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_115_1049)::[])
in (_115_1051)::_115_1050))
in (_115_1053)::_115_1052))
in (_115_1055)::_115_1054))
in (_115_1057)::_115_1056))
in (_115_1059)::_115_1058))
in (_115_1060, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1061))
in (FStar_All.pipe_left w _115_1062))
in (let _115_1063 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _115_1063 (norm_t env))))
in (
# 1429 "FStar.Tc.Tc.fst"
let bind_wlp = (
# 1430 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1074 = (let _115_1073 = (let _115_1072 = (let _115_1071 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1070 = (let _115_1069 = (FStar_Absyn_Syntax.t_binder b)
in (let _115_1068 = (let _115_1067 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _115_1066 = (let _115_1065 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_115_1065)::[])
in (_115_1067)::_115_1066))
in (_115_1069)::_115_1068))
in (_115_1071)::_115_1070))
in (_115_1072, kwlp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1073))
in (FStar_All.pipe_left w _115_1074))
in (let _115_1075 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _115_1075 (norm_t env))))
in (
# 1435 "FStar.Tc.Tc.fst"
let if_then_else = (
# 1436 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1086 = (let _115_1085 = (let _115_1084 = (let _115_1083 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1082 = (let _115_1081 = (FStar_Absyn_Syntax.t_binder b)
in (let _115_1080 = (let _115_1079 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _115_1078 = (let _115_1077 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_115_1077)::[])
in (_115_1079)::_115_1078))
in (_115_1081)::_115_1080))
in (_115_1083)::_115_1082))
in (_115_1084, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1085))
in (FStar_All.pipe_left w _115_1086))
in (let _115_1087 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _115_1087 (norm_t env))))
in (
# 1441 "FStar.Tc.Tc.fst"
let ite_wp = (
# 1442 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1096 = (let _115_1095 = (let _115_1094 = (let _115_1093 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1092 = (let _115_1091 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _115_1090 = (let _115_1089 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_115_1089)::[])
in (_115_1091)::_115_1090))
in (_115_1093)::_115_1092))
in (_115_1094, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1095))
in (FStar_All.pipe_left w _115_1096))
in (let _115_1097 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _115_1097 (norm_t env))))
in (
# 1447 "FStar.Tc.Tc.fst"
let ite_wlp = (
# 1448 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1104 = (let _115_1103 = (let _115_1102 = (let _115_1101 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1100 = (let _115_1099 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_115_1099)::[])
in (_115_1101)::_115_1100))
in (_115_1102, kwlp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1103))
in (FStar_All.pipe_left w _115_1104))
in (let _115_1105 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _115_1105 (norm_t env))))
in (
# 1452 "FStar.Tc.Tc.fst"
let wp_binop = (
# 1453 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1117 = (let _115_1116 = (let _115_1115 = (let _115_1114 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1113 = (let _115_1112 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _115_1111 = (let _115_1110 = (let _115_1107 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _115_1107))
in (let _115_1109 = (let _115_1108 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_115_1108)::[])
in (_115_1110)::_115_1109))
in (_115_1112)::_115_1111))
in (_115_1114)::_115_1113))
in (_115_1115, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1116))
in (FStar_All.pipe_left w _115_1117))
in (let _115_1118 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _115_1118 (norm_t env))))
in (
# 1459 "FStar.Tc.Tc.fst"
let wp_as_type = (
# 1460 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1125 = (let _115_1124 = (let _115_1123 = (let _115_1122 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1121 = (let _115_1120 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_115_1120)::[])
in (_115_1122)::_115_1121))
in (_115_1123, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1124))
in (FStar_All.pipe_left w _115_1125))
in (let _115_1126 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _115_1126 (norm_t env))))
in (
# 1464 "FStar.Tc.Tc.fst"
let close_wp = (
# 1465 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1135 = (let _115_1134 = (let _115_1133 = (let _115_1132 = (FStar_Absyn_Syntax.t_binder b)
in (let _115_1131 = (let _115_1130 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1129 = (let _115_1128 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_115_1128)::[])
in (_115_1130)::_115_1129))
in (_115_1132)::_115_1131))
in (_115_1133, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1134))
in (FStar_All.pipe_left w _115_1135))
in (let _115_1136 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _115_1136 (norm_t env))))
in (
# 1469 "FStar.Tc.Tc.fst"
let close_wp_t = (
# 1470 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1149 = (let _115_1148 = (let _115_1147 = (let _115_1146 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1145 = (let _115_1144 = (let _115_1143 = (let _115_1142 = (let _115_1141 = (let _115_1140 = (let _115_1139 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_115_1139)::[])
in (_115_1140, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1141))
in (FStar_All.pipe_left w _115_1142))
in (FStar_Absyn_Syntax.null_t_binder _115_1143))
in (_115_1144)::[])
in (_115_1146)::_115_1145))
in (_115_1147, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1148))
in (FStar_All.pipe_left w _115_1149))
in (let _115_1150 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _115_1150 (norm_t env))))
in (
# 1474 "FStar.Tc.Tc.fst"
let _36_2576 = (
# 1475 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1159 = (let _115_1158 = (let _115_1157 = (let _115_1156 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1155 = (let _115_1154 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _115_1153 = (let _115_1152 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_115_1152)::[])
in (_115_1154)::_115_1153))
in (_115_1156)::_115_1155))
in (_115_1157, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1158))
in (FStar_All.pipe_left w _115_1159))
in (let _115_1163 = (let _115_1160 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _115_1160 (norm_t env)))
in (let _115_1162 = (let _115_1161 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _115_1161 (norm_t env)))
in (_115_1163, _115_1162))))
in (match (_36_2576) with
| (assert_p, assume_p) -> begin
(
# 1479 "FStar.Tc.Tc.fst"
let null_wp = (
# 1480 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1168 = (let _115_1167 = (let _115_1166 = (let _115_1165 = (FStar_Absyn_Syntax.t_binder a)
in (_115_1165)::[])
in (_115_1166, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1167))
in (FStar_All.pipe_left w _115_1168))
in (let _115_1169 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _115_1169 (norm_t env))))
in (
# 1482 "FStar.Tc.Tc.fst"
let trivial_wp = (
# 1483 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1176 = (let _115_1175 = (let _115_1174 = (let _115_1173 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1172 = (let _115_1171 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_115_1171)::[])
in (_115_1173)::_115_1172))
in (_115_1174, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1175))
in (FStar_All.pipe_left w _115_1176))
in (let _115_1177 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _115_1177 (norm_t env))))
in {FStar_Absyn_Syntax.mname = m.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = m.FStar_Absyn_Syntax.qualifiers; FStar_Absyn_Syntax.signature = mk; FStar_Absyn_Syntax.ret = ret; FStar_Absyn_Syntax.bind_wp = bind_wp; FStar_Absyn_Syntax.bind_wlp = bind_wlp; FStar_Absyn_Syntax.if_then_else = if_then_else; FStar_Absyn_Syntax.ite_wp = ite_wp; FStar_Absyn_Syntax.ite_wlp = ite_wlp; FStar_Absyn_Syntax.wp_binop = wp_binop; FStar_Absyn_Syntax.wp_as_type = wp_as_type; FStar_Absyn_Syntax.close_wp = close_wp; FStar_Absyn_Syntax.close_wp_t = close_wp_t; FStar_Absyn_Syntax.assert_p = assert_p; FStar_Absyn_Syntax.assume_p = assume_p; FStar_Absyn_Syntax.null_wp = null_wp; FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.bool  ->  (FStar_Absyn_Syntax.sigelt * FStar_Tc_Env.env) = (fun env se deserialized -> (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (p, r) -> begin
(
# 1508 "FStar.Tc.Tc.fst"
let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.GoOn -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end))
in (match (p) with
| FStar_Absyn_Syntax.SetOptions (o) -> begin
(
# 1514 "FStar.Tc.Tc.fst"
let _36_2597 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Absyn_Syntax.ResetOptions (sopt) -> begin
(
# 1517 "FStar.Tc.Tc.fst"
let _36_2601 = (let _115_1185 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _115_1185 Prims.ignore))
in (
# 1518 "FStar.Tc.Tc.fst"
let _36_2606 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 1521 "FStar.Tc.Tc.fst"
let _36_2608 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (se, env))))
end))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, r) -> begin
(
# 1526 "FStar.Tc.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 1527 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ne, r))
in (
# 1528 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 1532 "FStar.Tc.Tc.fst"
let _36_2623 = (let _115_1186 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _115_1186))
in (match (_36_2623) with
| (a, kwp_a_src) -> begin
(
# 1533 "FStar.Tc.Tc.fst"
let _36_2626 = (let _115_1187 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _115_1187))
in (match (_36_2626) with
| (b, kwp_b_tgt) -> begin
(
# 1534 "FStar.Tc.Tc.fst"
let kwp_a_tgt = (let _115_1191 = (let _115_1190 = (let _115_1189 = (let _115_1188 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _115_1188))
in FStar_Util.Inl (_115_1189))
in (_115_1190)::[])
in (FStar_Absyn_Util.subst_kind _115_1191 kwp_b_tgt))
in (
# 1535 "FStar.Tc.Tc.fst"
let expected_k = (let _115_1197 = (let _115_1196 = (let _115_1195 = (let _115_1194 = (FStar_Absyn_Syntax.t_binder a)
in (let _115_1193 = (let _115_1192 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_115_1192)::[])
in (_115_1194)::_115_1193))
in (_115_1195, kwp_a_tgt))
in (FStar_Absyn_Syntax.mk_Kind_arrow _115_1196))
in (FStar_All.pipe_right r _115_1197))
in (
# 1536 "FStar.Tc.Tc.fst"
let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (
# 1537 "FStar.Tc.Tc.fst"
let sub = (
# 1537 "FStar.Tc.Tc.fst"
let _36_2630 = sub
in {FStar_Absyn_Syntax.source = _36_2630.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _36_2630.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (
# 1538 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (
# 1539 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(
# 1543 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1544 "FStar.Tc.Tc.fst"
let _36_2647 = (tc_tparams env tps)
in (match (_36_2647) with
| (tps, env) -> begin
(
# 1545 "FStar.Tc.Tc.fst"
let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _36_2650 -> begin
(tc_kind_trivial env k)
end)
in (
# 1548 "FStar.Tc.Tc.fst"
let _36_2652 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _115_1200 = (FStar_Absyn_Print.sli lid)
in (let _115_1199 = (let _115_1198 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _115_1198))
in (FStar_Util.print2 "Checked %s at kind %s\n" _115_1200 _115_1199)))
end else begin
()
end
in (
# 1549 "FStar.Tc.Tc.fst"
let k = (norm_k env k)
in (
# 1550 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (
# 1551 "FStar.Tc.Tc.fst"
let _36_2670 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_36_2665); FStar_Absyn_Syntax.tk = _36_2663; FStar_Absyn_Syntax.pos = _36_2661; FStar_Absyn_Syntax.fvs = _36_2659; FStar_Absyn_Syntax.uvs = _36_2657} -> begin
(let _115_1201 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _115_1201))
end
| _36_2669 -> begin
()
end)
in (
# 1554 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(
# 1558 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 1559 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1560 "FStar.Tc.Tc.fst"
let _36_2683 = (tc_tparams env tps)
in (match (_36_2683) with
| (tps, env) -> begin
(
# 1561 "FStar.Tc.Tc.fst"
let k = (tc_kind_trivial env k)
in (
# 1562 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r))
in (
# 1563 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, tps, c, tags, r) -> begin
(
# 1567 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 1568 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1569 "FStar.Tc.Tc.fst"
let _36_2698 = (tc_tparams env tps)
in (match (_36_2698) with
| (tps, env) -> begin
(
# 1570 "FStar.Tc.Tc.fst"
let _36_2701 = (tc_comp env c)
in (match (_36_2701) with
| (c, g) -> begin
(
# 1571 "FStar.Tc.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _36_13 -> (match (_36_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(
# 1573 "FStar.Tc.Tc.fst"
let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _115_1204 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _115_1203 -> Some (_115_1203)))
in FStar_Absyn_Syntax.DefaultEffect (_115_1204)))
end
| t -> begin
t
end))))
in (
# 1576 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, tps, c, tags, r))
in (
# 1577 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))
end))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, tags, r) -> begin
(
# 1581 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1582 "FStar.Tc.Tc.fst"
let _36_2721 = (tc_tparams env tps)
in (match (_36_2721) with
| (tps, env') -> begin
(
# 1583 "FStar.Tc.Tc.fst"
let _36_2727 = (let _115_1208 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _115_1208 (fun _36_2724 -> (match (_36_2724) with
| (t, k) -> begin
(let _115_1207 = (norm_t env' t)
in (let _115_1206 = (norm_k env' k)
in (_115_1207, _115_1206)))
end))))
in (match (_36_2727) with
| (t, k1) -> begin
(
# 1584 "FStar.Tc.Tc.fst"
let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _36_2730 -> begin
(
# 1586 "FStar.Tc.Tc.fst"
let k2 = (let _115_1209 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _115_1209 (norm_k env)))
in (
# 1587 "FStar.Tc.Tc.fst"
let _36_2732 = (let _115_1210 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _115_1210))
in k2))
end)
in (
# 1588 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k2, t, tags, r))
in (
# 1589 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end))
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, (tname, tps, k), quals, mutuals, r) -> begin
(
# 1593 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1594 "FStar.Tc.Tc.fst"
let _36_2752 = (tc_binders env tps)
in (match (_36_2752) with
| (tps, env, g) -> begin
(
# 1595 "FStar.Tc.Tc.fst"
let tycon = (tname, tps, k)
in (
# 1596 "FStar.Tc.Tc.fst"
let _36_2754 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1597 "FStar.Tc.Tc.fst"
let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (
# 1598 "FStar.Tc.Tc.fst"
let t = (norm_t env t)
in (
# 1600 "FStar.Tc.Tc.fst"
let _36_2766 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _36_2763 -> begin
([], t)
end)
in (match (_36_2766) with
| (formals, result_t) -> begin
(
# 1604 "FStar.Tc.Tc.fst"
let cardinality_and_positivity_check = (fun formal -> (
# 1605 "FStar.Tc.Tc.fst"
let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _36_2774 -> (match (_36_2774) with
| (a, _36_2773) -> begin
(match (a) with
| FStar_Util.Inl (_36_2776) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(
# 1609 "FStar.Tc.Tc.fst"
let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _115_1218 = (FStar_Absyn_Util.compress_typ t)
in _115_1218.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _115_1222 = (let _115_1221 = (let _115_1220 = (let _115_1219 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _115_1219 tname))
in (_115_1220, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_115_1221))
in (Prims.raise _115_1222))
end)
end
| _36_2789 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(
# 1621 "FStar.Tc.Tc.fst"
let _36_2792 = if (FStar_Options.warn_cardinality ()) then begin
(let _115_1223 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _115_1223))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _115_1226 = (let _115_1225 = (let _115_1224 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_115_1224, r))
in FStar_Absyn_Syntax.Error (_115_1225))
in (Prims.raise _115_1226))
end else begin
()
end
end
in (
# 1627 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_36_2796) -> begin
(
# 1630 "FStar.Tc.Tc.fst"
let _36_2801 = (FStar_Absyn_Util.kind_formals k)
in (match (_36_2801) with
| (formals, _36_2800) -> begin
(check_positivity formals)
end))
end
| _36_2803 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(
# 1636 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(
# 1638 "FStar.Tc.Tc.fst"
let _36_2810 = (let _115_1227 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _115_1227 FStar_Util.must))
in (match (_36_2810) with
| (formals, _36_2809) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (
# 1641 "FStar.Tc.Tc.fst"
let _36_2811 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (
# 1643 "FStar.Tc.Tc.fst"
let _36_2865 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _115_1231 = (let _115_1230 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _115_1230 Prims.fst))
in (FStar_List.forall2 (fun _36_2818 _36_2822 -> (match ((_36_2818, _36_2822)) with
| ((a, _36_2817), (b, _36_2821)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _36_2830; FStar_Absyn_Syntax.pos = _36_2828; FStar_Absyn_Syntax.fvs = _36_2826; FStar_Absyn_Syntax.uvs = _36_2824}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _36_2845; FStar_Absyn_Syntax.pos = _36_2843; FStar_Absyn_Syntax.fvs = _36_2841; FStar_Absyn_Syntax.uvs = _36_2839}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _36_2854 -> begin
false
end)
end)) _115_1231 tps))))) then begin
(
# 1650 "FStar.Tc.Tc.fst"
let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _36_2857 -> begin
(
# 1653 "FStar.Tc.Tc.fst"
let _36_2861 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_36_2861) with
| (_36_2859, expected_args) -> begin
(let _115_1232 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _115_1232 expected_args))
end))
end)
in (let _115_1236 = (let _115_1235 = (let _115_1234 = (let _115_1233 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _115_1233 result_t expected_t))
in (_115_1234, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_115_1235))
in (Prims.raise _115_1236)))
end else begin
()
end
end
| _36_2864 -> begin
(let _115_1241 = (let _115_1240 = (let _115_1239 = (let _115_1238 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _115_1237 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _115_1238 result_t _115_1237)))
in (_115_1239, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_115_1240))
in (Prims.raise _115_1241))
end)
in (
# 1657 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (
# 1658 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (
# 1659 "FStar.Tc.Tc.fst"
let _36_2869 = if (log env) then begin
(let _115_1243 = (let _115_1242 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _115_1242))
in (FStar_All.pipe_left FStar_Util.print_string _115_1243))
end else begin
()
end
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(
# 1663 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1664 "FStar.Tc.Tc.fst"
let t = (let _115_1244 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _115_1244 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (
# 1665 "FStar.Tc.Tc.fst"
let _36_2879 = (FStar_Tc_Util.check_uvars r t)
in (
# 1666 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (
# 1667 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (
# 1668 "FStar.Tc.Tc.fst"
let _36_2883 = if (log env) then begin
(let _115_1246 = (let _115_1245 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _115_1245))
in (FStar_All.pipe_left FStar_Util.print_string _115_1246))
end else begin
()
end
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 1672 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1673 "FStar.Tc.Tc.fst"
let phi = (let _115_1247 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _115_1247 (norm_t env)))
in (
# 1674 "FStar.Tc.Tc.fst"
let _36_2893 = (FStar_Tc_Util.check_uvars r phi)
in (
# 1675 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 1676 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 1681 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1682 "FStar.Tc.Tc.fst"
let _36_2946 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _36_2906 lb -> (match (_36_2906) with
| (gen, lbs) -> begin
(
# 1683 "FStar.Tc.Tc.fst"
let _36_2943 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_36_2915); FStar_Absyn_Syntax.lbtyp = _36_2913; FStar_Absyn_Syntax.lbeff = _36_2911; FStar_Absyn_Syntax.lbdef = _36_2909} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _36_2920; FStar_Absyn_Syntax.lbdef = e} -> begin
(
# 1686 "FStar.Tc.Tc.fst"
let _36_2940 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _36_2928) -> begin
(
# 1689 "FStar.Tc.Tc.fst"
let _36_2931 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _115_1250 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _115_1250 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _115_1251 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _115_1251))
end
| _36_2935 -> begin
(
# 1695 "FStar.Tc.Tc.fst"
let _36_2936 = if (not (deserialized)) then begin
(let _115_1253 = (let _115_1252 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _115_1252))
in (FStar_All.pipe_left FStar_Util.print_string _115_1253))
end else begin
()
end
in (let _115_1254 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _115_1254)))
end))
end)
in (match (_36_2940) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_36_2943) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_36_2946) with
| (generalize, lbs') -> begin
(
# 1700 "FStar.Tc.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 1701 "FStar.Tc.Tc.fst"
let e = (let _115_1259 = (let _115_1258 = (let _115_1257 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _115_1257 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((Prims.fst lbs), lbs'), _115_1258))
in (FStar_Absyn_Syntax.mk_Exp_let _115_1259 None r))
in (
# 1702 "FStar.Tc.Tc.fst"
let _36_2981 = (match ((tc_exp (
# 1702 "FStar.Tc.Tc.fst"
let _36_2949 = env
in {FStar_Tc_Env.solver = _36_2949.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_2949.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_2949.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_2949.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_2949.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_2949.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_2949.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_2949.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_2949.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_2949.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_2949.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_2949.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _36_2949.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_2949.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_2949.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_2949.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _36_2949.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _36_2949.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _36_2949.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _36_2958; FStar_Absyn_Syntax.pos = _36_2956; FStar_Absyn_Syntax.fvs = _36_2954; FStar_Absyn_Syntax.uvs = _36_2952}, _36_2965, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(
# 1704 "FStar.Tc.Tc.fst"
let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_36_2969, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _36_2975 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _36_2978 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_36_2981) with
| (se, lbs) -> begin
(
# 1709 "FStar.Tc.Tc.fst"
let _36_2987 = if (log env) then begin
(let _115_1265 = (let _115_1264 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1711 "FStar.Tc.Tc.fst"
let should_log = (match ((let _115_1261 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _115_1261))) with
| None -> begin
true
end
| _36_2985 -> begin
false
end)
in if should_log then begin
(let _115_1263 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _115_1262 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _115_1263 _115_1262)))
end else begin
""
end))))
in (FStar_All.pipe_right _115_1264 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _115_1265))
end else begin
()
end
in (
# 1717 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))
end))))
end)))
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(
# 1721 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1722 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (
# 1723 "FStar.Tc.Tc.fst"
let _36_2999 = (tc_exp env e)
in (match (_36_2999) with
| (e, c, g1) -> begin
(
# 1724 "FStar.Tc.Tc.fst"
let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (
# 1725 "FStar.Tc.Tc.fst"
let _36_3005 = (let _115_1269 = (let _115_1266 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_115_1266))
in (let _115_1268 = (let _115_1267 = (c.FStar_Absyn_Syntax.comp ())
in (e, _115_1267))
in (check_expected_effect env _115_1269 _115_1268)))
in (match (_36_3005) with
| (e, _36_3003, g) -> begin
(
# 1726 "FStar.Tc.Tc.fst"
let _36_3006 = (let _115_1270 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _115_1270))
in (
# 1727 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (
# 1728 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 1732 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1733 "FStar.Tc.Tc.fst"
let _36_3025 = (FStar_All.pipe_right ses (FStar_List.partition (fun _36_14 -> (match (_36_14) with
| FStar_Absyn_Syntax.Sig_tycon (_36_3019) -> begin
true
end
| _36_3022 -> begin
false
end))))
in (match (_36_3025) with
| (tycons, rest) -> begin
(
# 1734 "FStar.Tc.Tc.fst"
let _36_3034 = (FStar_All.pipe_right rest (FStar_List.partition (fun _36_15 -> (match (_36_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_36_3028) -> begin
true
end
| _36_3031 -> begin
false
end))))
in (match (_36_3034) with
| (abbrevs, rest) -> begin
(
# 1735 "FStar.Tc.Tc.fst"
let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _36_16 -> (match (_36_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(
# 1737 "FStar.Tc.Tc.fst"
let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _115_1274 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _115_1274 Prims.fst))
end
| _36_3046 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _36_3049 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1742 "FStar.Tc.Tc.fst"
let _36_3053 = (FStar_List.split recs)
in (match (_36_3053) with
| (recs, abbrev_defs) -> begin
(
# 1743 "FStar.Tc.Tc.fst"
let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _115_1275 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _115_1275))
end else begin
""
end
in (
# 1746 "FStar.Tc.Tc.fst"
let _36_3055 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (
# 1747 "FStar.Tc.Tc.fst"
let _36_3060 = (tc_decls env tycons deserialized)
in (match (_36_3060) with
| (tycons, _36_3059) -> begin
(
# 1748 "FStar.Tc.Tc.fst"
let _36_3064 = (tc_decls env recs deserialized)
in (match (_36_3064) with
| (recs, _36_3063) -> begin
(
# 1749 "FStar.Tc.Tc.fst"
let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (
# 1750 "FStar.Tc.Tc.fst"
let _36_3069 = (tc_decls env1 rest deserialized)
in (match (_36_3069) with
| (rest, _36_3068) -> begin
(
# 1751 "FStar.Tc.Tc.fst"
let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(
# 1753 "FStar.Tc.Tc.fst"
let tt = (let _115_1278 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _115_1278))
in (
# 1754 "FStar.Tc.Tc.fst"
let _36_3085 = (tc_typ_trivial env1 tt)
in (match (_36_3085) with
| (tt, _36_3084) -> begin
(
# 1755 "FStar.Tc.Tc.fst"
let _36_3094 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _36_3091 -> begin
([], tt)
end)
in (match (_36_3094) with
| (tps, t) -> begin
(let _115_1280 = (let _115_1279 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _115_1279, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_115_1280))
end))
end)))
end
| _36_3096 -> begin
(let _115_1282 = (let _115_1281 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _115_1281))
in (FStar_All.failwith _115_1282))
end)) recs abbrev_defs)
in (
# 1761 "FStar.Tc.Tc.fst"
let _36_3098 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
in (
# 1762 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append (FStar_List.append tycons abbrevs) rest), quals, lids, r))
in (
# 1763 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))
end)))
end))
end))))
end)))
end))
end)))
end))
and tc_decls : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.bool  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Tc_Env.env) = (fun env ses deserialized -> (
# 1767 "FStar.Tc.Tc.fst"
let time_tc_decl = (fun env se ds -> (
# 1768 "FStar.Tc.Tc.fst"
let start = (FStar_Util.now ())
in (
# 1769 "FStar.Tc.Tc.fst"
let res = (tc_decl env se ds)
in (
# 1770 "FStar.Tc.Tc.fst"
let stop = (FStar_Util.now ())
in (
# 1771 "FStar.Tc.Tc.fst"
let diff = (FStar_Util.time_diff start stop)
in (
# 1772 "FStar.Tc.Tc.fst"
let _36_3113 = (let _115_1292 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _115_1292))
in res))))))
in (
# 1775 "FStar.Tc.Tc.fst"
let _36_3128 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _36_3117 se -> (match (_36_3117) with
| (ses, env) -> begin
(
# 1777 "FStar.Tc.Tc.fst"
let _36_3119 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _115_1296 = (let _115_1295 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _115_1295))
in (FStar_Util.print_string _115_1296))
end else begin
()
end
in (
# 1779 "FStar.Tc.Tc.fst"
let _36_3123 = if (FStar_ST.read FStar_Options.timing) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_36_3123) with
| (se, env) -> begin
(
# 1783 "FStar.Tc.Tc.fst"
let _36_3124 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in ((se)::ses, env))
end)))
end)) ([], env)))
in (match (_36_3128) with
| (ses, env) -> begin
((FStar_List.rev ses), env)
end))))

# 1789 "FStar.Tc.Tc.fst"
let rec for_export : FStar_Tc_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (
# 1811 "FStar.Tc.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _36_17 -> (match (_36_17) with
| FStar_Absyn_Syntax.Abstract -> begin
true
end
| _36_3137 -> begin
false
end)))))
in (
# 1812 "FStar.Tc.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Absyn_Syntax.Projector (l, _)) | (FStar_Absyn_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _36_3147 -> begin
false
end))
in (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (_36_3149) -> begin
([], hidden)
end
| FStar_Absyn_Syntax.Sig_datacon (_36_3152) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, binders, knd, def, quals, r) -> begin
if (is_abstract quals) then begin
(
# 1826 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((lid, binders, knd, [], [], (FStar_Absyn_Syntax.Assumption)::quals, r))
in ((se)::[], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _36_3172, _36_3174) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _36_3180 -> (match (_36_3180) with
| (out, hidden) -> begin
(match (se) with
| FStar_Absyn_Syntax.Sig_tycon (l, bs, t, _36_3185, _36_3187, quals, r) -> begin
(
# 1834 "FStar.Tc.Tc.fst"
let dec = FStar_Absyn_Syntax.Sig_tycon ((l, bs, t, [], [], quals, r))
in ((dec)::out, hidden))
end
| FStar_Absyn_Syntax.Sig_datacon (l, t, _tc, quals, _mutuals, r) -> begin
(
# 1837 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Env.lookup_datacon env l)
in (
# 1838 "FStar.Tc.Tc.fst"
let dec = FStar_Absyn_Syntax.Sig_val_decl ((l, t, (FStar_Absyn_Syntax.Assumption)::[], r))
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
| FStar_Absyn_Syntax.Sig_assume (_36_3205, _36_3207, quals, _36_3210) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _36_18 -> (match (_36_18) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _36_3228 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Absyn_Syntax.Sig_main (_36_3230) -> begin
([], hidden)
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_let ((false, lb::[]), _36_3246, _36_3248, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 1868 "FStar.Tc.Tc.fst"
let lid = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(
# 1871 "FStar.Tc.Tc.fst"
let dec = FStar_Absyn_Syntax.Sig_val_decl ((lid, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _115_1314 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _115_1313 = (let _115_1312 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_115_1312, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::quals, r))
in FStar_Absyn_Syntax.Sig_val_decl (_115_1313)))))
in (_115_1314, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 1880 "FStar.Tc.Tc.fst"
let get_exports : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env modul -> (
# 1881 "FStar.Tc.Tc.fst"
let _36_3273 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.fold_left (fun _36_3265 se -> (match (_36_3265) with
| (exports, hidden) -> begin
(
# 1882 "FStar.Tc.Tc.fst"
let _36_3269 = (for_export env hidden se)
in (match (_36_3269) with
| (exports', hidden) -> begin
((exports')::exports, hidden)
end))
end)) ([], [])))
in (match (_36_3273) with
| (exports, _36_3272) -> begin
(FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
end)))

# 1886 "FStar.Tc.Tc.fst"
let tc_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1887 "FStar.Tc.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (
# 1888 "FStar.Tc.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 1889 "FStar.Tc.Tc.fst"
let env = (
# 1889 "FStar.Tc.Tc.fst"
let _36_3278 = env
in (let _115_1325 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _36_3278.FStar_Tc_Env.solver; FStar_Tc_Env.range = _36_3278.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _36_3278.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _36_3278.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _36_3278.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _36_3278.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _36_3278.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _36_3278.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _36_3278.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _36_3278.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _36_3278.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _36_3278.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _36_3278.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _36_3278.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _36_3278.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _36_3278.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _36_3278.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _115_1325; FStar_Tc_Env.default_effects = _36_3278.FStar_Tc_Env.default_effects}))
in (
# 1890 "FStar.Tc.Tc.fst"
let _36_3281 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (
# 1891 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (
# 1892 "FStar.Tc.Tc.fst"
let _36_3286 = (tc_decls env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_36_3286) with
| (ses, env) -> begin
((
# 1893 "FStar.Tc.Tc.fst"
let _36_3287 = modul
in {FStar_Absyn_Syntax.name = _36_3287.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _36_3287.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _36_3287.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _36_3287.FStar_Absyn_Syntax.is_deserialized}), env)
end))))))))

# 1895 "FStar.Tc.Tc.fst"
let tc_more_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul decls -> (
# 1896 "FStar.Tc.Tc.fst"
let _36_3294 = (tc_decls env decls false)
in (match (_36_3294) with
| (ses, env) -> begin
(
# 1897 "FStar.Tc.Tc.fst"
let modul = (
# 1897 "FStar.Tc.Tc.fst"
let _36_3295 = modul
in {FStar_Absyn_Syntax.name = _36_3295.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _36_3295.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _36_3295.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _36_3295.FStar_Absyn_Syntax.is_deserialized})
in (modul, env))
end)))

# 1900 "FStar.Tc.Tc.fst"
let finish_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1901 "FStar.Tc.Tc.fst"
let exports = (get_exports env modul)
in (
# 1902 "FStar.Tc.Tc.fst"
let modul = (
# 1902 "FStar.Tc.Tc.fst"
let _36_3301 = modul
in {FStar_Absyn_Syntax.name = _36_3301.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _36_3301.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (
# 1903 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.finish_module env modul)
in (
# 1904 "FStar.Tc.Tc.fst"
let _36_3311 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(
# 1906 "FStar.Tc.Tc.fst"
let _36_3305 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (
# 1907 "FStar.Tc.Tc.fst"
let _36_3307 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
in (
# 1908 "FStar.Tc.Tc.fst"
let _36_3309 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _115_1336 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _115_1336 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

# 1913 "FStar.Tc.Tc.fst"
let tc_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1914 "FStar.Tc.Tc.fst"
let _36_3317 = (tc_partial_modul env modul)
in (match (_36_3317) with
| (modul, env) -> begin
(finish_partial_modul env modul)
end)))

# 1917 "FStar.Tc.Tc.fst"
let add_modul_to_tcenv : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Tc_Env.env = (fun en m -> (
# 1918 "FStar.Tc.Tc.fst"
let do_sigelt = (fun en elt -> (
# 1919 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt en elt)
in (
# 1920 "FStar.Tc.Tc.fst"
let _36_3324 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (
# 1923 "FStar.Tc.Tc.fst"
let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _115_1349 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _115_1349 m)))))

# 1926 "FStar.Tc.Tc.fst"
let check_module : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env) = (fun env m -> (
# 1927 "FStar.Tc.Tc.fst"
let _36_3329 = if ((let _115_1354 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _115_1354)) <> 0) then begin
(let _115_1355 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _115_1355))
end else begin
()
end
in (
# 1930 "FStar.Tc.Tc.fst"
let _36_3333 = (tc_modul env m)
in (match (_36_3333) with
| (m, env) -> begin
(
# 1931 "FStar.Tc.Tc.fst"
let _36_3334 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _115_1356 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _115_1356))
end else begin
()
end
in ((m)::[], env))
end))))




