
open Prims
# 30 "FStar.Tc.Tc.fst"
let syn' = (fun env k -> (let _122_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _122_11 (Some (k)))))

# 31 "FStar.Tc.Tc.fst"
let log : FStar_Tc_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _122_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _122_14))))))

# 32 "FStar.Tc.Tc.fst"
let rng : FStar_Tc_Env.env  ->  FStar_Range.range = (fun env -> (FStar_Tc_Env.get_range env))

# 33 "FStar.Tc.Tc.fst"
let instantiate_both : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (
# 33 "FStar.Tc.Tc.fst"
let _43_24 = env
in {FStar_Tc_Env.solver = _43_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _43_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_24.FStar_Tc_Env.default_effects}))

# 34 "FStar.Tc.Tc.fst"
let no_inst : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (
# 34 "FStar.Tc.Tc.fst"
let _43_27 = env
in {FStar_Tc_Env.solver = _43_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _43_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_27.FStar_Tc_Env.default_effects}))

# 35 "FStar.Tc.Tc.fst"
let mk_lex_list : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 37 "FStar.Tc.Tc.fst"
let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _122_34 = (let _122_33 = (let _122_32 = (let _122_27 = (let _122_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _122_25 -> FStar_Util.Inl (_122_25)) _122_26))
in (_122_27, Some (FStar_Absyn_Syntax.Implicit (false))))
in (let _122_31 = (let _122_30 = (FStar_Absyn_Syntax.varg v)
in (let _122_29 = (let _122_28 = (FStar_Absyn_Syntax.varg tl)
in (_122_28)::[])
in (_122_30)::_122_29))
in (_122_32)::_122_31))
in (FStar_Absyn_Util.lex_pair, _122_33))
in (FStar_Absyn_Syntax.mk_Exp_app _122_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

# 39 "FStar.Tc.Tc.fst"
let is_eq : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _43_1 -> (match (_43_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _43_37 -> begin
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
let norm_t : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _122_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _122_47 env t)))

# 48 "FStar.Tc.Tc.fst"
let norm_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let _122_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _122_52 env k)))

# 49 "FStar.Tc.Tc.fst"
let norm_c : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun env c -> (let _122_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _122_57 env c)))

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
(let _122_76 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _122_76))
end
| FStar_Util.Inr (t) -> begin
(let _122_77 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _122_77))
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
let fail = (fun _43_61 -> (match (()) with
| () -> begin
(
# 62 "FStar.Tc.Tc.fst"
let escaping = (let _122_82 = (let _122_81 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _122_81 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _122_82 (FStar_String.concat ", ")))
in (
# 63 "FStar.Tc.Tc.fst"
let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _122_83 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _122_83))
end else begin
(let _122_84 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _122_84))
end
in (let _122_87 = (let _122_86 = (let _122_85 = (FStar_Tc_Env.get_range env)
in (msg, _122_85))
in FStar_Absyn_Syntax.Error (_122_86))
in (Prims.raise _122_87))))
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
| _43_71 -> begin
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
| _43_78 -> begin
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
let maybe_make_subst = (fun _43_2 -> (match (_43_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _43_99 -> begin
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
(let _122_98 = (let _122_97 = (let _122_96 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _122_96))
in FStar_Util.Inl (_122_97))
in (_122_98)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _122_101 = (let _122_100 = (let _122_99 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _122_99))
in FStar_Util.Inr (_122_100))
in (_122_101)::s)
end
end
| _43_114 -> begin
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
| _43_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

# 113 "FStar.Tc.Tc.fst"
let set_lcomp_result : FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.lcomp = (fun lc t -> (
# 114 "FStar.Tc.Tc.fst"
let _43_132 = lc
in {FStar_Absyn_Syntax.eff_name = _43_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _43_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _43_134 -> (match (()) with
| () -> begin
(let _122_110 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _122_110 t))
end))}))

# 116 "FStar.Tc.Tc.fst"
let value_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, FStar_Absyn_Syntax.lcomp) FStar_Util.either  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e tlc -> (
# 117 "FStar.Tc.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _122_117 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _122_117))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 122 "FStar.Tc.Tc.fst"
let t = lc.FStar_Absyn_Syntax.res_typ
in (
# 123 "FStar.Tc.Tc.fst"
let _43_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(
# 126 "FStar.Tc.Tc.fst"
let _43_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_119 = (FStar_Absyn_Print.typ_to_string t)
in (let _122_118 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _122_119 _122_118)))
end else begin
()
end
in (
# 128 "FStar.Tc.Tc.fst"
let _43_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_43_151) with
| (e, g) -> begin
(
# 129 "FStar.Tc.Tc.fst"
let _43_154 = (let _122_125 = (FStar_All.pipe_left (fun _122_124 -> Some (_122_124)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _122_125 env e lc g))
in (match (_43_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_43_158) with
| (e, lc, g) -> begin
(
# 131 "FStar.Tc.Tc.fst"
let _43_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_126 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _122_126))
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
let check_expected_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp Prims.option  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp)  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env copt _43_171 -> (match (_43_171) with
| (e, c) -> begin
(
# 141 "FStar.Tc.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_43_173) -> begin
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
(let _122_139 = (norm_c env c)
in (e, _122_139, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 162 "FStar.Tc.Tc.fst"
let _43_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_142 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _122_141 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _122_140 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _122_142 _122_141 _122_140))))
end else begin
()
end
in (
# 164 "FStar.Tc.Tc.fst"
let c = (norm_c env c)
in (
# 165 "FStar.Tc.Tc.fst"
let expected_c' = (let _122_143 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _122_143))
in (
# 166 "FStar.Tc.Tc.fst"
let _43_195 = (let _122_144 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _122_144))
in (match (_43_195) with
| (e, _43_193, g) -> begin
(
# 167 "FStar.Tc.Tc.fst"
let _43_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_146 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _122_145 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _122_146 _122_145)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

# 170 "FStar.Tc.Tc.fst"
let no_logical_guard = (fun env _43_202 -> (match (_43_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _122_152 = (let _122_151 = (let _122_150 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _122_149 = (FStar_Tc_Env.get_range env)
in (_122_150, _122_149)))
in FStar_Absyn_Syntax.Error (_122_151))
in (Prims.raise _122_152))
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
(let _122_159 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _122_159))
end))

# 182 "FStar.Tc.Tc.fst"
let with_implicits = (fun imps _43_220 -> (match (_43_220) with
| (e, l, g) -> begin
(e, l, (
# 182 "FStar.Tc.Tc.fst"
let _43_221 = g
in {FStar_Tc_Rel.guard_f = _43_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _43_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

# 183 "FStar.Tc.Tc.fst"
let add_implicit : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * Prims.int64), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * Prims.int64)) FStar_Util.either  ->  FStar_Tc_Rel.guard_t  ->  FStar_Tc_Rel.guard_t = (fun u g -> (
# 183 "FStar.Tc.Tc.fst"
let _43_225 = g
in {FStar_Tc_Rel.guard_f = _43_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _43_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

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
let _43_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _122_212 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _122_211 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _122_212 _122_211)))
end else begin
()
end
in (
# 195 "FStar.Tc.Tc.fst"
let _43_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_43_249) with
| (env, _43_248) -> begin
(
# 196 "FStar.Tc.Tc.fst"
let _43_252 = (tc_args env args)
in (match (_43_252) with
| (args, g) -> begin
(let _122_214 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_122_214, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _43_263; FStar_Absyn_Syntax.pos = _43_261; FStar_Absyn_Syntax.fvs = _43_259; FStar_Absyn_Syntax.uvs = _43_257}) -> begin
(
# 200 "FStar.Tc.Tc.fst"
let _43_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_43_272) with
| (_43_269, binders, body) -> begin
(
# 201 "FStar.Tc.Tc.fst"
let _43_275 = (tc_args env args)
in (match (_43_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _122_218 = (let _122_217 = (let _122_216 = (let _122_215 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _122_215))
in (_122_216, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_217))
in (Prims.raise _122_218))
end else begin
(
# 204 "FStar.Tc.Tc.fst"
let _43_308 = (FStar_List.fold_left2 (fun _43_279 b a -> (match (_43_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(
# 207 "FStar.Tc.Tc.fst"
let _43_289 = (let _122_222 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _122_222))
in (match (_43_289) with
| (t, g) -> begin
(
# 208 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _122_224 = (let _122_223 = (FStar_Absyn_Syntax.targ t)
in (_122_223)::args)
in (subst, _122_224, (g)::guards)))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(
# 211 "FStar.Tc.Tc.fst"
let env = (let _122_225 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _122_225))
in (
# 212 "FStar.Tc.Tc.fst"
let _43_301 = (tc_ghost_exp env e)
in (match (_43_301) with
| (e, _43_299, g) -> begin
(
# 213 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (let _122_227 = (let _122_226 = (FStar_Absyn_Syntax.varg e)
in (_122_226)::args)
in (subst, _122_227, (g)::guards)))
end)))
end
| _43_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_43_308) with
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
in (let _122_230 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _122_230))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(
# 224 "FStar.Tc.Tc.fst"
let _43_319 = (tc_kind env k)
in (match (_43_319) with
| (k, f) -> begin
(
# 225 "FStar.Tc.Tc.fst"
let _43_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_43_322) with
| (args, g) -> begin
(
# 226 "FStar.Tc.Tc.fst"
let kabr = ((Prims.fst kabr), args)
in (
# 227 "FStar.Tc.Tc.fst"
let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _122_232 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _122_232))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 231 "FStar.Tc.Tc.fst"
let _43_332 = (tc_binders env bs)
in (match (_43_332) with
| (bs, env, g) -> begin
(
# 232 "FStar.Tc.Tc.fst"
let _43_335 = (tc_kind env k)
in (match (_43_335) with
| (k, f) -> begin
(
# 233 "FStar.Tc.Tc.fst"
let f = (FStar_Tc_Rel.close_guard bs f)
in (let _122_235 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _122_234 = (FStar_Tc_Rel.conj_guard g f)
in (_122_235, _122_234))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _122_236 = (FStar_Tc_Util.new_kvar env)
in (_122_236, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder : FStar_Tc_Env.env  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env x -> (
# 240 "FStar.Tc.Tc.fst"
let _43_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_43_342) with
| (t, g) -> begin
(
# 241 "FStar.Tc.Tc.fst"
let x = (
# 241 "FStar.Tc.Tc.fst"
let _43_343 = x
in {FStar_Absyn_Syntax.v = _43_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _43_343.FStar_Absyn_Syntax.p})
in (
# 242 "FStar.Tc.Tc.fst"
let env' = (let _122_239 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _122_239))
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
let _43_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_43_362) with
| (k, g) -> begin
(
# 252 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inl ((
# 252 "FStar.Tc.Tc.fst"
let _43_363 = a
in {FStar_Absyn_Syntax.v = _43_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _43_363.FStar_Absyn_Syntax.p})), imp)
in (
# 253 "FStar.Tc.Tc.fst"
let env' = (maybe_push_binding env b)
in (
# 254 "FStar.Tc.Tc.fst"
let _43_370 = (aux env' bs)
in (match (_43_370) with
| (bs, env', g') -> begin
(let _122_247 = (let _122_246 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _122_246))
in ((b)::bs, env', _122_247))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(
# 258 "FStar.Tc.Tc.fst"
let _43_376 = (tc_vbinder env x)
in (match (_43_376) with
| (x, env', g) -> begin
(
# 259 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inr (x), imp)
in (
# 260 "FStar.Tc.Tc.fst"
let _43_381 = (aux env' bs)
in (match (_43_381) with
| (bs, env', g') -> begin
(let _122_249 = (let _122_248 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _122_248))
in ((b)::bs, env', _122_249))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.args * FStar_Tc_Rel.guard_t) = (fun env args -> (FStar_List.fold_right (fun _43_386 _43_389 -> (match ((_43_386, _43_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(
# 268 "FStar.Tc.Tc.fst"
let _43_396 = (tc_typ env t)
in (match (_43_396) with
| (t, _43_394, g') -> begin
(let _122_254 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _122_254))
end))
end
| FStar_Util.Inr (e) -> begin
(
# 271 "FStar.Tc.Tc.fst"
let _43_403 = (tc_ghost_exp env e)
in (match (_43_403) with
| (e, _43_401, g') -> begin
(let _122_255 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _122_255))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list Prims.list  ->  (FStar_Absyn_Syntax.args Prims.list * FStar_Tc_Rel.guard_t) = (fun env pats -> (FStar_List.fold_right (fun p _43_409 -> (match (_43_409) with
| (pats, g) -> begin
(
# 275 "FStar.Tc.Tc.fst"
let _43_412 = (tc_args env p)
in (match (_43_412) with
| (args, g') -> begin
(let _122_260 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _122_260))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 280 "FStar.Tc.Tc.fst"
let _43_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_43_419) with
| (t, g) -> begin
(let _122_263 = (FStar_Absyn_Syntax.mk_Total t)
in (_122_263, g))
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
let tc = (let _122_266 = (let _122_265 = (let _122_264 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_122_264)::c.FStar_Absyn_Syntax.effect_args)
in (head, _122_265))
in (FStar_Absyn_Syntax.mk_Typ_app _122_266 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (
# 287 "FStar.Tc.Tc.fst"
let _43_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_43_427) with
| (tc, f) -> begin
(
# 288 "FStar.Tc.Tc.fst"
let _43_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_43_431) with
| (_43_429, args) -> begin
(
# 289 "FStar.Tc.Tc.fst"
let _43_443 = (match (args) with
| (FStar_Util.Inl (res), _43_436)::args -> begin
(res, args)
end
| _43_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_43_443) with
| (res, args) -> begin
(
# 292 "FStar.Tc.Tc.fst"
let _43_459 = (let _122_268 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _43_3 -> (match (_43_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(
# 294 "FStar.Tc.Tc.fst"
let _43_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_43_450) with
| (env, _43_449) -> begin
(
# 295 "FStar.Tc.Tc.fst"
let _43_455 = (tc_ghost_exp env e)
in (match (_43_455) with
| (e, _43_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _122_268 FStar_List.unzip))
in (match (_43_459) with
| (flags, guards) -> begin
(let _122_270 = (FStar_Absyn_Syntax.mk_Comp (
# 298 "FStar.Tc.Tc.fst"
let _43_460 = c
in {FStar_Absyn_Syntax.effect_name = _43_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _43_460.FStar_Absyn_Syntax.flags}))
in (let _122_269 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_122_270, _122_269)))
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
let _43_472 = a
in {FStar_Absyn_Syntax.v = _43_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _43_472.FStar_Absyn_Syntax.p})
in (
# 311 "FStar.Tc.Tc.fst"
let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (
# 312 "FStar.Tc.Tc.fst"
let _43_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_43_479) with
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
let _43_484 = i
in {FStar_Absyn_Syntax.v = _43_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _43_484.FStar_Absyn_Syntax.p})
in (let _122_293 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_122_293, qk, FStar_Tc_Rel.trivial_guard)))))
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
let _43_491 = i
in {FStar_Absyn_Syntax.v = _43_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _43_491.FStar_Absyn_Syntax.p})
in (let _122_294 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_122_294, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(
# 329 "FStar.Tc.Tc.fst"
let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _43_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (
# 332 "FStar.Tc.Tc.fst"
let i = (
# 332 "FStar.Tc.Tc.fst"
let _43_501 = i
in {FStar_Absyn_Syntax.v = _43_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _43_501.FStar_Absyn_Syntax.p})
in (
# 333 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (
# 334 "FStar.Tc.Tc.fst"
let _43_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_43_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(
# 338 "FStar.Tc.Tc.fst"
let _43_516 = (tc_binders env bs)
in (match (_43_516) with
| (bs, env, g) -> begin
(
# 339 "FStar.Tc.Tc.fst"
let _43_519 = (tc_comp env cod)
in (match (_43_519) with
| (cod, f) -> begin
(
# 340 "FStar.Tc.Tc.fst"
let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (
# 341 "FStar.Tc.Tc.fst"
let _43_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _43_542; FStar_Absyn_Syntax.result_typ = _43_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _43_536)::(FStar_Util.Inl (post), _43_531)::(FStar_Util.Inr (pats), _43_526)::[]; FStar_Absyn_Syntax.flags = _43_522}) -> begin
(
# 345 "FStar.Tc.Tc.fst"
let rec extract_pats = (fun pats -> (match ((let _122_299 = (FStar_Absyn_Util.compress_exp pats)
in _122_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _43_557); FStar_Absyn_Syntax.tk = _43_554; FStar_Absyn_Syntax.pos = _43_552; FStar_Absyn_Syntax.fvs = _43_550; FStar_Absyn_Syntax.uvs = _43_548}, _43_572::(FStar_Util.Inr (hd), _43_569)::(FStar_Util.Inr (tl), _43_564)::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(
# 347 "FStar.Tc.Tc.fst"
let _43_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_43_578) with
| (head, args) -> begin
(
# 348 "FStar.Tc.Tc.fst"
let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _43_585 -> begin
[]
end)
in (let _122_300 = (extract_pats tl)
in (FStar_List.append pat _122_300)))
end))
end
| _43_588 -> begin
[]
end))
in (
# 354 "FStar.Tc.Tc.fst"
let pats = (let _122_301 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _122_301))
in (
# 355 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _43_594 -> (match (_43_594) with
| (b, _43_593) -> begin
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
(let _122_304 = (let _122_303 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _122_303))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _122_304))
end))))
end
| _43_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _122_306 = (let _122_305 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _122_305))
in (t, FStar_Absyn_Syntax.ktype, _122_306))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(
# 368 "FStar.Tc.Tc.fst"
let _43_613 = (tc_binders env bs)
in (match (_43_613) with
| (bs, env, g) -> begin
(
# 369 "FStar.Tc.Tc.fst"
let _43_617 = (tc_typ env t)
in (match (_43_617) with
| (t, k, f) -> begin
(
# 370 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _122_311 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _122_310 = (let _122_309 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _122_309))
in (_122_311, k, _122_310))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(
# 374 "FStar.Tc.Tc.fst"
let _43_626 = (tc_vbinder env x)
in (match (_43_626) with
| (x, env, f1) -> begin
(
# 375 "FStar.Tc.Tc.fst"
let _43_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_314 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _122_313 = (FStar_Absyn_Print.typ_to_string phi)
in (let _122_312 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _122_314 _122_313 _122_312))))
end else begin
()
end
in (
# 380 "FStar.Tc.Tc.fst"
let _43_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_43_634) with
| (phi, f2) -> begin
(let _122_321 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _122_320 = (let _122_319 = (let _122_318 = (let _122_317 = (FStar_Absyn_Syntax.v_binder x)
in (_122_317)::[])
in (FStar_Tc_Rel.close_guard _122_318 f2))
in (FStar_Tc_Rel.conj_guard f1 _122_319))
in (_122_321, FStar_Absyn_Syntax.ktype, _122_320)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(
# 384 "FStar.Tc.Tc.fst"
let _43_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_324 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _122_323 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _122_322 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _122_324 _122_323 _122_322))))
end else begin
()
end
in (
# 388 "FStar.Tc.Tc.fst"
let _43_644 = (tc_typ (no_inst env) head)
in (match (_43_644) with
| (head, k1', f1) -> begin
(
# 389 "FStar.Tc.Tc.fst"
let args0 = args
in (
# 390 "FStar.Tc.Tc.fst"
let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (
# 392 "FStar.Tc.Tc.fst"
let _43_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_328 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _122_327 = (FStar_Absyn_Print.typ_to_string head)
in (let _122_326 = (FStar_Absyn_Print.kind_to_string k1')
in (let _122_325 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _122_328 _122_327 _122_326 _122_325)))))
end else begin
()
end
in (
# 398 "FStar.Tc.Tc.fst"
let check_app = (fun _43_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_43_652) -> begin
(
# 400 "FStar.Tc.Tc.fst"
let _43_656 = (tc_args env args)
in (match (_43_656) with
| (args, g) -> begin
(
# 401 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (
# 402 "FStar.Tc.Tc.fst"
let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (
# 403 "FStar.Tc.Tc.fst"
let kres = (let _122_331 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _122_331 Prims.fst))
in (
# 404 "FStar.Tc.Tc.fst"
let bs = (let _122_332 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _122_332))
in (
# 405 "FStar.Tc.Tc.fst"
let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (
# 406 "FStar.Tc.Tc.fst"
let _43_662 = (let _122_333 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _122_333))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(
# 410 "FStar.Tc.Tc.fst"
let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _122_344 = (FStar_Absyn_Util.subst_kind subst kres)
in (_122_344, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) -> begin
(let _122_348 = (let _122_347 = (let _122_346 = (let _122_345 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _122_345))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _122_346))
in FStar_Absyn_Syntax.Error (_122_347))
in (Prims.raise _122_348))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, [])) -> begin
(
# 418 "FStar.Tc.Tc.fst"
let formal = (FStar_List.hd formals)
in (
# 419 "FStar.Tc.Tc.fst"
let _43_743 = (let _122_349 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _122_349))
in (match (_43_743) with
| (t, u) -> begin
(
# 420 "FStar.Tc.Tc.fst"
let targ = (let _122_351 = (FStar_All.pipe_left (fun _122_350 -> Some (_122_350)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _122_351))
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
let _43_776 = (let _122_352 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _122_352))
in (match (_43_776) with
| (e, u) -> begin
(
# 429 "FStar.Tc.Tc.fst"
let varg = (let _122_354 = (FStar_All.pipe_left (fun _122_353 -> Some (_122_353)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (e), _122_354))
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
let _43_797 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_356 = (FStar_Absyn_Print.arg_to_string actual)
in (let _122_355 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _122_356 _122_355)))
end else begin
()
end
in (
# 441 "FStar.Tc.Tc.fst"
let _43_803 = (tc_typ_check (
# 441 "FStar.Tc.Tc.fst"
let _43_799 = env
in {FStar_Tc_Env.solver = _43_799.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_799.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_799.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_799.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_799.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_799.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_799.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_799.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_799.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_799.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_799.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_799.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_799.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_799.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_799.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_799.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _43_799.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_799.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_799.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_43_803) with
| (t, g') -> begin
(
# 442 "FStar.Tc.Tc.fst"
let _43_804 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_357 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _122_357))
end else begin
()
end
in (
# 444 "FStar.Tc.Tc.fst"
let actual = (FStar_Util.Inl (t), imp)
in (
# 445 "FStar.Tc.Tc.fst"
let g' = (let _122_359 = (let _122_358 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _122_358))
in (FStar_Tc_Rel.imp_guard _122_359 g'))
in (
# 446 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal actual)
in (let _122_360 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _122_360 formals actuals))))))
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
let _43_820 = env'
in {FStar_Tc_Env.solver = _43_820.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_820.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_820.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_820.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_820.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_820.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_820.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_820.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_820.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_820.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_820.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_820.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_820.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_820.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_820.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_820.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _43_820.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_820.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_820.FStar_Tc_Env.default_effects})
in (
# 453 "FStar.Tc.Tc.fst"
let _43_823 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_362 = (FStar_Absyn_Print.arg_to_string actual)
in (let _122_361 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _122_362 _122_361)))
end else begin
()
end
in (
# 454 "FStar.Tc.Tc.fst"
let _43_829 = (tc_ghost_exp env' v)
in (match (_43_829) with
| (v, _43_827, g') -> begin
(
# 455 "FStar.Tc.Tc.fst"
let actual = (FStar_Util.Inr (v), imp)
in (
# 456 "FStar.Tc.Tc.fst"
let g' = (let _122_364 = (let _122_363 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _122_363))
in (FStar_Tc_Rel.imp_guard _122_364 g'))
in (
# 457 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal actual)
in (let _122_365 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _122_365 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _43_836), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(
# 463 "FStar.Tc.Tc.fst"
let tv = (FStar_Absyn_Util.b2t v)
in (let _122_367 = (let _122_366 = (FStar_Absyn_Syntax.targ tv)
in (_122_366)::actuals)
in (check_args outargs subst g ((formal)::formals) _122_367)))
end
| _43_846 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_43_848), _43_851), (FStar_Util.Inl (_43_854), _43_857)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_43_861, []) -> begin
(let _122_369 = (let _122_368 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _122_368))
in (_122_369, (FStar_List.rev outargs), g))
end
| ([], _43_866) -> begin
(let _122_377 = (let _122_376 = (let _122_375 = (let _122_374 = (let _122_372 = (let _122_371 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _43_4 -> (match (_43_4) with
| (_43_870, Some (FStar_Absyn_Syntax.Implicit (_43_872))) -> begin
false
end
| _43_877 -> begin
true
end))))
in (FStar_List.length _122_371))
in (FStar_All.pipe_right _122_372 FStar_Util.string_of_int))
in (let _122_373 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _122_374 _122_373)))
in (_122_375, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_376))
in (Prims.raise _122_377))
end))
in (check_args [] [] f1 formals args))
end
| _43_879 -> begin
(let _122_380 = (let _122_379 = (let _122_378 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_122_378, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_379))
in (Prims.raise _122_380))
end)
end))
in (match ((let _122_384 = (let _122_381 = (FStar_Absyn_Util.compress_typ head)
in _122_381.FStar_Absyn_Syntax.n)
in (let _122_383 = (let _122_382 = (FStar_Absyn_Util.compress_kind k1)
in _122_382.FStar_Absyn_Syntax.n)
in (_122_384, _122_383)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_43_881), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
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
| _43_892 -> begin
(
# 496 "FStar.Tc.Tc.fst"
let _43_896 = (check_app ())
in (match (_43_896) with
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
let _43_904 = (tc_kind env k1)
in (match (_43_904) with
| (k1, f1) -> begin
(
# 504 "FStar.Tc.Tc.fst"
let _43_907 = (tc_typ_check env t1 k1)
in (match (_43_907) with
| (t1, f2) -> begin
(let _122_388 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _122_387 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_122_388, k1, _122_387)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_43_909, k1) -> begin
(
# 508 "FStar.Tc.Tc.fst"
let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(
# 511 "FStar.Tc.Tc.fst"
let _43_918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _122_390 = (FStar_Absyn_Print.typ_to_string s)
in (let _122_389 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _122_390 _122_389)))
end else begin
()
end
in (let _122_393 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_122_393, k1, FStar_Tc_Rel.trivial_guard)))
end
| _43_921 -> begin
(
# 515 "FStar.Tc.Tc.fst"
let _43_922 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _122_395 = (FStar_Absyn_Print.typ_to_string s)
in (let _122_394 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _122_395 _122_394)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(
# 520 "FStar.Tc.Tc.fst"
let _43_933 = (tc_typ env t)
in (match (_43_933) with
| (t, k, f) -> begin
(let _122_396 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_122_396, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(
# 524 "FStar.Tc.Tc.fst"
let _43_944 = (tc_typ env t)
in (match (_43_944) with
| (t, k, f) -> begin
(let _122_397 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_122_397, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(
# 528 "FStar.Tc.Tc.fst"
let _43_953 = (tc_typ env t)
in (match (_43_953) with
| (t, k, f) -> begin
(let _122_398 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_122_398, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(
# 532 "FStar.Tc.Tc.fst"
let _43_961 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_43_961) with
| (quant, f) -> begin
(
# 533 "FStar.Tc.Tc.fst"
let _43_964 = (tc_pats env pats)
in (match (_43_964) with
| (pats, g) -> begin
(
# 534 "FStar.Tc.Tc.fst"
let g = (
# 534 "FStar.Tc.Tc.fst"
let _43_965 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _43_965.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _43_965.FStar_Tc_Rel.implicits})
in (let _122_401 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _122_400 = (FStar_Tc_Util.force_tk quant)
in (let _122_399 = (FStar_Tc_Rel.conj_guard f g)
in (_122_401, _122_400, _122_399)))))
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
| _43_972 -> begin
(let _122_403 = (let _122_402 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _122_402))
in (FStar_All.failwith _122_403))
end))))))
and tc_typ_check : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env t k -> (
# 545 "FStar.Tc.Tc.fst"
let _43_979 = (tc_typ env t)
in (match (_43_979) with
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
| FStar_Absyn_Syntax.Exp_uvar (_43_988, t1) -> begin
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
let _43_995 = x
in {FStar_Absyn_Syntax.v = _43_995.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _43_995.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (
# 563 "FStar.Tc.Tc.fst"
let _43_1001 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_43_1001) with
| (e, t, implicits) -> begin
(
# 564 "FStar.Tc.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _122_410 = (let _122_409 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _122_409))
in FStar_Util.Inr (_122_410))
end
in (let _122_411 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _122_411)))
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
let _43_1008 = v
in {FStar_Absyn_Syntax.v = _43_1008.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _43_1008.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (
# 570 "FStar.Tc.Tc.fst"
let _43_1014 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_43_1014) with
| (e, t, implicits) -> begin
(
# 572 "FStar.Tc.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _122_413 = (let _122_412 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _122_412))
in FStar_Util.Inr (_122_413))
end
in (
# 573 "FStar.Tc.Tc.fst"
let is_data_ctor = (fun _43_5 -> (match (_43_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _43_1024 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _122_419 = (let _122_418 = (let _122_417 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _122_416 = (FStar_Tc_Env.get_range env)
in (_122_417, _122_416)))
in FStar_Absyn_Syntax.Error (_122_418))
in (Prims.raise _122_419))
end else begin
(let _122_420 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _122_420))
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
let fail = (fun msg t -> (let _122_425 = (let _122_424 = (let _122_423 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_122_423, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_424))
in (Prims.raise _122_425)))
in (
# 588 "FStar.Tc.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 596 "FStar.Tc.Tc.fst"
let _43_1045 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _43_1044 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 597 "FStar.Tc.Tc.fst"
let _43_1050 = (tc_binders env bs)
in (match (_43_1050) with
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
let rec as_function_typ = (fun norm t -> (match ((let _122_434 = (FStar_Absyn_Util.compress_typ t)
in _122_434.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(
# 606 "FStar.Tc.Tc.fst"
let _43_1079 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _43_1078 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 607 "FStar.Tc.Tc.fst"
let _43_1084 = (tc_binders env bs)
in (match (_43_1084) with
| (bs, envbody, g) -> begin
(
# 608 "FStar.Tc.Tc.fst"
let _43_1088 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_43_1088) with
| (envbody, _43_1087) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(
# 620 "FStar.Tc.Tc.fst"
let rec tc_binders = (fun _43_1098 bs_annot c bs -> (match (_43_1098) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _122_443 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _122_443))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_43_1113), _43_1116), (FStar_Util.Inr (_43_1119), _43_1122)) -> begin
(
# 626 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _43_1129), (FStar_Util.Inl (b), imp)) -> begin
(
# 630 "FStar.Tc.Tc.fst"
let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 631 "FStar.Tc.Tc.fst"
let _43_1147 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _43_1139 -> begin
(
# 634 "FStar.Tc.Tc.fst"
let _43_1142 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_43_1142) with
| (k, g1) -> begin
(
# 635 "FStar.Tc.Tc.fst"
let g2 = (FStar_Tc_Rel.keq env None ka k)
in (
# 636 "FStar.Tc.Tc.fst"
let g = (let _122_444 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _122_444))
in (k, g)))
end))
end)
in (match (_43_1147) with
| (k, g) -> begin
(
# 638 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inl ((
# 638 "FStar.Tc.Tc.fst"
let _43_1148 = b
in {FStar_Absyn_Syntax.v = _43_1148.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _43_1148.FStar_Absyn_Syntax.p})), imp)
in (
# 639 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 640 "FStar.Tc.Tc.fst"
let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _43_1156), (FStar_Util.Inr (y), imp)) -> begin
(
# 644 "FStar.Tc.Tc.fst"
let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 645 "FStar.Tc.Tc.fst"
let _43_1178 = (match ((let _122_445 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _122_445.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _43_1166 -> begin
(
# 648 "FStar.Tc.Tc.fst"
let _43_1167 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_446 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _122_446))
end else begin
()
end
in (
# 649 "FStar.Tc.Tc.fst"
let _43_1173 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_43_1173) with
| (t, _43_1171, g1) -> begin
(
# 650 "FStar.Tc.Tc.fst"
let g2 = (FStar_Tc_Rel.teq env tx t)
in (
# 651 "FStar.Tc.Tc.fst"
let g = (let _122_447 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _122_447))
in (t, g)))
end)))
end)
in (match (_43_1178) with
| (t, g) -> begin
(
# 653 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inr ((
# 653 "FStar.Tc.Tc.fst"
let _43_1179 = y
in {FStar_Absyn_Syntax.v = _43_1179.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _43_1179.FStar_Absyn_Syntax.p})), imp)
in (
# 654 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 655 "FStar.Tc.Tc.fst"
let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _43_1185 -> begin
(let _122_450 = (let _122_449 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _122_448 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _122_449 _122_448)))
in (fail _122_450 t))
end)
end
| ([], _43_1188) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _43_1197; FStar_Absyn_Syntax.pos = _43_1195; FStar_Absyn_Syntax.fvs = _43_1193; FStar_Absyn_Syntax.uvs = _43_1191} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _122_452 = (let _122_451 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _122_451))
in (fail _122_452 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_43_1205, []) -> begin
(
# 669 "FStar.Tc.Tc.fst"
let c = (let _122_453 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _122_453 c.FStar_Absyn_Syntax.pos))
in (let _122_454 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _122_454)))
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
let _43_1214 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_459 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _122_459))
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
let _43_1217 = env
in {FStar_Tc_Env.solver = _43_1217.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_1217.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_1217.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_1217.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_1217.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_1217.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_1217.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_1217.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_1217.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_1217.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_1217.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_1217.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_1217.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _43_1217.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_1217.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_1217.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_1217.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_1217.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_1217.FStar_Tc_Env.default_effects})
in (
# 679 "FStar.Tc.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_43_1224), _43_1227) -> begin
[]
end
| (FStar_Util.Inr (x), _43_1232) -> begin
(match ((let _122_465 = (let _122_464 = (let _122_463 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _122_463))
in (FStar_Absyn_Util.unrefine _122_464))
in _122_465.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_43_1235) -> begin
[]
end
| _43_1238 -> begin
(let _122_466 = (FStar_Absyn_Util.bvar_to_exp x)
in (_122_466)::[])
end)
end)))))
in (
# 687 "FStar.Tc.Tc.fst"
let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (
# 688 "FStar.Tc.Tc.fst"
let as_lex_list = (fun dec -> (
# 689 "FStar.Tc.Tc.fst"
let _43_1245 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_43_1245) with
| (head, _43_1244) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _43_1248) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _43_1252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 693 "FStar.Tc.Tc.fst"
let prev_dec = (
# 694 "FStar.Tc.Tc.fst"
let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _43_6 -> (match (_43_6) with
| FStar_Absyn_Syntax.DECREASES (_43_1256) -> begin
true
end
| _43_1259 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(
# 697 "FStar.Tc.Tc.fst"
let _43_1263 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _122_475 = (let _122_474 = (let _122_473 = (let _122_471 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _122_470 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _122_471 _122_470)))
in (let _122_472 = (FStar_Tc_Env.get_range env)
in (_122_473, _122_472)))
in FStar_Absyn_Syntax.Error (_122_474))
in (Prims.raise _122_475))
end else begin
()
end
in (
# 701 "FStar.Tc.Tc.fst"
let dec = (as_lex_list dec)
in (
# 702 "FStar.Tc.Tc.fst"
let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _43_1271), (FStar_Util.Inl (actual), _43_1276)) -> begin
(let _122_479 = (let _122_478 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _122_478))
in FStar_Util.Inl (_122_479))
end
| ((FStar_Util.Inr (formal), _43_1282), (FStar_Util.Inr (actual), _43_1287)) -> begin
(let _122_481 = (let _122_480 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _122_480))
in FStar_Util.Inr (_122_481))
end
| _43_1291 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _43_1294 -> begin
(
# 709 "FStar.Tc.Tc.fst"
let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _43_1299 -> begin
(mk_lex_list actual_args)
end))
end))
in (
# 714 "FStar.Tc.Tc.fst"
let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _43_1303 -> (match (_43_1303) with
| (l, t0) -> begin
(
# 715 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _122_483 = (FStar_Absyn_Util.compress_typ t)
in _122_483.FStar_Absyn_Syntax.n)) with
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
let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _43_7 -> (match (_43_7) with
| FStar_Absyn_Syntax.DECREASES (_43_1319) -> begin
true
end
| _43_1322 -> begin
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
let subst = (let _122_487 = (let _122_486 = (let _122_485 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _122_485))
in FStar_Util.Inr (_122_486))
in (_122_487)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _122_492 = (let _122_491 = (let _122_490 = (FStar_Absyn_Syntax.varg dec)
in (let _122_489 = (let _122_488 = (FStar_Absyn_Syntax.varg prev_dec)
in (_122_488)::[])
in (_122_490)::_122_489))
in (precedes, _122_491))
in (FStar_Absyn_Syntax.mk_Typ_app _122_492 None r))))
end
| _43_1330 -> begin
(
# 731 "FStar.Tc.Tc.fst"
let formal_args = (let _122_495 = (let _122_494 = (let _122_493 = (FStar_Absyn_Syntax.v_binder y)
in (_122_493)::[])
in (FStar_List.append bs _122_494))
in (FStar_All.pipe_right _122_495 filter_types_and_functions))
in (
# 732 "FStar.Tc.Tc.fst"
let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _43_1335 -> begin
(mk_lex_list formal_args)
end)
in (let _122_500 = (let _122_499 = (let _122_498 = (FStar_Absyn_Syntax.varg lhs)
in (let _122_497 = (let _122_496 = (FStar_Absyn_Syntax.varg prev_dec)
in (_122_496)::[])
in (_122_498)::_122_497))
in (precedes, _122_499))
in (FStar_Absyn_Syntax.mk_Typ_app _122_500 None r))))
end)
in (
# 737 "FStar.Tc.Tc.fst"
let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (
# 738 "FStar.Tc.Tc.fst"
let bs = (FStar_List.append bs (((FStar_Util.Inr ((
# 738 "FStar.Tc.Tc.fst"
let _43_1339 = x
in {FStar_Absyn_Syntax.v = _43_1339.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _43_1339.FStar_Absyn_Syntax.p})), imp))::[]))
in (
# 739 "FStar.Tc.Tc.fst"
let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (
# 740 "FStar.Tc.Tc.fst"
let _43_1343 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_503 = (FStar_Absyn_Print.lbname_to_string l)
in (let _122_502 = (FStar_Absyn_Print.typ_to_string t)
in (let _122_501 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _122_503 _122_502 _122_501))))
end else begin
()
end
in (
# 743 "FStar.Tc.Tc.fst"
let _43_1350 = (let _122_505 = (let _122_504 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _122_504 Prims.fst))
in (tc_typ _122_505 t'))
in (match (_43_1350) with
| (t', _43_1347, _43_1349) -> begin
(l, t')
end)))))))))
end
| _43_1352 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _43_1354 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _122_511 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _43_1359 -> (match (_43_1359) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _122_510 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _43_8 -> (match (_43_8) with
| (FStar_Util.Inl (x), t) -> begin
(let _122_509 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_122_509)::[])
end
| _43_1366 -> begin
[]
end))))
in (_122_511, _122_510)))))))))))
end))
in (
# 755 "FStar.Tc.Tc.fst"
let _43_1371 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_43_1371) with
| (bs, envbody, g, c) -> begin
(
# 756 "FStar.Tc.Tc.fst"
let _43_1374 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_43_1374) with
| (envbody, letrecs) -> begin
(
# 757 "FStar.Tc.Tc.fst"
let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _43_1378) -> begin
(
# 763 "FStar.Tc.Tc.fst"
let _43_1388 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_43_1388) with
| (_43_1382, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _43_1390 -> begin
if (not (norm)) then begin
(let _122_512 = (whnf env t)
in (as_function_typ true _122_512))
end else begin
(
# 771 "FStar.Tc.Tc.fst"
let _43_1399 = (expected_function_typ env None)
in (match (_43_1399) with
| (_43_1392, bs, _43_1395, c_opt, envbody, g) -> begin
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
let _43_1403 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_43_1403) with
| (env, topt) -> begin
(
# 777 "FStar.Tc.Tc.fst"
let _43_1410 = (expected_function_typ env topt)
in (match (_43_1410) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 778 "FStar.Tc.Tc.fst"
let _43_1416 = (tc_exp (
# 778 "FStar.Tc.Tc.fst"
let _43_1411 = envbody
in {FStar_Tc_Env.solver = _43_1411.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_1411.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_1411.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_1411.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_1411.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_1411.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_1411.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_1411.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_1411.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_1411.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_1411.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_1411.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_1411.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_1411.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _43_1411.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _43_1411.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_1411.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_1411.FStar_Tc_Env.default_effects}) body)
in (match (_43_1416) with
| (body, cbody, guard_body) -> begin
(
# 779 "FStar.Tc.Tc.fst"
let _43_1417 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _122_515 = (FStar_Absyn_Print.exp_to_string body)
in (let _122_514 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _122_513 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _122_515 _122_514 _122_513))))
end else begin
()
end
in (
# 781 "FStar.Tc.Tc.fst"
let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (
# 782 "FStar.Tc.Tc.fst"
let _43_1420 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _122_516 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _122_516))
end else begin
()
end
in (
# 784 "FStar.Tc.Tc.fst"
let _43_1427 = (let _122_518 = (let _122_517 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _122_517))
in (check_expected_effect (
# 784 "FStar.Tc.Tc.fst"
let _43_1422 = envbody
in {FStar_Tc_Env.solver = _43_1422.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_1422.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_1422.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_1422.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_1422.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_1422.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_1422.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_1422.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_1422.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_1422.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_1422.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_1422.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_1422.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_1422.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_1422.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_1422.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _43_1422.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_1422.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_1422.FStar_Tc_Env.default_effects}) c_opt _122_518))
in (match (_43_1427) with
| (body, cbody, guard) -> begin
(
# 785 "FStar.Tc.Tc.fst"
let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (
# 786 "FStar.Tc.Tc.fst"
let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(
# 787 "FStar.Tc.Tc.fst"
let _43_1429 = (let _122_519 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _122_519))
in (
# 787 "FStar.Tc.Tc.fst"
let _43_1431 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _43_1431.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _43_1431.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
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
let e = (let _122_521 = (let _122_520 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_122_520, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _122_521 None top.FStar_Absyn_Syntax.pos))
in (
# 794 "FStar.Tc.Tc.fst"
let _43_1454 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 796 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_43_1443) -> begin
(let _122_524 = (let _122_523 = (let _122_522 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_122_522, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _122_523 None top.FStar_Absyn_Syntax.pos))
in (_122_524, t, guard))
end
| _43_1446 -> begin
(
# 805 "FStar.Tc.Tc.fst"
let _43_1449 = if use_teq then begin
(let _122_525 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _122_525))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_43_1449) with
| (e, guard') -> begin
(let _122_527 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _122_526 = (FStar_Tc_Rel.conj_guard guard guard')
in (_122_527, t, _122_526)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_43_1454) with
| (e, tfun, guard) -> begin
(
# 813 "FStar.Tc.Tc.fst"
let _43_1455 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_530 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _122_529 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _122_528 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _122_530 _122_529 _122_528))))
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
let _43_1460 = (let _122_532 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _122_532 guard))
in (match (_43_1460) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _43_1462 -> begin
(let _122_534 = (let _122_533 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _122_533))
in (FStar_All.failwith _122_534))
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
let _43_1466 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_539 = (let _122_537 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _122_537))
in (let _122_538 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _122_539 _122_538)))
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
| FStar_Absyn_Syntax.Exp_delayed (_43_1472) -> begin
(let _122_563 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _122_563))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _43_1492) -> begin
(
# 839 "FStar.Tc.Tc.fst"
let _43_1497 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_43_1497) with
| (t1, f) -> begin
(
# 840 "FStar.Tc.Tc.fst"
let _43_1501 = (let _122_564 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _122_564 e1))
in (match (_43_1501) with
| (e1, c, g) -> begin
(
# 841 "FStar.Tc.Tc.fst"
let _43_1505 = (let _122_568 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _43_1502 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _122_568 e1 c f))
in (match (_43_1505) with
| (c, f) -> begin
(
# 842 "FStar.Tc.Tc.fst"
let _43_1509 = (let _122_572 = (let _122_571 = (w c)
in (FStar_All.pipe_left _122_571 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _122_572 c))
in (match (_43_1509) with
| (e, c, f2) -> begin
(let _122_574 = (let _122_573 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _122_573))
in (e, c, _122_574))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(
# 846 "FStar.Tc.Tc.fst"
let pats_t = (let _122_580 = (let _122_579 = (let _122_575 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _122_575))
in (let _122_578 = (let _122_577 = (let _122_576 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _122_576))
in (_122_577)::[])
in (_122_579, _122_578)))
in (FStar_Absyn_Syntax.mk_Typ_app _122_580 None FStar_Absyn_Syntax.dummyRange))
in (
# 847 "FStar.Tc.Tc.fst"
let _43_1519 = (let _122_581 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _122_581 e))
in (match (_43_1519) with
| (e, t, g) -> begin
(
# 848 "FStar.Tc.Tc.fst"
let g = (
# 848 "FStar.Tc.Tc.fst"
let _43_1520 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _43_1520.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _43_1520.FStar_Tc_Rel.implicits})
in (
# 849 "FStar.Tc.Tc.fst"
let c = (let _122_582 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _122_582 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _122_583 = (FStar_Absyn_Util.compress_exp e)
in _122_583.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_43_1530, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _43_1535; FStar_Absyn_Syntax.lbeff = _43_1533; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 855 "FStar.Tc.Tc.fst"
let _43_1546 = (let _122_584 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _122_584 e1))
in (match (_43_1546) with
| (e1, c1, g1) -> begin
(
# 856 "FStar.Tc.Tc.fst"
let _43_1550 = (tc_exp env e2)
in (match (_43_1550) with
| (e2, c2, g2) -> begin
(
# 857 "FStar.Tc.Tc.fst"
let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _122_597 = (let _122_595 = (let _122_594 = (let _122_593 = (let _122_592 = (w c)
in (let _122_591 = (let _122_590 = (let _122_589 = (let _122_588 = (let _122_587 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1))
in (_122_587)::[])
in (false, _122_588))
in (_122_589, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _122_590))
in (FStar_All.pipe_left _122_592 _122_591)))
in (_122_593, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_122_594))
in (FStar_Absyn_Syntax.mk_Exp_meta _122_595))
in (let _122_596 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_122_597, c, _122_596))))
end))
end))
end
| _43_1553 -> begin
(
# 860 "FStar.Tc.Tc.fst"
let _43_1557 = (tc_exp env e)
in (match (_43_1557) with
| (e, c, g) -> begin
(let _122_598 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_122_598, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(
# 865 "FStar.Tc.Tc.fst"
let _43_1566 = (tc_exp env e)
in (match (_43_1566) with
| (e, c, g) -> begin
(let _122_599 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_122_599, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 869 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 870 "FStar.Tc.Tc.fst"
let env = (let _122_601 = (let _122_600 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _122_600 Prims.fst))
in (FStar_All.pipe_right _122_601 instantiate_both))
in (
# 871 "FStar.Tc.Tc.fst"
let _43_1573 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_603 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _122_602 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _122_603 _122_602)))
end else begin
()
end
in (
# 872 "FStar.Tc.Tc.fst"
let _43_1578 = (tc_exp (no_inst env) head)
in (match (_43_1578) with
| (head, chead, g_head) -> begin
(
# 873 "FStar.Tc.Tc.fst"
let aux = (fun _43_1580 -> (match (()) with
| () -> begin
(
# 874 "FStar.Tc.Tc.fst"
let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _43_1584) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(
# 877 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _43_1596)::(FStar_Util.Inr (e2), _43_1591)::[] -> begin
(
# 880 "FStar.Tc.Tc.fst"
let _43_1602 = (tc_exp env e1)
in (match (_43_1602) with
| (e1, c1, g1) -> begin
(
# 881 "FStar.Tc.Tc.fst"
let _43_1606 = (tc_exp env e2)
in (match (_43_1606) with
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
(let _122_609 = (let _122_606 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _122_606))
in (let _122_608 = (let _122_607 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _122_607 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _122_609 c2 _122_608)))
end else begin
(let _122_613 = (let _122_610 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _122_610))
in (let _122_612 = (let _122_611 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _122_611 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _122_613 _122_612 c2)))
end
in (
# 888 "FStar.Tc.Tc.fst"
let c = (let _122_616 = (let _122_615 = (FStar_All.pipe_left (fun _122_614 -> Some (_122_614)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_122_615, c2))
in (FStar_Tc_Util.bind env None c1 _122_616))
in (
# 889 "FStar.Tc.Tc.fst"
let e = (let _122_621 = (let _122_620 = (let _122_619 = (FStar_Absyn_Syntax.varg e1)
in (let _122_618 = (let _122_617 = (FStar_Absyn_Syntax.varg e2)
in (_122_617)::[])
in (_122_619)::_122_618))
in (head, _122_620))
in (FStar_Absyn_Syntax.mk_Exp_app _122_621 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _122_623 = (let _122_622 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _122_622))
in (e, c, _122_623)))))))
end))
end))
end
| _43_1613 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _43_1615 -> begin
(
# 896 "FStar.Tc.Tc.fst"
let thead = chead.FStar_Absyn_Syntax.res_typ
in (
# 897 "FStar.Tc.Tc.fst"
let _43_1617 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_625 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _122_624 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _122_625 _122_624)))
end else begin
()
end
in (
# 898 "FStar.Tc.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _122_630 = (FStar_Absyn_Util.unrefine tf)
in _122_630.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(
# 901 "FStar.Tc.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _43_1650)::_43_1646 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(
# 906 "FStar.Tc.Tc.fst"
let _43_1662 = (tc_exp env e)
in (match (_43_1662) with
| (e, c, g_e) -> begin
(
# 907 "FStar.Tc.Tc.fst"
let _43_1666 = (tc_args env tl)
in (match (_43_1666) with
| (args, comps, g_rest) -> begin
(let _122_635 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _122_635))
end))
end))
end))
in (
# 912 "FStar.Tc.Tc.fst"
let _43_1670 = (tc_args env args)
in (match (_43_1670) with
| (args, comps, g_args) -> begin
(
# 913 "FStar.Tc.Tc.fst"
let bs = (let _122_636 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _122_636))
in (
# 914 "FStar.Tc.Tc.fst"
let cres = (let _122_637 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _122_637 top.FStar_Absyn_Syntax.pos))
in (
# 915 "FStar.Tc.Tc.fst"
let _43_1673 = (let _122_639 = (let _122_638 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _122_638))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _122_639))
in (
# 916 "FStar.Tc.Tc.fst"
let comp = (let _122_642 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _122_642))
in (let _122_644 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _122_643 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_122_644, comp, _122_643)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 920 "FStar.Tc.Tc.fst"
let vars = (FStar_Tc_Env.binders env)
in (
# 922 "FStar.Tc.Tc.fst"
let rec tc_args = (fun _43_1690 bs cres args -> (match (_43_1690) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_43_1698)))::rest, (_43_1706, None)::_43_1704) -> begin
(
# 933 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 934 "FStar.Tc.Tc.fst"
let _43_1712 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (
# 935 "FStar.Tc.Tc.fst"
let _43_1716 = (let _122_680 = (let _122_679 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _122_679))
in (FStar_Tc_Rel.new_tvar _122_680 vars k))
in (match (_43_1716) with
| (targ, u) -> begin
(
# 936 "FStar.Tc.Tc.fst"
let _43_1717 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_682 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _122_681 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _122_682 _122_681)))
end else begin
()
end
in (
# 937 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (
# 938 "FStar.Tc.Tc.fst"
let arg = (let _122_683 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (targ), _122_683))
in (let _122_692 = (let _122_691 = (let _122_690 = (let _122_689 = (let _122_688 = (FStar_Tc_Util.as_uvar_t u)
in (_122_688, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_122_689))
in (add_implicit _122_690 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _122_691, fvs))
in (tc_args _122_692 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_43_1725)))::rest, (_43_1733, None)::_43_1731) -> begin
(
# 942 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 943 "FStar.Tc.Tc.fst"
let _43_1739 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (
# 944 "FStar.Tc.Tc.fst"
let _43_1743 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_43_1743) with
| (varg, u) -> begin
(
# 945 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (
# 946 "FStar.Tc.Tc.fst"
let arg = (let _122_693 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (varg), _122_693))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(
# 950 "FStar.Tc.Tc.fst"
let _43_1759 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_699 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _122_698 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _122_699 _122_698)))
end else begin
()
end
in (
# 951 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 952 "FStar.Tc.Tc.fst"
let _43_1762 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (
# 953 "FStar.Tc.Tc.fst"
let _43_1768 = (tc_typ_check (
# 953 "FStar.Tc.Tc.fst"
let _43_1764 = env
in {FStar_Tc_Env.solver = _43_1764.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_1764.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_1764.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_1764.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_1764.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_1764.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_1764.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_1764.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_1764.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_1764.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_1764.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_1764.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_1764.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_1764.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_1764.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_1764.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _43_1764.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_1764.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_1764.FStar_Tc_Env.default_effects}) t k)
in (match (_43_1768) with
| (t, g') -> begin
(
# 954 "FStar.Tc.Tc.fst"
let f = (let _122_700 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _122_700))
in (
# 955 "FStar.Tc.Tc.fst"
let g' = (
# 955 "FStar.Tc.Tc.fst"
let _43_1770 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _43_1770.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _43_1770.FStar_Tc_Rel.implicits})
in (
# 956 "FStar.Tc.Tc.fst"
let arg = (FStar_Util.Inl (t), aq)
in (
# 957 "FStar.Tc.Tc.fst"
let subst = (let _122_701 = (FStar_List.hd bs)
in (maybe_extend_subst subst _122_701 arg))
in (let _122_707 = (let _122_706 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _122_706, fvs))
in (tc_args _122_707 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(
# 961 "FStar.Tc.Tc.fst"
let _43_1788 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_709 = (FStar_Absyn_Print.subst_to_string subst)
in (let _122_708 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _122_709 _122_708)))
end else begin
()
end
in (
# 962 "FStar.Tc.Tc.fst"
let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 963 "FStar.Tc.Tc.fst"
let _43_1791 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_710 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _122_710))
end else begin
()
end
in (
# 964 "FStar.Tc.Tc.fst"
let _43_1793 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (
# 965 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env targ)
in (
# 966 "FStar.Tc.Tc.fst"
let env = (
# 966 "FStar.Tc.Tc.fst"
let _43_1796 = env
in {FStar_Tc_Env.solver = _43_1796.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_1796.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_1796.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_1796.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_1796.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_1796.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_1796.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_1796.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_1796.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_1796.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_1796.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_1796.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_1796.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_1796.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_1796.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_1796.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _43_1796.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_1796.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_1796.FStar_Tc_Env.default_effects})
in (
# 967 "FStar.Tc.Tc.fst"
let _43_1799 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _122_712 = (FStar_Absyn_Print.exp_to_string e)
in (let _122_711 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _122_712 _122_711)))
end else begin
()
end
in (
# 968 "FStar.Tc.Tc.fst"
let _43_1801 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_715 = (FStar_Absyn_Print.tag_of_exp e)
in (let _122_714 = (FStar_Absyn_Print.exp_to_string e)
in (let _122_713 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _122_715 _122_714 _122_713))))
end else begin
()
end
in (
# 969 "FStar.Tc.Tc.fst"
let _43_1806 = (tc_exp env e)
in (match (_43_1806) with
| (e, c, g_e) -> begin
(
# 970 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g g_e)
in (
# 971 "FStar.Tc.Tc.fst"
let _43_1808 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_717 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _122_716 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _122_717 _122_716)))
end else begin
()
end
in (
# 972 "FStar.Tc.Tc.fst"
let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(
# 974 "FStar.Tc.Tc.fst"
let subst = (let _122_718 = (FStar_List.hd bs)
in (maybe_extend_subst subst _122_718 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(
# 977 "FStar.Tc.Tc.fst"
let subst = (let _122_723 = (FStar_List.hd bs)
in (maybe_extend_subst subst _122_723 arg))
in (
# 978 "FStar.Tc.Tc.fst"
let _43_1815 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_43_1815) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _122_728 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _122_728)) then begin
(
# 982 "FStar.Tc.Tc.fst"
let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (
# 983 "FStar.Tc.Tc.fst"
let arg' = (let _122_729 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _122_729))
in (
# 984 "FStar.Tc.Tc.fst"
let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _122_742 = (let _122_741 = (let _122_735 = (let _122_734 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _122_734))
in (_122_735)::arg_rets)
in (let _122_740 = (let _122_738 = (let _122_737 = (FStar_All.pipe_left (fun _122_736 -> Some (_122_736)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_122_737, c))
in (_122_738)::comps)
in (let _122_739 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _122_741, _122_740, g, _122_739))))
in (tc_args _122_742 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_43_1822), _43_1825)::_43_1820, (FStar_Util.Inl (_43_1831), _43_1834)::_43_1829) -> begin
(let _122_746 = (let _122_745 = (let _122_744 = (let _122_743 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _122_743))
in ("Expected an expression; got a type", _122_744))
in FStar_Absyn_Syntax.Error (_122_745))
in (Prims.raise _122_746))
end
| ((FStar_Util.Inl (_43_1841), _43_1844)::_43_1839, (FStar_Util.Inr (_43_1850), _43_1853)::_43_1848) -> begin
(let _122_750 = (let _122_749 = (let _122_748 = (let _122_747 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _122_747))
in ("Expected a type; got an expression", _122_748))
in FStar_Absyn_Syntax.Error (_122_749))
in (Prims.raise _122_750))
end
| (_43_1858, []) -> begin
(
# 995 "FStar.Tc.Tc.fst"
let _43_1861 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (
# 996 "FStar.Tc.Tc.fst"
let _43_1879 = (match (bs) with
| [] -> begin
(
# 998 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (
# 1004 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g_head g)
in (
# 1006 "FStar.Tc.Tc.fst"
let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _43_1869 -> (match (_43_1869) with
| (_43_1867, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 1012 "FStar.Tc.Tc.fst"
let cres = if refine_with_equality then begin
(let _122_752 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _122_752 cres))
end else begin
(
# 1015 "FStar.Tc.Tc.fst"
let _43_1871 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_755 = (FStar_Absyn_Print.exp_to_string head)
in (let _122_754 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _122_753 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _122_755 _122_754 _122_753))))
end else begin
()
end
in cres)
end
in (let _122_756 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_122_756, g))))))
end
| _43_1875 -> begin
(
# 1023 "FStar.Tc.Tc.fst"
let g = (let _122_757 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _122_757 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _122_763 = (let _122_762 = (let _122_761 = (let _122_760 = (let _122_759 = (let _122_758 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _122_758))
in (FStar_Absyn_Syntax.mk_Typ_fun _122_759 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _122_760))
in (FStar_Absyn_Syntax.mk_Total _122_761))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _122_762))
in (_122_763, g)))
end)
in (match (_43_1879) with
| (cres, g) -> begin
(
# 1026 "FStar.Tc.Tc.fst"
let _43_1880 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_764 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _122_764))
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
let _43_1889 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_43_1889) with
| (comp, g) -> begin
(
# 1031 "FStar.Tc.Tc.fst"
let _43_1890 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_770 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _122_769 = (let _122_768 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _122_768))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _122_770 _122_769)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_43_1894) -> begin
(
# 1036 "FStar.Tc.Tc.fst"
let rec aux = (fun norm tres -> (
# 1037 "FStar.Tc.Tc.fst"
let tres = (let _122_775 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _122_775 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(
# 1040 "FStar.Tc.Tc.fst"
let _43_1906 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_776 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _122_776))
end else begin
()
end
in (let _122_781 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _122_781 args)))
end
| _43_1909 when (not (norm)) -> begin
(let _122_782 = (whnf env tres)
in (aux true _122_782))
end
| _43_1911 -> begin
(let _122_788 = (let _122_787 = (let _122_786 = (let _122_784 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _122_783 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _122_784 _122_783)))
in (let _122_785 = (FStar_Absyn_Syntax.argpos arg)
in (_122_786, _122_785)))
in FStar_Absyn_Syntax.Error (_122_787))
in (Prims.raise _122_788))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _122_789 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _122_789 args))))
end
| _43_1913 -> begin
if (not (norm)) then begin
(let _122_790 = (whnf env tf)
in (check_function_app true _122_790))
end else begin
(let _122_793 = (let _122_792 = (let _122_791 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_122_791, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_792))
in (Prims.raise _122_793))
end
end))
in (let _122_794 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _122_794)))))
end))
end))
in (
# 1055 "FStar.Tc.Tc.fst"
let _43_1917 = (aux ())
in (match (_43_1917) with
| (e, c, g) -> begin
(
# 1056 "FStar.Tc.Tc.fst"
let _43_1918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _122_795 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _122_795))
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
let _43_1925 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_800 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _122_799 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _122_798 = (let _122_797 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _122_797 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _122_800 _122_799 _122_798))))
end else begin
()
end
in (
# 1067 "FStar.Tc.Tc.fst"
let _43_1930 = (comp_check_expected_typ env0 e c)
in (match (_43_1930) with
| (e, c, g') -> begin
(let _122_801 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _122_801))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(
# 1071 "FStar.Tc.Tc.fst"
let _43_1937 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_43_1937) with
| (env1, topt) -> begin
(
# 1072 "FStar.Tc.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 1073 "FStar.Tc.Tc.fst"
let _43_1942 = (tc_exp env1 e1)
in (match (_43_1942) with
| (e1, c1, g1) -> begin
(
# 1074 "FStar.Tc.Tc.fst"
let _43_1949 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 1077 "FStar.Tc.Tc.fst"
let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _122_802 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_122_802, res_t)))
end)
in (match (_43_1949) with
| (env_branches, res_t) -> begin
(
# 1079 "FStar.Tc.Tc.fst"
let guard_x = (let _122_804 = (FStar_All.pipe_left (fun _122_803 -> Some (_122_803)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _122_804))
in (
# 1080 "FStar.Tc.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (
# 1081 "FStar.Tc.Tc.fst"
let _43_1966 = (
# 1082 "FStar.Tc.Tc.fst"
let _43_1963 = (FStar_List.fold_right (fun _43_1957 _43_1960 -> (match ((_43_1957, _43_1960)) with
| ((_43_1953, f, c, g), (caccum, gaccum)) -> begin
(let _122_807 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _122_807))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_43_1963) with
| (cases, g) -> begin
(let _122_808 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_122_808, g))
end))
in (match (_43_1966) with
| (c_branches, g_branches) -> begin
(
# 1085 "FStar.Tc.Tc.fst"
let _43_1967 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_812 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _122_811 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _122_810 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _122_809 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _122_812 _122_811 _122_810 _122_809)))))
end else begin
()
end
in (
# 1088 "FStar.Tc.Tc.fst"
let cres = (let _122_815 = (let _122_814 = (FStar_All.pipe_left (fun _122_813 -> Some (_122_813)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_122_814, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _122_815))
in (
# 1090 "FStar.Tc.Tc.fst"
let e = (let _122_822 = (w cres)
in (let _122_821 = (let _122_820 = (let _122_819 = (FStar_List.map (fun _43_1977 -> (match (_43_1977) with
| (f, _43_1972, _43_1974, _43_1976) -> begin
f
end)) t_eqns)
in (e1, _122_819))
in (FStar_Absyn_Syntax.mk_Exp_match _122_820))
in (FStar_All.pipe_left _122_822 _122_821)))
in (let _122_824 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _122_823 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_122_824, cres, _122_823))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _43_1982; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
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
| FStar_Util.Inr (_43_1995) -> begin
true
end
| _43_1998 -> begin
false
end)
in (
# 1099 "FStar.Tc.Tc.fst"
let _43_2003 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_43_2003) with
| (env1, _43_2002) -> begin
(
# 1100 "FStar.Tc.Tc.fst"
let _43_2016 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _43_2006 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _122_825 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _122_825))
end else begin
(
# 1106 "FStar.Tc.Tc.fst"
let _43_2009 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_43_2009) with
| (t, f) -> begin
(
# 1107 "FStar.Tc.Tc.fst"
let _43_2010 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _122_827 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _122_826 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _122_827 _122_826)))
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
in (match (_43_2016) with
| (f, env1) -> begin
(
# 1112 "FStar.Tc.Tc.fst"
let _43_2022 = (tc_exp (
# 1112 "FStar.Tc.Tc.fst"
let _43_2017 = env1
in {FStar_Tc_Env.solver = _43_2017.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_2017.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_2017.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_2017.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_2017.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_2017.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_2017.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_2017.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_2017.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_2017.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_2017.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_2017.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_2017.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_2017.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _43_2017.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_2017.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_2017.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_2017.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_2017.FStar_Tc_Env.default_effects}) e1)
in (match (_43_2022) with
| (e1, c1, g1) -> begin
(
# 1113 "FStar.Tc.Tc.fst"
let _43_2026 = (let _122_831 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _43_2023 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _122_831 e1 c1 f))
in (match (_43_2026) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_43_2028) -> begin
(
# 1116 "FStar.Tc.Tc.fst"
let _43_2042 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(
# 1118 "FStar.Tc.Tc.fst"
let _43_2032 = (let _122_832 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _122_832 c1))
in (match (_43_2032) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1121 "FStar.Tc.Tc.fst"
let _43_2033 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _122_833 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _122_833 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _122_834 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_122_834, c1)))
end
end))
end else begin
(
# 1124 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (
# 1125 "FStar.Tc.Tc.fst"
let _43_2036 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1126 "FStar.Tc.Tc.fst"
let _43_2038 = (FStar_Tc_Util.check_unresolved_implicits g)
in (let _122_835 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _122_835)))))
end
in (match (_43_2042) with
| (e2, c1) -> begin
(
# 1128 "FStar.Tc.Tc.fst"
let _43_2047 = if env.FStar_Tc_Env.generalize then begin
(let _122_836 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _122_836))
end else begin
(x, e1, c1)
end
in (match (_43_2047) with
| (_43_2044, e1, c1) -> begin
(
# 1131 "FStar.Tc.Tc.fst"
let cres = (let _122_837 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _122_837))
in (
# 1132 "FStar.Tc.Tc.fst"
let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _122_838 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _122_838 (None, cres)))
end
in (
# 1135 "FStar.Tc.Tc.fst"
let _43_2050 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _122_847 = (let _122_846 = (w cres)
in (let _122_845 = (let _122_844 = (let _122_843 = (let _122_842 = (let _122_841 = (FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1))
in (_122_841)::[])
in (false, _122_842))
in (_122_843, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _122_844))
in (FStar_All.pipe_left _122_846 _122_845)))
in (_122_847, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(
# 1139 "FStar.Tc.Tc.fst"
let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (
# 1140 "FStar.Tc.Tc.fst"
let _43_2058 = (let _122_848 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _122_848 e2))
in (match (_43_2058) with
| (e2, c2, g2) -> begin
(
# 1141 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (
# 1142 "FStar.Tc.Tc.fst"
let e = (let _122_856 = (w cres)
in (let _122_855 = (let _122_854 = (let _122_853 = (let _122_852 = (let _122_851 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1))
in (_122_851)::[])
in (false, _122_852))
in (_122_853, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _122_854))
in (FStar_All.pipe_left _122_856 _122_855)))
in (
# 1143 "FStar.Tc.Tc.fst"
let g2 = (let _122_865 = (let _122_858 = (let _122_857 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_122_857)::[])
in (FStar_Tc_Rel.close_guard _122_858))
in (let _122_864 = (let _122_863 = (let _122_862 = (let _122_861 = (let _122_860 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _122_860 e1))
in (FStar_All.pipe_left (fun _122_859 -> FStar_Tc_Rel.NonTrivial (_122_859)) _122_861))
in (FStar_Tc_Rel.guard_of_guard_formula _122_862))
in (FStar_Tc_Rel.imp_guard _122_863 g2))
in (FStar_All.pipe_left _122_865 _122_864)))
in (
# 1145 "FStar.Tc.Tc.fst"
let guard = (let _122_866 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _122_866))
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
let _43_2067 = (let _122_867 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _122_867))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _43_2070 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _43_2073), _43_2076) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(
# 1162 "FStar.Tc.Tc.fst"
let env = (instantiate_both env)
in (
# 1163 "FStar.Tc.Tc.fst"
let _43_2088 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_43_2088) with
| (env0, topt) -> begin
(
# 1164 "FStar.Tc.Tc.fst"
let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _43_9 -> (match (_43_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_43_2097); FStar_Absyn_Syntax.lbtyp = _43_2095; FStar_Absyn_Syntax.lbeff = _43_2093; FStar_Absyn_Syntax.lbdef = _43_2091} -> begin
true
end
| _43_2101 -> begin
false
end))))
in (
# 1166 "FStar.Tc.Tc.fst"
let _43_2126 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _43_2105 _43_2111 -> (match ((_43_2105, _43_2111)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _43_2108; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 1167 "FStar.Tc.Tc.fst"
let _43_2116 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_43_2116) with
| (_43_2113, t, check_t) -> begin
(
# 1169 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Util.unascribe e)
in (
# 1170 "FStar.Tc.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
(let _122_871 = (tc_typ_check_trivial (
# 1183 "FStar.Tc.Tc.fst"
let _43_2118 = env0
in {FStar_Tc_Env.solver = _43_2118.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_2118.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_2118.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_2118.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_2118.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_2118.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_2118.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_2118.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_2118.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_2118.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_2118.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_2118.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_2118.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_2118.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_2118.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _43_2118.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_2118.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_2118.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_2118.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _122_871 (norm_t env)))
end
in (
# 1184 "FStar.Tc.Tc.fst"
let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(
# 1186 "FStar.Tc.Tc.fst"
let _43_2121 = env
in {FStar_Tc_Env.solver = _43_2121.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_2121.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_2121.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_2121.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_2121.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_2121.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_2121.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_2121.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_2121.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_2121.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_2121.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_2121.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_2121.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_2121.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_2121.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_2121.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_2121.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_2121.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_2121.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_43_2126) with
| (lbs, env') -> begin
(
# 1191 "FStar.Tc.Tc.fst"
let _43_2141 = (let _122_877 = (let _122_876 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _122_876 (FStar_List.map (fun _43_2130 -> (match (_43_2130) with
| (x, t, e) -> begin
(
# 1192 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (
# 1193 "FStar.Tc.Tc.fst"
let _43_2132 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_875 = (FStar_Absyn_Print.lbname_to_string x)
in (let _122_874 = (FStar_Absyn_Print.exp_to_string e)
in (let _122_873 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _122_875 _122_874 _122_873))))
end else begin
()
end
in (
# 1195 "FStar.Tc.Tc.fst"
let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (
# 1196 "FStar.Tc.Tc.fst"
let _43_2138 = (tc_total_exp env' e)
in (match (_43_2138) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _122_877 FStar_List.unzip))
in (match (_43_2141) with
| (lbs, gs) -> begin
(
# 1199 "FStar.Tc.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (
# 1201 "FStar.Tc.Tc.fst"
let _43_2160 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _122_879 = (FStar_List.map (fun _43_2146 -> (match (_43_2146) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_122_879, g_lbs))
end else begin
(
# 1205 "FStar.Tc.Tc.fst"
let _43_2147 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (
# 1206 "FStar.Tc.Tc.fst"
let ecs = (let _122_882 = (FStar_All.pipe_right lbs (FStar_List.map (fun _43_2152 -> (match (_43_2152) with
| (x, t, e) -> begin
(let _122_881 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb (x, t, e)))
in (x, e, _122_881))
end))))
in (FStar_Tc_Util.generalize true env _122_882))
in (let _122_884 = (FStar_List.map (fun _43_2157 -> (match (_43_2157) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_122_884, FStar_Tc_Rel.trivial_guard))))
end
in (match (_43_2160) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(
# 1211 "FStar.Tc.Tc.fst"
let cres = (let _122_885 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _122_885))
in (
# 1212 "FStar.Tc.Tc.fst"
let _43_2162 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (
# 1213 "FStar.Tc.Tc.fst"
let _43_2164 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _122_889 = (let _122_888 = (w cres)
in (FStar_All.pipe_left _122_888 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_122_889, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(
# 1215 "FStar.Tc.Tc.fst"
let _43_2180 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _43_2168 _43_2175 -> (match ((_43_2168, _43_2175)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _43_2172; FStar_Absyn_Syntax.lbdef = _43_2170}) -> begin
(
# 1216 "FStar.Tc.Tc.fst"
let b = (binding_of_lb x t)
in (
# 1217 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_43_2180) with
| (bindings, env) -> begin
(
# 1219 "FStar.Tc.Tc.fst"
let _43_2184 = (tc_exp env e1)
in (match (_43_2184) with
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
let _43_2188 = cres
in {FStar_Absyn_Syntax.eff_name = _43_2188.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _43_2188.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _43_2188.FStar_Absyn_Syntax.comp})
in (
# 1225 "FStar.Tc.Tc.fst"
let e = (let _122_894 = (w cres)
in (FStar_All.pipe_left _122_894 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_43_2193) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1229 "FStar.Tc.Tc.fst"
let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _43_10 -> (match (_43_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_43_2205); FStar_Absyn_Syntax.lbtyp = _43_2203; FStar_Absyn_Syntax.lbeff = _43_2201; FStar_Absyn_Syntax.lbdef = _43_2199} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _43_2213; FStar_Absyn_Syntax.lbeff = _43_2211; FStar_Absyn_Syntax.lbdef = _43_2209} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _43_2222; FStar_Absyn_Syntax.lbeff = _43_2220; FStar_Absyn_Syntax.lbdef = _43_2218}) -> begin
(
# 1234 "FStar.Tc.Tc.fst"
let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (
# 1235 "FStar.Tc.Tc.fst"
let _43_2228 = (let _122_896 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _122_896))
in (e, cres, guard)))
end
| _43_2231 -> begin
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
and tc_eqn : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp)  ->  ((FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun scrutinee_x pat_t env _43_2238 -> (match (_43_2238) with
| (pattern, when_clause, branch) -> begin
(
# 1249 "FStar.Tc.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1250 "FStar.Tc.Tc.fst"
let _43_2246 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_43_2246) with
| (bindings, exps, p) -> begin
(
# 1251 "FStar.Tc.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (
# 1252 "FStar.Tc.Tc.fst"
let _43_2255 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _43_11 -> (match (_43_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _122_909 = (FStar_Absyn_Print.strBvd x)
in (let _122_908 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _122_909 _122_908)))
end
| _43_2254 -> begin
()
end))))
end else begin
()
end
in (
# 1256 "FStar.Tc.Tc.fst"
let _43_2260 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_43_2260) with
| (env1, _43_2259) -> begin
(
# 1257 "FStar.Tc.Tc.fst"
let env1 = (
# 1257 "FStar.Tc.Tc.fst"
let _43_2261 = env1
in {FStar_Tc_Env.solver = _43_2261.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_2261.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_2261.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_2261.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_2261.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_2261.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_2261.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_2261.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _43_2261.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_2261.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_2261.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_2261.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_2261.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_2261.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_2261.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_2261.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_2261.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_2261.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_2261.FStar_Tc_Env.default_effects})
in (
# 1258 "FStar.Tc.Tc.fst"
let expected_pat_t = (FStar_Tc_Rel.unrefine env pat_t)
in (
# 1259 "FStar.Tc.Tc.fst"
let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1260 "FStar.Tc.Tc.fst"
let _43_2266 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_912 = (FStar_Absyn_Print.exp_to_string e)
in (let _122_911 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _122_912 _122_911)))
end else begin
()
end
in (
# 1263 "FStar.Tc.Tc.fst"
let _43_2271 = (tc_exp env1 e)
in (match (_43_2271) with
| (e, lc, g) -> begin
(
# 1265 "FStar.Tc.Tc.fst"
let _43_2272 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_914 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _122_913 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _122_914 _122_913)))
end else begin
()
end
in (
# 1268 "FStar.Tc.Tc.fst"
let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (
# 1269 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g g')
in (
# 1270 "FStar.Tc.Tc.fst"
let _43_2276 = (let _122_915 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _122_915))
in (
# 1271 "FStar.Tc.Tc.fst"
let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (
# 1272 "FStar.Tc.Tc.fst"
let _43_2279 = if (let _122_918 = (let _122_917 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _122_916 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _122_917 _122_916)))
in (FStar_All.pipe_left Prims.op_Negation _122_918)) then begin
(let _122_923 = (let _122_922 = (let _122_921 = (let _122_920 = (FStar_Absyn_Print.exp_to_string e')
in (let _122_919 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _122_920 _122_919)))
in (_122_921, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_122_922))
in (Prims.raise _122_923))
end else begin
()
end
in (
# 1274 "FStar.Tc.Tc.fst"
let _43_2281 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_924 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _122_924))
end else begin
()
end
in e)))))))
end))))))
in (
# 1279 "FStar.Tc.Tc.fst"
let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (
# 1280 "FStar.Tc.Tc.fst"
let _43_2292 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _43_12 -> (match (_43_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _122_927 = (FStar_Absyn_Print.strBvd x)
in (let _122_926 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _122_927 _122_926)))
end
| _43_2291 -> begin
()
end))))
end else begin
()
end
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (
# 1287 "FStar.Tc.Tc.fst"
let _43_2299 = (tc_pat true pat_t pattern)
in (match (_43_2299) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(
# 1288 "FStar.Tc.Tc.fst"
let _43_2309 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(
# 1295 "FStar.Tc.Tc.fst"
let _43_2306 = (let _122_928 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _122_928 e))
in (match (_43_2306) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_43_2309) with
| (when_clause, g_when) -> begin
(
# 1297 "FStar.Tc.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _122_930 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _122_929 -> Some (_122_929)) _122_930))
end)
in (
# 1300 "FStar.Tc.Tc.fst"
let _43_2317 = (tc_exp pat_env branch)
in (match (_43_2317) with
| (branch, c, g_branch) -> begin
(
# 1301 "FStar.Tc.Tc.fst"
let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (
# 1302 "FStar.Tc.Tc.fst"
let _43_2322 = (let _122_931 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _122_931 FStar_Tc_Env.clear_expected_typ))
in (match (_43_2322) with
| (scrutinee_env, _43_2321) -> begin
(
# 1303 "FStar.Tc.Tc.fst"
let c = (
# 1304 "FStar.Tc.Tc.fst"
let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (
# 1305 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _43_2336 -> begin
(
# 1311 "FStar.Tc.Tc.fst"
let clause = (let _122_935 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _122_934 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _122_935 _122_934 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _122_937 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _122_936 -> Some (_122_936)) _122_937))
end))
end))) None))
in (
# 1315 "FStar.Tc.Tc.fst"
let c = (match ((eqs, when_condition)) with
| (None, None) -> begin
c
end
| (Some (f), None) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (f)))
end
| (Some (f), Some (w)) -> begin
(let _122_940 = (let _122_939 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _122_938 -> FStar_Tc_Rel.NonTrivial (_122_938)) _122_939))
in (FStar_Tc_Util.weaken_precondition env c _122_940))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (
# 1322 "FStar.Tc.Tc.fst"
let discriminate = (fun scrutinee f -> (
# 1323 "FStar.Tc.Tc.fst"
let disc = (let _122_946 = (let _122_945 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _122_945))
in (FStar_All.pipe_left _122_946 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (
# 1324 "FStar.Tc.Tc.fst"
let disc = (let _122_949 = (let _122_948 = (let _122_947 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_122_947)::[])
in (disc, _122_948))
in (FStar_Absyn_Syntax.mk_Exp_app _122_949 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (
# 1327 "FStar.Tc.Tc.fst"
let rec mk_guard = (fun scrutinee pat_exp -> (
# 1328 "FStar.Tc.Tc.fst"
let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_43_2394) -> begin
(let _122_958 = (let _122_957 = (let _122_956 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _122_955 = (let _122_954 = (FStar_Absyn_Syntax.varg pat_exp)
in (_122_954)::[])
in (_122_956)::_122_955))
in (FStar_Absyn_Util.teq, _122_957))
in (FStar_Absyn_Syntax.mk_Typ_app _122_958 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _43_2398) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _43_2411); FStar_Absyn_Syntax.tk = _43_2408; FStar_Absyn_Syntax.pos = _43_2406; FStar_Absyn_Syntax.fvs = _43_2404; FStar_Absyn_Syntax.uvs = _43_2402}, args) -> begin
(
# 1337 "FStar.Tc.Tc.fst"
let head = (discriminate scrutinee f)
in (
# 1338 "FStar.Tc.Tc.fst"
let sub_term_guards = (let _122_967 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_43_2422) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(
# 1341 "FStar.Tc.Tc.fst"
let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in if (let _122_961 = (FStar_Tc_Env.is_projector env projector)
in (FStar_All.pipe_left Prims.op_Negation _122_961)) then begin
[]
end else begin
(
# 1344 "FStar.Tc.Tc.fst"
let sub_term = (let _122_965 = (let _122_964 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _122_963 = (let _122_962 = (FStar_Absyn_Syntax.varg scrutinee)
in (_122_962)::[])
in (_122_964, _122_963)))
in (FStar_Absyn_Syntax.mk_Exp_app _122_965 None f.FStar_Absyn_Syntax.p))
in (let _122_966 = (mk_guard sub_term ei)
in (_122_966)::[]))
end)
end))))
in (FStar_All.pipe_right _122_967 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _43_2430 -> begin
(let _122_970 = (let _122_969 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _122_968 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _122_969 _122_968)))
in (FStar_All.failwith _122_970))
end)))
in (
# 1348 "FStar.Tc.Tc.fst"
let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(
# 1351 "FStar.Tc.Tc.fst"
let t = (mk_guard s pat)
in (
# 1352 "FStar.Tc.Tc.fst"
let _43_2439 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_43_2439) with
| (t, _43_2438) -> begin
t
end)))
end)
in (
# 1354 "FStar.Tc.Tc.fst"
let path_guard = (let _122_979 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _122_978 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _122_978)))))
in (FStar_All.pipe_right _122_979 FStar_Absyn_Util.mk_disj_l))
in (
# 1355 "FStar.Tc.Tc.fst"
let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (
# 1358 "FStar.Tc.Tc.fst"
let guard = (let _122_980 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _122_980))
in (
# 1359 "FStar.Tc.Tc.fst"
let _43_2447 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _122_981 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _122_981))
end else begin
()
end
in (let _122_983 = (let _122_982 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _122_982))
in ((pattern, when_clause, branch), path_guard, c, _122_983))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1364 "FStar.Tc.Tc.fst"
let _43_2453 = (tc_kind env k)
in (match (_43_2453) with
| (k, g) -> begin
(
# 1365 "FStar.Tc.Tc.fst"
let _43_2454 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd) = (fun env t -> (
# 1369 "FStar.Tc.Tc.fst"
let _43_2461 = (tc_typ env t)
in (match (_43_2461) with
| (t, k, g) -> begin
(
# 1370 "FStar.Tc.Tc.fst"
let _43_2462 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env t k -> (
# 1374 "FStar.Tc.Tc.fst"
let _43_2469 = (tc_typ_check env t k)
in (match (_43_2469) with
| (t, f) -> begin
(
# 1375 "FStar.Tc.Tc.fst"
let _43_2470 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 1379 "FStar.Tc.Tc.fst"
let _43_2477 = (tc_exp env e)
in (match (_43_2477) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(
# 1382 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (
# 1383 "FStar.Tc.Tc.fst"
let c = (let _122_993 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _122_993 (norm_c env)))
in (match ((let _122_995 = (let _122_994 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _122_994))
in (FStar_Tc_Rel.sub_comp env c _122_995))) with
| Some (g') -> begin
(let _122_996 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _122_996))
end
| _43_2483 -> begin
(let _122_999 = (let _122_998 = (let _122_997 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_122_997, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_998))
in (Prims.raise _122_999))
end)))
end
end)))
and tc_ghost_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 1389 "FStar.Tc.Tc.fst"
let _43_2489 = (tc_exp env e)
in (match (_43_2489) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(
# 1392 "FStar.Tc.Tc.fst"
let c = (let _122_1002 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _122_1002 (norm_c env)))
in (
# 1393 "FStar.Tc.Tc.fst"
let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (
# 1394 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (
# 1395 "FStar.Tc.Tc.fst"
let _43_2493 = env
in {FStar_Tc_Env.solver = _43_2493.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_2493.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_2493.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_2493.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_2493.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_2493.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_2493.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_2493.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_2493.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_2493.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_2493.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_2493.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_2493.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_2493.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_2493.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_2493.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _43_2493.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_2493.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_2493.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _122_1003 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _122_1003))
end
| _43_2498 -> begin
(let _122_1006 = (let _122_1005 = (let _122_1004 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_122_1004, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_122_1005))
in (Prims.raise _122_1006))
end))))
end
end)))

# 1401 "FStar.Tc.Tc.fst"
let tc_tparams : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env) = (fun env tps -> (
# 1402 "FStar.Tc.Tc.fst"
let _43_2504 = (tc_binders env tps)
in (match (_43_2504) with
| (tps, env, g) -> begin
(
# 1403 "FStar.Tc.Tc.fst"
let _43_2505 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

# 1406 "FStar.Tc.Tc.fst"
let a_kwp_a : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _43_2524)::(FStar_Util.Inl (wp), _43_2519)::(FStar_Util.Inl (_43_2511), _43_2514)::[], _43_2528) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _43_2532 -> begin
(let _122_1019 = (let _122_1018 = (let _122_1017 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (_122_1017, (FStar_Ident.range_of_lid m)))
in FStar_Absyn_Syntax.Error (_122_1018))
in (Prims.raise _122_1019))
end))

# 1412 "FStar.Tc.Tc.fst"
let rec tc_eff_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.eff_decl = (fun env m -> (
# 1413 "FStar.Tc.Tc.fst"
let _43_2538 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_43_2538) with
| (binders, env, g) -> begin
(
# 1414 "FStar.Tc.Tc.fst"
let _43_2539 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1415 "FStar.Tc.Tc.fst"
let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (
# 1416 "FStar.Tc.Tc.fst"
let _43_2544 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_43_2544) with
| (a, kwp_a) -> begin
(
# 1417 "FStar.Tc.Tc.fst"
let a_typ = (FStar_Absyn_Util.btvar_to_typ a)
in (
# 1418 "FStar.Tc.Tc.fst"
let b = (FStar_Absyn_Util.gen_bvar_p (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname) FStar_Absyn_Syntax.ktype)
in (
# 1419 "FStar.Tc.Tc.fst"
let b_typ = (FStar_Absyn_Util.btvar_to_typ b)
in (
# 1420 "FStar.Tc.Tc.fst"
let kwp_b = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (
# 1421 "FStar.Tc.Tc.fst"
let kwlp_a = kwp_a
in (
# 1422 "FStar.Tc.Tc.fst"
let kwlp_b = kwp_b
in (
# 1423 "FStar.Tc.Tc.fst"
let a_kwp_b = (let _122_1032 = (let _122_1031 = (let _122_1030 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_122_1030)::[])
in (_122_1031, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1032 a_typ.FStar_Absyn_Syntax.pos))
in (
# 1424 "FStar.Tc.Tc.fst"
let a_kwlp_b = a_kwp_b
in (
# 1425 "FStar.Tc.Tc.fst"
let w = (fun k -> (k (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname)))
in (
# 1426 "FStar.Tc.Tc.fst"
let ret = (
# 1427 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1046 = (let _122_1045 = (let _122_1044 = (let _122_1043 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1042 = (let _122_1041 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_122_1041)::[])
in (_122_1043)::_122_1042))
in (_122_1044, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1045))
in (FStar_All.pipe_left w _122_1046))
in (let _122_1047 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _122_1047 (norm_t env))))
in (
# 1429 "FStar.Tc.Tc.fst"
let bind_wp = (
# 1430 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1062 = (let _122_1061 = (let _122_1060 = (let _122_1059 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1058 = (let _122_1057 = (FStar_Absyn_Syntax.t_binder b)
in (let _122_1056 = (let _122_1055 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _122_1054 = (let _122_1053 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _122_1052 = (let _122_1051 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _122_1050 = (let _122_1049 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_122_1049)::[])
in (_122_1051)::_122_1050))
in (_122_1053)::_122_1052))
in (_122_1055)::_122_1054))
in (_122_1057)::_122_1056))
in (_122_1059)::_122_1058))
in (_122_1060, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1061))
in (FStar_All.pipe_left w _122_1062))
in (let _122_1063 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _122_1063 (norm_t env))))
in (
# 1435 "FStar.Tc.Tc.fst"
let bind_wlp = (
# 1436 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1074 = (let _122_1073 = (let _122_1072 = (let _122_1071 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1070 = (let _122_1069 = (FStar_Absyn_Syntax.t_binder b)
in (let _122_1068 = (let _122_1067 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _122_1066 = (let _122_1065 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_122_1065)::[])
in (_122_1067)::_122_1066))
in (_122_1069)::_122_1068))
in (_122_1071)::_122_1070))
in (_122_1072, kwlp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1073))
in (FStar_All.pipe_left w _122_1074))
in (let _122_1075 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _122_1075 (norm_t env))))
in (
# 1441 "FStar.Tc.Tc.fst"
let if_then_else = (
# 1442 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1086 = (let _122_1085 = (let _122_1084 = (let _122_1083 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1082 = (let _122_1081 = (FStar_Absyn_Syntax.t_binder b)
in (let _122_1080 = (let _122_1079 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _122_1078 = (let _122_1077 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_122_1077)::[])
in (_122_1079)::_122_1078))
in (_122_1081)::_122_1080))
in (_122_1083)::_122_1082))
in (_122_1084, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1085))
in (FStar_All.pipe_left w _122_1086))
in (let _122_1087 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _122_1087 (norm_t env))))
in (
# 1447 "FStar.Tc.Tc.fst"
let ite_wp = (
# 1448 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1096 = (let _122_1095 = (let _122_1094 = (let _122_1093 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1092 = (let _122_1091 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _122_1090 = (let _122_1089 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_122_1089)::[])
in (_122_1091)::_122_1090))
in (_122_1093)::_122_1092))
in (_122_1094, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1095))
in (FStar_All.pipe_left w _122_1096))
in (let _122_1097 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _122_1097 (norm_t env))))
in (
# 1453 "FStar.Tc.Tc.fst"
let ite_wlp = (
# 1454 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1104 = (let _122_1103 = (let _122_1102 = (let _122_1101 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1100 = (let _122_1099 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_122_1099)::[])
in (_122_1101)::_122_1100))
in (_122_1102, kwlp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1103))
in (FStar_All.pipe_left w _122_1104))
in (let _122_1105 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _122_1105 (norm_t env))))
in (
# 1458 "FStar.Tc.Tc.fst"
let wp_binop = (
# 1459 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1117 = (let _122_1116 = (let _122_1115 = (let _122_1114 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1113 = (let _122_1112 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _122_1111 = (let _122_1110 = (let _122_1107 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _122_1107))
in (let _122_1109 = (let _122_1108 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_122_1108)::[])
in (_122_1110)::_122_1109))
in (_122_1112)::_122_1111))
in (_122_1114)::_122_1113))
in (_122_1115, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1116))
in (FStar_All.pipe_left w _122_1117))
in (let _122_1118 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _122_1118 (norm_t env))))
in (
# 1465 "FStar.Tc.Tc.fst"
let wp_as_type = (
# 1466 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1125 = (let _122_1124 = (let _122_1123 = (let _122_1122 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1121 = (let _122_1120 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_122_1120)::[])
in (_122_1122)::_122_1121))
in (_122_1123, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1124))
in (FStar_All.pipe_left w _122_1125))
in (let _122_1126 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _122_1126 (norm_t env))))
in (
# 1470 "FStar.Tc.Tc.fst"
let close_wp = (
# 1471 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1135 = (let _122_1134 = (let _122_1133 = (let _122_1132 = (FStar_Absyn_Syntax.t_binder b)
in (let _122_1131 = (let _122_1130 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1129 = (let _122_1128 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_122_1128)::[])
in (_122_1130)::_122_1129))
in (_122_1132)::_122_1131))
in (_122_1133, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1134))
in (FStar_All.pipe_left w _122_1135))
in (let _122_1136 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _122_1136 (norm_t env))))
in (
# 1475 "FStar.Tc.Tc.fst"
let close_wp_t = (
# 1476 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1149 = (let _122_1148 = (let _122_1147 = (let _122_1146 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1145 = (let _122_1144 = (let _122_1143 = (let _122_1142 = (let _122_1141 = (let _122_1140 = (let _122_1139 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_122_1139)::[])
in (_122_1140, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1141))
in (FStar_All.pipe_left w _122_1142))
in (FStar_Absyn_Syntax.null_t_binder _122_1143))
in (_122_1144)::[])
in (_122_1146)::_122_1145))
in (_122_1147, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1148))
in (FStar_All.pipe_left w _122_1149))
in (let _122_1150 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _122_1150 (norm_t env))))
in (
# 1480 "FStar.Tc.Tc.fst"
let _43_2578 = (
# 1481 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1159 = (let _122_1158 = (let _122_1157 = (let _122_1156 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1155 = (let _122_1154 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _122_1153 = (let _122_1152 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_122_1152)::[])
in (_122_1154)::_122_1153))
in (_122_1156)::_122_1155))
in (_122_1157, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1158))
in (FStar_All.pipe_left w _122_1159))
in (let _122_1163 = (let _122_1160 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _122_1160 (norm_t env)))
in (let _122_1162 = (let _122_1161 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _122_1161 (norm_t env)))
in (_122_1163, _122_1162))))
in (match (_43_2578) with
| (assert_p, assume_p) -> begin
(
# 1485 "FStar.Tc.Tc.fst"
let null_wp = (
# 1486 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1168 = (let _122_1167 = (let _122_1166 = (let _122_1165 = (FStar_Absyn_Syntax.t_binder a)
in (_122_1165)::[])
in (_122_1166, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1167))
in (FStar_All.pipe_left w _122_1168))
in (let _122_1169 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _122_1169 (norm_t env))))
in (
# 1488 "FStar.Tc.Tc.fst"
let trivial_wp = (
# 1489 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1176 = (let _122_1175 = (let _122_1174 = (let _122_1173 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1172 = (let _122_1171 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_122_1171)::[])
in (_122_1173)::_122_1172))
in (_122_1174, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1175))
in (FStar_All.pipe_left w _122_1176))
in (let _122_1177 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _122_1177 (norm_t env))))
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
(
# 1522 "FStar.Tc.Tc.fst"
let _43_2597 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (
# 1523 "FStar.Tc.Tc.fst"
let _43_2599 = (let _122_1181 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _122_1181 Prims.ignore))
in (se, env)))
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, r) -> begin
(
# 1528 "FStar.Tc.Tc.fst"
let ne = (tc_eff_decl env ne)
in (
# 1529 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ne, r))
in (
# 1530 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, r) -> begin
(
# 1534 "FStar.Tc.Tc.fst"
let _43_2614 = (let _122_1182 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _122_1182))
in (match (_43_2614) with
| (a, kwp_a_src) -> begin
(
# 1535 "FStar.Tc.Tc.fst"
let _43_2617 = (let _122_1183 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _122_1183))
in (match (_43_2617) with
| (b, kwp_b_tgt) -> begin
(
# 1536 "FStar.Tc.Tc.fst"
let kwp_a_tgt = (let _122_1187 = (let _122_1186 = (let _122_1185 = (let _122_1184 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _122_1184))
in FStar_Util.Inl (_122_1185))
in (_122_1186)::[])
in (FStar_Absyn_Util.subst_kind _122_1187 kwp_b_tgt))
in (
# 1537 "FStar.Tc.Tc.fst"
let expected_k = (let _122_1193 = (let _122_1192 = (let _122_1191 = (let _122_1190 = (FStar_Absyn_Syntax.t_binder a)
in (let _122_1189 = (let _122_1188 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_122_1188)::[])
in (_122_1190)::_122_1189))
in (_122_1191, kwp_a_tgt))
in (FStar_Absyn_Syntax.mk_Kind_arrow _122_1192))
in (FStar_All.pipe_right r _122_1193))
in (
# 1538 "FStar.Tc.Tc.fst"
let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (
# 1539 "FStar.Tc.Tc.fst"
let sub = (
# 1539 "FStar.Tc.Tc.fst"
let _43_2621 = sub
in {FStar_Absyn_Syntax.source = _43_2621.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _43_2621.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (
# 1540 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (
# 1541 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(
# 1545 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1546 "FStar.Tc.Tc.fst"
let _43_2638 = (tc_tparams env tps)
in (match (_43_2638) with
| (tps, env) -> begin
(
# 1547 "FStar.Tc.Tc.fst"
let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _43_2641 -> begin
(tc_kind_trivial env k)
end)
in (
# 1550 "FStar.Tc.Tc.fst"
let _43_2643 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _122_1196 = (FStar_Absyn_Print.sli lid)
in (let _122_1195 = (let _122_1194 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _122_1194))
in (FStar_Util.print2 "Checked %s at kind %s\n" _122_1196 _122_1195)))
end else begin
()
end
in (
# 1551 "FStar.Tc.Tc.fst"
let k = (norm_k env k)
in (
# 1552 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (
# 1553 "FStar.Tc.Tc.fst"
let _43_2661 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_43_2656); FStar_Absyn_Syntax.tk = _43_2654; FStar_Absyn_Syntax.pos = _43_2652; FStar_Absyn_Syntax.fvs = _43_2650; FStar_Absyn_Syntax.uvs = _43_2648} -> begin
(let _122_1197 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _122_1197))
end
| _43_2660 -> begin
()
end)
in (
# 1556 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(
# 1560 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 1561 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1562 "FStar.Tc.Tc.fst"
let _43_2674 = (tc_tparams env tps)
in (match (_43_2674) with
| (tps, env) -> begin
(
# 1563 "FStar.Tc.Tc.fst"
let k = (tc_kind_trivial env k)
in (
# 1564 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, tps, k, r))
in (
# 1565 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, tps, c, tags, r) -> begin
(
# 1569 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 1570 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1571 "FStar.Tc.Tc.fst"
let _43_2689 = (tc_tparams env tps)
in (match (_43_2689) with
| (tps, env) -> begin
(
# 1572 "FStar.Tc.Tc.fst"
let _43_2692 = (tc_comp env c)
in (match (_43_2692) with
| (c, g) -> begin
(
# 1573 "FStar.Tc.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _43_13 -> (match (_43_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(
# 1575 "FStar.Tc.Tc.fst"
let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _122_1200 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _122_1199 -> Some (_122_1199)))
in FStar_Absyn_Syntax.DefaultEffect (_122_1200)))
end
| t -> begin
t
end))))
in (
# 1578 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, tps, c, tags, r))
in (
# 1579 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env0 se)
in (se, env))))
end))
end))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, tags, r) -> begin
(
# 1583 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1584 "FStar.Tc.Tc.fst"
let _43_2712 = (tc_tparams env tps)
in (match (_43_2712) with
| (tps, env') -> begin
(
# 1585 "FStar.Tc.Tc.fst"
let _43_2718 = (let _122_1204 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _122_1204 (fun _43_2715 -> (match (_43_2715) with
| (t, k) -> begin
(let _122_1203 = (norm_t env' t)
in (let _122_1202 = (norm_k env' k)
in (_122_1203, _122_1202)))
end))))
in (match (_43_2718) with
| (t, k1) -> begin
(
# 1586 "FStar.Tc.Tc.fst"
let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _43_2721 -> begin
(
# 1588 "FStar.Tc.Tc.fst"
let k2 = (let _122_1205 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _122_1205 (norm_k env)))
in (
# 1589 "FStar.Tc.Tc.fst"
let _43_2723 = (let _122_1206 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _122_1206))
in k2))
end)
in (
# 1590 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k2, t, tags, r))
in (
# 1591 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end))
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, (tname, tps, k), quals, mutuals, r) -> begin
(
# 1595 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1596 "FStar.Tc.Tc.fst"
let _43_2743 = (tc_binders env tps)
in (match (_43_2743) with
| (tps, env, g) -> begin
(
# 1597 "FStar.Tc.Tc.fst"
let tycon = (tname, tps, k)
in (
# 1598 "FStar.Tc.Tc.fst"
let _43_2745 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1599 "FStar.Tc.Tc.fst"
let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (
# 1600 "FStar.Tc.Tc.fst"
let t = (norm_t env t)
in (
# 1602 "FStar.Tc.Tc.fst"
let _43_2757 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _43_2754 -> begin
([], t)
end)
in (match (_43_2757) with
| (formals, result_t) -> begin
(
# 1606 "FStar.Tc.Tc.fst"
let cardinality_and_positivity_check = (fun formal -> (
# 1607 "FStar.Tc.Tc.fst"
let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _43_2765 -> (match (_43_2765) with
| (a, _43_2764) -> begin
(match (a) with
| FStar_Util.Inl (_43_2767) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(
# 1611 "FStar.Tc.Tc.fst"
let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _122_1214 = (FStar_Absyn_Util.compress_typ t)
in _122_1214.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _122_1218 = (let _122_1217 = (let _122_1216 = (let _122_1215 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _122_1215 tname))
in (_122_1216, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_122_1217))
in (Prims.raise _122_1218))
end)
end
| _43_2780 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(
# 1623 "FStar.Tc.Tc.fst"
let _43_2783 = if (FStar_Options.warn_cardinality ()) then begin
(let _122_1219 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _122_1219))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _122_1222 = (let _122_1221 = (let _122_1220 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_122_1220, r))
in FStar_Absyn_Syntax.Error (_122_1221))
in (Prims.raise _122_1222))
end else begin
()
end
end
in (
# 1629 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_43_2787) -> begin
(
# 1632 "FStar.Tc.Tc.fst"
let _43_2792 = (FStar_Absyn_Util.kind_formals k)
in (match (_43_2792) with
| (formals, _43_2791) -> begin
(check_positivity formals)
end))
end
| _43_2794 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(
# 1638 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(
# 1640 "FStar.Tc.Tc.fst"
let _43_2801 = (let _122_1223 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _122_1223 FStar_Util.must))
in (match (_43_2801) with
| (formals, _43_2800) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (
# 1643 "FStar.Tc.Tc.fst"
let _43_2802 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (
# 1645 "FStar.Tc.Tc.fst"
let _43_2856 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _122_1227 = (let _122_1226 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _122_1226 Prims.fst))
in (FStar_List.forall2 (fun _43_2809 _43_2813 -> (match ((_43_2809, _43_2813)) with
| ((a, _43_2808), (b, _43_2812)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _43_2821; FStar_Absyn_Syntax.pos = _43_2819; FStar_Absyn_Syntax.fvs = _43_2817; FStar_Absyn_Syntax.uvs = _43_2815}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _43_2836; FStar_Absyn_Syntax.pos = _43_2834; FStar_Absyn_Syntax.fvs = _43_2832; FStar_Absyn_Syntax.uvs = _43_2830}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _43_2845 -> begin
false
end)
end)) _122_1227 tps))))) then begin
(
# 1652 "FStar.Tc.Tc.fst"
let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _43_2848 -> begin
(
# 1655 "FStar.Tc.Tc.fst"
let _43_2852 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_43_2852) with
| (_43_2850, expected_args) -> begin
(let _122_1228 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _122_1228 expected_args))
end))
end)
in (let _122_1232 = (let _122_1231 = (let _122_1230 = (let _122_1229 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _122_1229 result_t expected_t))
in (_122_1230, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_122_1231))
in (Prims.raise _122_1232)))
end else begin
()
end
end
| _43_2855 -> begin
(let _122_1237 = (let _122_1236 = (let _122_1235 = (let _122_1234 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _122_1233 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _122_1234 result_t _122_1233)))
in (_122_1235, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_122_1236))
in (Prims.raise _122_1237))
end)
in (
# 1659 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (
# 1660 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (
# 1661 "FStar.Tc.Tc.fst"
let _43_2860 = if (log env) then begin
(let _122_1239 = (let _122_1238 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _122_1238))
in (FStar_All.pipe_left FStar_Util.print_string _122_1239))
end else begin
()
end
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(
# 1665 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1666 "FStar.Tc.Tc.fst"
let t = (let _122_1240 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _122_1240 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (
# 1667 "FStar.Tc.Tc.fst"
let _43_2870 = (FStar_Tc_Util.check_uvars r t)
in (
# 1668 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (
# 1669 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (
# 1670 "FStar.Tc.Tc.fst"
let _43_2874 = if (log env) then begin
(let _122_1242 = (let _122_1241 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _122_1241))
in (FStar_All.pipe_left FStar_Util.print_string _122_1242))
end else begin
()
end
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(
# 1674 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1675 "FStar.Tc.Tc.fst"
let phi = (let _122_1243 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _122_1243 (norm_t env)))
in (
# 1676 "FStar.Tc.Tc.fst"
let _43_2884 = (FStar_Tc_Util.check_uvars r phi)
in (
# 1677 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (
# 1678 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(
# 1683 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1684 "FStar.Tc.Tc.fst"
let _43_2937 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _43_2897 lb -> (match (_43_2897) with
| (gen, lbs) -> begin
(
# 1685 "FStar.Tc.Tc.fst"
let _43_2934 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_43_2906); FStar_Absyn_Syntax.lbtyp = _43_2904; FStar_Absyn_Syntax.lbeff = _43_2902; FStar_Absyn_Syntax.lbdef = _43_2900} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _43_2911; FStar_Absyn_Syntax.lbdef = e} -> begin
(
# 1688 "FStar.Tc.Tc.fst"
let _43_2931 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _43_2919) -> begin
(
# 1691 "FStar.Tc.Tc.fst"
let _43_2922 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _122_1246 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _122_1246 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _122_1247 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _122_1247))
end
| _43_2926 -> begin
(
# 1697 "FStar.Tc.Tc.fst"
let _43_2927 = if (not (deserialized)) then begin
(let _122_1249 = (let _122_1248 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _122_1248))
in (FStar_All.pipe_left FStar_Util.print_string _122_1249))
end else begin
()
end
in (let _122_1250 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _122_1250)))
end))
end)
in (match (_43_2931) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_43_2934) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_43_2937) with
| (generalize, lbs') -> begin
(
# 1702 "FStar.Tc.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 1703 "FStar.Tc.Tc.fst"
let e = (let _122_1255 = (let _122_1254 = (let _122_1253 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _122_1253 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((Prims.fst lbs), lbs'), _122_1254))
in (FStar_Absyn_Syntax.mk_Exp_let _122_1255 None r))
in (
# 1704 "FStar.Tc.Tc.fst"
let _43_2972 = (match ((tc_exp (
# 1704 "FStar.Tc.Tc.fst"
let _43_2940 = env
in {FStar_Tc_Env.solver = _43_2940.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_2940.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_2940.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_2940.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_2940.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_2940.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_2940.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_2940.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_2940.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_2940.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_2940.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_2940.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _43_2940.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_2940.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_2940.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_2940.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _43_2940.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _43_2940.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _43_2940.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _43_2949; FStar_Absyn_Syntax.pos = _43_2947; FStar_Absyn_Syntax.fvs = _43_2945; FStar_Absyn_Syntax.uvs = _43_2943}, _43_2956, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(
# 1706 "FStar.Tc.Tc.fst"
let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_43_2960, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _43_2966 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _43_2969 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_43_2972) with
| (se, lbs) -> begin
(
# 1711 "FStar.Tc.Tc.fst"
let _43_2978 = if (log env) then begin
(let _122_1261 = (let _122_1260 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1713 "FStar.Tc.Tc.fst"
let should_log = (match ((let _122_1257 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _122_1257))) with
| None -> begin
true
end
| _43_2976 -> begin
false
end)
in if should_log then begin
(let _122_1259 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _122_1258 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _122_1259 _122_1258)))
end else begin
""
end))))
in (FStar_All.pipe_right _122_1260 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _122_1261))
end else begin
()
end
in (
# 1719 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))
end))))
end)))
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(
# 1723 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1724 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (
# 1725 "FStar.Tc.Tc.fst"
let _43_2990 = (tc_exp env e)
in (match (_43_2990) with
| (e, c, g1) -> begin
(
# 1726 "FStar.Tc.Tc.fst"
let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (
# 1727 "FStar.Tc.Tc.fst"
let _43_2996 = (let _122_1265 = (let _122_1262 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_122_1262))
in (let _122_1264 = (let _122_1263 = (c.FStar_Absyn_Syntax.comp ())
in (e, _122_1263))
in (check_expected_effect env _122_1265 _122_1264)))
in (match (_43_2996) with
| (e, _43_2994, g) -> begin
(
# 1728 "FStar.Tc.Tc.fst"
let _43_2997 = (let _122_1266 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _122_1266))
in (
# 1729 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (
# 1730 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(
# 1734 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_range env r)
in (
# 1735 "FStar.Tc.Tc.fst"
let _43_3016 = (FStar_All.pipe_right ses (FStar_List.partition (fun _43_14 -> (match (_43_14) with
| FStar_Absyn_Syntax.Sig_tycon (_43_3010) -> begin
true
end
| _43_3013 -> begin
false
end))))
in (match (_43_3016) with
| (tycons, rest) -> begin
(
# 1736 "FStar.Tc.Tc.fst"
let _43_3025 = (FStar_All.pipe_right rest (FStar_List.partition (fun _43_15 -> (match (_43_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_43_3019) -> begin
true
end
| _43_3022 -> begin
false
end))))
in (match (_43_3025) with
| (abbrevs, rest) -> begin
(
# 1737 "FStar.Tc.Tc.fst"
let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _43_16 -> (match (_43_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(
# 1739 "FStar.Tc.Tc.fst"
let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _122_1270 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _122_1270 Prims.fst))
end
| _43_3037 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _43_3040 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1744 "FStar.Tc.Tc.fst"
let _43_3044 = (FStar_List.split recs)
in (match (_43_3044) with
| (recs, abbrev_defs) -> begin
(
# 1745 "FStar.Tc.Tc.fst"
let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _122_1271 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _122_1271))
end else begin
""
end
in (
# 1748 "FStar.Tc.Tc.fst"
let _43_3046 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (
# 1749 "FStar.Tc.Tc.fst"
let _43_3051 = (tc_decls env tycons deserialized)
in (match (_43_3051) with
| (tycons, _43_3050) -> begin
(
# 1750 "FStar.Tc.Tc.fst"
let _43_3055 = (tc_decls env recs deserialized)
in (match (_43_3055) with
| (recs, _43_3054) -> begin
(
# 1751 "FStar.Tc.Tc.fst"
let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (
# 1752 "FStar.Tc.Tc.fst"
let _43_3060 = (tc_decls env1 rest deserialized)
in (match (_43_3060) with
| (rest, _43_3059) -> begin
(
# 1753 "FStar.Tc.Tc.fst"
let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(
# 1755 "FStar.Tc.Tc.fst"
let tt = (let _122_1274 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _122_1274))
in (
# 1756 "FStar.Tc.Tc.fst"
let _43_3076 = (tc_typ_trivial env1 tt)
in (match (_43_3076) with
| (tt, _43_3075) -> begin
(
# 1757 "FStar.Tc.Tc.fst"
let _43_3085 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _43_3082 -> begin
([], tt)
end)
in (match (_43_3085) with
| (tps, t) -> begin
(let _122_1276 = (let _122_1275 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _122_1275, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_122_1276))
end))
end)))
end
| _43_3087 -> begin
(let _122_1278 = (let _122_1277 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _122_1277))
in (FStar_All.failwith _122_1278))
end)) recs abbrev_defs)
in (
# 1763 "FStar.Tc.Tc.fst"
let _43_3089 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
in (
# 1764 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append (FStar_List.append tycons abbrevs) rest), quals, lids, r))
in (
# 1765 "FStar.Tc.Tc.fst"
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
# 1769 "FStar.Tc.Tc.fst"
let time_tc_decl = (fun env se ds -> (
# 1770 "FStar.Tc.Tc.fst"
let start = (FStar_Util.now ())
in (
# 1771 "FStar.Tc.Tc.fst"
let res = (tc_decl env se ds)
in (
# 1772 "FStar.Tc.Tc.fst"
let stop = (FStar_Util.now ())
in (
# 1773 "FStar.Tc.Tc.fst"
let diff = (FStar_Util.time_diff start stop)
in (
# 1774 "FStar.Tc.Tc.fst"
let _43_3104 = (let _122_1288 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _122_1288))
in res))))))
in (
# 1777 "FStar.Tc.Tc.fst"
let _43_3119 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _43_3108 se -> (match (_43_3108) with
| (ses, env) -> begin
(
# 1779 "FStar.Tc.Tc.fst"
let _43_3110 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _122_1292 = (let _122_1291 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _122_1291))
in (FStar_Util.print_string _122_1292))
end else begin
()
end
in (
# 1781 "FStar.Tc.Tc.fst"
let _43_3114 = if (FStar_ST.read FStar_Options.timing) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_43_3114) with
| (se, env) -> begin
(
# 1785 "FStar.Tc.Tc.fst"
let _43_3115 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in ((se)::ses, env))
end)))
end)) ([], env)))
in (match (_43_3119) with
| (ses, env) -> begin
((FStar_List.rev ses), env)
end))))

# 1791 "FStar.Tc.Tc.fst"
let rec for_export : FStar_Tc_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (
# 1813 "FStar.Tc.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _43_17 -> (match (_43_17) with
| FStar_Absyn_Syntax.Abstract -> begin
true
end
| _43_3128 -> begin
false
end)))))
in (
# 1814 "FStar.Tc.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Absyn_Syntax.Projector (l, _)) | (FStar_Absyn_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _43_3138 -> begin
false
end))
in (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (_43_3140) -> begin
([], hidden)
end
| FStar_Absyn_Syntax.Sig_datacon (_43_3143) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, binders, knd, def, quals, r) -> begin
if (is_abstract quals) then begin
(
# 1828 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((lid, binders, knd, [], [], (FStar_Absyn_Syntax.Assumption)::quals, r))
in ((se)::[], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _43_3163, _43_3165) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _43_3171 -> (match (_43_3171) with
| (out, hidden) -> begin
(match (se) with
| FStar_Absyn_Syntax.Sig_tycon (l, bs, t, _43_3176, _43_3178, quals, r) -> begin
(
# 1836 "FStar.Tc.Tc.fst"
let dec = FStar_Absyn_Syntax.Sig_tycon ((l, bs, t, [], [], quals, r))
in ((dec)::out, hidden))
end
| FStar_Absyn_Syntax.Sig_datacon (l, t, _tc, quals, _mutuals, r) -> begin
(
# 1839 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Env.lookup_datacon env l)
in (
# 1840 "FStar.Tc.Tc.fst"
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
| FStar_Absyn_Syntax.Sig_assume (_43_3196, _43_3198, quals, _43_3201) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _43_18 -> (match (_43_18) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _43_3219 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Absyn_Syntax.Sig_main (_43_3221) -> begin
([], hidden)
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_let ((false, lb::[]), _43_3237, _43_3239, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(
# 1870 "FStar.Tc.Tc.fst"
let lid = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
([], hidden)
end else begin
(
# 1873 "FStar.Tc.Tc.fst"
let dec = FStar_Absyn_Syntax.Sig_val_decl ((lid, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end)
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _122_1310 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _122_1309 = (let _122_1308 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_122_1308, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::quals, r))
in FStar_Absyn_Syntax.Sig_val_decl (_122_1309)))))
in (_122_1310, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 1882 "FStar.Tc.Tc.fst"
let get_exports : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env modul -> (
# 1883 "FStar.Tc.Tc.fst"
let _43_3264 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.fold_left (fun _43_3256 se -> (match (_43_3256) with
| (exports, hidden) -> begin
(
# 1884 "FStar.Tc.Tc.fst"
let _43_3260 = (for_export env hidden se)
in (match (_43_3260) with
| (exports', hidden) -> begin
((exports')::exports, hidden)
end))
end)) ([], [])))
in (match (_43_3264) with
| (exports, _43_3263) -> begin
(FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
end)))

# 1888 "FStar.Tc.Tc.fst"
let tc_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1889 "FStar.Tc.Tc.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (
# 1890 "FStar.Tc.Tc.fst"
let msg = (Prims.strcat "Internals for " name)
in (
# 1891 "FStar.Tc.Tc.fst"
let env = (
# 1891 "FStar.Tc.Tc.fst"
let _43_3269 = env
in (let _122_1321 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _43_3269.FStar_Tc_Env.solver; FStar_Tc_Env.range = _43_3269.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _43_3269.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _43_3269.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _43_3269.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _43_3269.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _43_3269.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _43_3269.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _43_3269.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _43_3269.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _43_3269.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _43_3269.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _43_3269.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _43_3269.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _43_3269.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _43_3269.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _43_3269.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _122_1321; FStar_Tc_Env.default_effects = _43_3269.FStar_Tc_Env.default_effects}))
in (
# 1892 "FStar.Tc.Tc.fst"
let _43_3272 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (
# 1893 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (
# 1894 "FStar.Tc.Tc.fst"
let _43_3277 = (tc_decls env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_43_3277) with
| (ses, env) -> begin
((
# 1895 "FStar.Tc.Tc.fst"
let _43_3278 = modul
in {FStar_Absyn_Syntax.name = _43_3278.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _43_3278.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _43_3278.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _43_3278.FStar_Absyn_Syntax.is_deserialized}), env)
end))))))))

# 1897 "FStar.Tc.Tc.fst"
let tc_more_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul decls -> (
# 1898 "FStar.Tc.Tc.fst"
let _43_3285 = (tc_decls env decls false)
in (match (_43_3285) with
| (ses, env) -> begin
(
# 1899 "FStar.Tc.Tc.fst"
let modul = (
# 1899 "FStar.Tc.Tc.fst"
let _43_3286 = modul
in {FStar_Absyn_Syntax.name = _43_3286.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _43_3286.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _43_3286.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _43_3286.FStar_Absyn_Syntax.is_deserialized})
in (modul, env))
end)))

# 1902 "FStar.Tc.Tc.fst"
let finish_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1903 "FStar.Tc.Tc.fst"
let exports = (get_exports env modul)
in (
# 1904 "FStar.Tc.Tc.fst"
let modul = (
# 1904 "FStar.Tc.Tc.fst"
let _43_3292 = modul
in {FStar_Absyn_Syntax.name = _43_3292.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _43_3292.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (
# 1905 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.finish_module env modul)
in (
# 1906 "FStar.Tc.Tc.fst"
let _43_3302 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(
# 1908 "FStar.Tc.Tc.fst"
let _43_3296 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (
# 1909 "FStar.Tc.Tc.fst"
let _43_3298 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
in (
# 1910 "FStar.Tc.Tc.fst"
let _43_3300 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _122_1332 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _122_1332 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

# 1915 "FStar.Tc.Tc.fst"
let tc_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1916 "FStar.Tc.Tc.fst"
let _43_3308 = (tc_partial_modul env modul)
in (match (_43_3308) with
| (modul, env) -> begin
(finish_partial_modul env modul)
end)))

# 1919 "FStar.Tc.Tc.fst"
let add_modul_to_tcenv : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Tc_Env.env = (fun en m -> (
# 1920 "FStar.Tc.Tc.fst"
let do_sigelt = (fun en elt -> (
# 1921 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt en elt)
in (
# 1922 "FStar.Tc.Tc.fst"
let _43_3315 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (
# 1925 "FStar.Tc.Tc.fst"
let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _122_1345 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _122_1345 m)))))

# 1928 "FStar.Tc.Tc.fst"
let check_module : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env) = (fun env m -> (
# 1929 "FStar.Tc.Tc.fst"
let _43_3320 = if ((let _122_1350 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _122_1350)) <> 0) then begin
(let _122_1351 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _122_1351))
end else begin
()
end
in (
# 1932 "FStar.Tc.Tc.fst"
let _43_3333 = if m.FStar_Absyn_Syntax.is_deserialized then begin
(
# 1934 "FStar.Tc.Tc.fst"
let env' = (add_modul_to_tcenv env m)
in (m, env'))
end else begin
(
# 1937 "FStar.Tc.Tc.fst"
let _43_3325 = (tc_modul env m)
in (match (_43_3325) with
| (m, env) -> begin
(
# 1938 "FStar.Tc.Tc.fst"
let _43_3329 = if (FStar_ST.read FStar_Options.serialize_mods) then begin
(
# 1940 "FStar.Tc.Tc.fst"
let c_file_name = (let _122_1356 = (let _122_1355 = (let _122_1354 = (let _122_1353 = (let _122_1352 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _122_1352 "/"))
in (Prims.strcat _122_1353 FStar_Options.cache_dir))
in (Prims.strcat _122_1354 "/"))
in (Prims.strcat _122_1355 (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)))
in (Prims.strcat _122_1356 ".cache"))
in (
# 1941 "FStar.Tc.Tc.fst"
let _43_3327 = (FStar_Util.print_string (Prims.strcat (Prims.strcat "Serializing module " (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)) "\n"))
in (let _122_1357 = (FStar_Util.get_owriter c_file_name)
in (FStar_Absyn_SSyntax.serialize_modul _122_1357 m))))
end else begin
()
end
in (m, env))
end))
end
in (match (_43_3333) with
| (m, env) -> begin
(
# 1947 "FStar.Tc.Tc.fst"
let _43_3334 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _122_1358 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _122_1358))
end else begin
()
end
in ((m)::[], env))
end))))




