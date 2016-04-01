
open Prims
# 30 "FStar.Tc.Tc.fst"
let syn' = (fun env k -> (let _135_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _135_11 (Some (k)))))

# 31 "FStar.Tc.Tc.fst"
let log : FStar_Tc_Env.env  ->  Prims.bool = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _135_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _135_14))))))

# 32 "FStar.Tc.Tc.fst"
let rng : FStar_Tc_Env.env  ->  FStar_Range.range = (fun env -> (FStar_Tc_Env.get_range env))

# 33 "FStar.Tc.Tc.fst"
let instantiate_both : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (
# 33 "FStar.Tc.Tc.fst"
let _46_24 = env
in {FStar_Tc_Env.solver = _46_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _46_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_24.FStar_Tc_Env.default_effects}))

# 34 "FStar.Tc.Tc.fst"
let no_inst : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (
# 34 "FStar.Tc.Tc.fst"
let _46_27 = env
in {FStar_Tc_Env.solver = _46_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _46_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_27.FStar_Tc_Env.default_effects}))

# 35 "FStar.Tc.Tc.fst"
let mk_lex_list : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (
# 37 "FStar.Tc.Tc.fst"
let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _135_34 = (let _135_33 = (let _135_32 = (let _135_27 = (let _135_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _135_25 -> FStar_Util.Inl (_135_25)) _135_26))
in (_135_27, Some (FStar_Absyn_Syntax.Implicit (false))))
in (let _135_31 = (let _135_30 = (FStar_Absyn_Syntax.varg v)
in (let _135_29 = (let _135_28 = (FStar_Absyn_Syntax.varg tl)
in (_135_28)::[])
in (_135_30)::_135_29))
in (_135_32)::_135_31))
in (FStar_Absyn_Util.lex_pair, _135_33))
in (FStar_Absyn_Syntax.mk_Exp_app _135_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

# 39 "FStar.Tc.Tc.fst"
let is_eq : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _46_1 -> (match (_46_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _46_37 -> begin
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
let norm_t : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _135_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _135_47 env t)))

# 48 "FStar.Tc.Tc.fst"
let norm_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let _135_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _135_52 env k)))

# 49 "FStar.Tc.Tc.fst"
let norm_c : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun env c -> (let _135_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _135_57 env c)))

# 50 "FStar.Tc.Tc.fst"
let fxv_check : FStar_Absyn_Syntax.exp  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either  ->  FStar_Absyn_Syntax.bvvar FStar_Util.set  ->  Prims.unit = (fun head env kt fvs -> (
# 51 "FStar.Tc.Tc.fst"
let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(
# 53 "FStar.Tc.Tc.fst"
let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _135_70 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _135_70))
end
| FStar_Util.Inr (t) -> begin
(let _135_71 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _135_71))
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
let fail = (fun _46_61 -> (match (()) with
| () -> begin
(
# 62 "FStar.Tc.Tc.fst"
let escaping = (let _135_76 = (let _135_75 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _135_75 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _135_76 (FStar_String.concat ", ")))
in (
# 63 "FStar.Tc.Tc.fst"
let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _135_77 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _135_77))
end else begin
(let _135_78 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _135_78))
end
in (let _135_81 = (let _135_80 = (let _135_79 = (FStar_Tc_Env.get_range env)
in (msg, _135_79))
in FStar_Absyn_Syntax.Error (_135_80))
in (Prims.raise _135_81))))
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
| _46_71 -> begin
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
| _46_78 -> begin
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
let maybe_make_subst = (fun _46_2 -> (match (_46_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _46_99 -> begin
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
(let _135_92 = (let _135_91 = (let _135_90 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _135_90))
in FStar_Util.Inl (_135_91))
in (_135_92)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _135_95 = (let _135_94 = (let _135_93 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _135_93))
in FStar_Util.Inr (_135_94))
in (_135_95)::s)
end
end
| _46_114 -> begin
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
| _46_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

# 113 "FStar.Tc.Tc.fst"
let set_lcomp_result : FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.lcomp = (fun lc t -> (
# 114 "FStar.Tc.Tc.fst"
let _46_132 = lc
in {FStar_Absyn_Syntax.eff_name = _46_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _46_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _46_134 -> (match (()) with
| () -> begin
(let _135_104 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _135_104 t))
end))}))

# 116 "FStar.Tc.Tc.fst"
let value_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, FStar_Absyn_Syntax.lcomp) FStar_Util.either  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e tlc -> (
# 117 "FStar.Tc.Tc.fst"
let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _135_111 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _135_111))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (
# 122 "FStar.Tc.Tc.fst"
let t = lc.FStar_Absyn_Syntax.res_typ
in (
# 123 "FStar.Tc.Tc.fst"
let _46_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(
# 126 "FStar.Tc.Tc.fst"
let _46_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_113 = (FStar_Absyn_Print.typ_to_string t)
in (let _135_112 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _135_113 _135_112)))
end else begin
()
end
in (
# 128 "FStar.Tc.Tc.fst"
let _46_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_46_151) with
| (e, g) -> begin
(
# 129 "FStar.Tc.Tc.fst"
let _46_154 = (let _135_119 = (FStar_All.pipe_left (fun _135_118 -> Some (_135_118)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _135_119 env e lc g))
in (match (_46_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_46_158) with
| (e, lc, g) -> begin
(
# 131 "FStar.Tc.Tc.fst"
let _46_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_120 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _135_120))
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
let check_expected_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp Prims.option  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp)  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env copt _46_171 -> (match (_46_171) with
| (e, c) -> begin
(
# 141 "FStar.Tc.Tc.fst"
let expected_c_opt = (match (copt) with
| Some (_46_173) -> begin
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
(let _135_133 = (norm_c env c)
in (e, _135_133, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(
# 162 "FStar.Tc.Tc.fst"
let _46_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_136 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _135_135 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _135_134 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _135_136 _135_135 _135_134))))
end else begin
()
end
in (
# 164 "FStar.Tc.Tc.fst"
let c = (norm_c env c)
in (
# 165 "FStar.Tc.Tc.fst"
let expected_c' = (let _135_137 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _135_137))
in (
# 166 "FStar.Tc.Tc.fst"
let _46_195 = (let _135_138 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _135_138))
in (match (_46_195) with
| (e, _46_193, g) -> begin
(
# 167 "FStar.Tc.Tc.fst"
let _46_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_140 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _135_139 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _135_140 _135_139)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

# 170 "FStar.Tc.Tc.fst"
let no_logical_guard = (fun env _46_202 -> (match (_46_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _135_146 = (let _135_145 = (let _135_144 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _135_143 = (FStar_Tc_Env.get_range env)
in (_135_144, _135_143)))
in FStar_Absyn_Syntax.Error (_135_145))
in (Prims.raise _135_146))
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
(let _135_153 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _135_153))
end))

# 182 "FStar.Tc.Tc.fst"
let with_implicits = (fun imps _46_220 -> (match (_46_220) with
| (e, l, g) -> begin
(e, l, (
# 182 "FStar.Tc.Tc.fst"
let _46_221 = g
in {FStar_Tc_Rel.guard_f = _46_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _46_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

# 183 "FStar.Tc.Tc.fst"
let add_implicit : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * FStar_Int64.int64), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * FStar_Int64.int64)) FStar_Util.either  ->  FStar_Tc_Rel.guard_t  ->  FStar_Tc_Rel.guard_t = (fun u g -> (
# 183 "FStar.Tc.Tc.fst"
let _46_225 = g
in {FStar_Tc_Rel.guard_f = _46_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _46_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

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
let _46_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _135_206 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _135_205 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _135_206 _135_205)))
end else begin
()
end
in (
# 195 "FStar.Tc.Tc.fst"
let _46_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_46_249) with
| (env, _46_248) -> begin
(
# 196 "FStar.Tc.Tc.fst"
let _46_252 = (tc_args env args)
in (match (_46_252) with
| (args, g) -> begin
(let _135_208 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_135_208, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _46_263; FStar_Absyn_Syntax.pos = _46_261; FStar_Absyn_Syntax.fvs = _46_259; FStar_Absyn_Syntax.uvs = _46_257}) -> begin
(
# 200 "FStar.Tc.Tc.fst"
let _46_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_46_272) with
| (_46_269, binders, body) -> begin
(
# 201 "FStar.Tc.Tc.fst"
let _46_275 = (tc_args env args)
in (match (_46_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _135_212 = (let _135_211 = (let _135_210 = (let _135_209 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _135_209))
in (_135_210, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_211))
in (Prims.raise _135_212))
end else begin
(
# 204 "FStar.Tc.Tc.fst"
let _46_308 = (FStar_List.fold_left2 (fun _46_279 b a -> (match (_46_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(
# 207 "FStar.Tc.Tc.fst"
let _46_289 = (let _135_216 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _135_216))
in (match (_46_289) with
| (t, g) -> begin
(
# 208 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _135_218 = (let _135_217 = (FStar_Absyn_Syntax.targ t)
in (_135_217)::args)
in (subst, _135_218, (g)::guards)))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(
# 211 "FStar.Tc.Tc.fst"
let env = (let _135_219 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _135_219))
in (
# 212 "FStar.Tc.Tc.fst"
let _46_301 = (tc_ghost_exp env e)
in (match (_46_301) with
| (e, _46_299, g) -> begin
(
# 213 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (let _135_221 = (let _135_220 = (FStar_Absyn_Syntax.varg e)
in (_135_220)::args)
in (subst, _135_221, (g)::guards)))
end)))
end
| _46_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_46_308) with
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
in (let _135_224 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _135_224))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(
# 224 "FStar.Tc.Tc.fst"
let _46_319 = (tc_kind env k)
in (match (_46_319) with
| (k, f) -> begin
(
# 225 "FStar.Tc.Tc.fst"
let _46_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_46_322) with
| (args, g) -> begin
(
# 226 "FStar.Tc.Tc.fst"
let kabr = ((Prims.fst kabr), args)
in (
# 227 "FStar.Tc.Tc.fst"
let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _135_226 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _135_226))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 231 "FStar.Tc.Tc.fst"
let _46_332 = (tc_binders env bs)
in (match (_46_332) with
| (bs, env, g) -> begin
(
# 232 "FStar.Tc.Tc.fst"
let _46_335 = (tc_kind env k)
in (match (_46_335) with
| (k, f) -> begin
(
# 233 "FStar.Tc.Tc.fst"
let f = (FStar_Tc_Rel.close_guard bs f)
in (let _135_229 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _135_228 = (FStar_Tc_Rel.conj_guard g f)
in (_135_229, _135_228))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _135_230 = (FStar_Tc_Util.new_kvar env)
in (_135_230, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder : FStar_Tc_Env.env  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env x -> (
# 240 "FStar.Tc.Tc.fst"
let _46_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_46_342) with
| (t, g) -> begin
(
# 241 "FStar.Tc.Tc.fst"
let x = (
# 241 "FStar.Tc.Tc.fst"
let _46_343 = x
in {FStar_Absyn_Syntax.v = _46_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _46_343.FStar_Absyn_Syntax.p})
in (
# 242 "FStar.Tc.Tc.fst"
let env' = (let _135_233 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _135_233))
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
let _46_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_46_362) with
| (k, g) -> begin
(
# 252 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inl ((
# 252 "FStar.Tc.Tc.fst"
let _46_363 = a
in {FStar_Absyn_Syntax.v = _46_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _46_363.FStar_Absyn_Syntax.p})), imp)
in (
# 253 "FStar.Tc.Tc.fst"
let env' = (maybe_push_binding env b)
in (
# 254 "FStar.Tc.Tc.fst"
let _46_370 = (aux env' bs)
in (match (_46_370) with
| (bs, env', g') -> begin
(let _135_241 = (let _135_240 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _135_240))
in ((b)::bs, env', _135_241))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(
# 258 "FStar.Tc.Tc.fst"
let _46_376 = (tc_vbinder env x)
in (match (_46_376) with
| (x, env', g) -> begin
(
# 259 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inr (x), imp)
in (
# 260 "FStar.Tc.Tc.fst"
let _46_381 = (aux env' bs)
in (match (_46_381) with
| (bs, env', g') -> begin
(let _135_243 = (let _135_242 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _135_242))
in ((b)::bs, env', _135_243))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.args * FStar_Tc_Rel.guard_t) = (fun env args -> (FStar_List.fold_right (fun _46_386 _46_389 -> (match ((_46_386, _46_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(
# 268 "FStar.Tc.Tc.fst"
let _46_396 = (tc_typ env t)
in (match (_46_396) with
| (t, _46_394, g') -> begin
(let _135_248 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _135_248))
end))
end
| FStar_Util.Inr (e) -> begin
(
# 271 "FStar.Tc.Tc.fst"
let _46_403 = (tc_ghost_exp env e)
in (match (_46_403) with
| (e, _46_401, g') -> begin
(let _135_249 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _135_249))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list Prims.list  ->  (FStar_Absyn_Syntax.args Prims.list * FStar_Tc_Rel.guard_t) = (fun env pats -> (FStar_List.fold_right (fun p _46_409 -> (match (_46_409) with
| (pats, g) -> begin
(
# 275 "FStar.Tc.Tc.fst"
let _46_412 = (tc_args env p)
in (match (_46_412) with
| (args, g') -> begin
(let _135_254 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _135_254))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 280 "FStar.Tc.Tc.fst"
let _46_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_46_419) with
| (t, g) -> begin
(let _135_257 = (FStar_Absyn_Syntax.mk_Total t)
in (_135_257, g))
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
let tc = (let _135_260 = (let _135_259 = (let _135_258 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_135_258)::c.FStar_Absyn_Syntax.effect_args)
in (head, _135_259))
in (FStar_Absyn_Syntax.mk_Typ_app _135_260 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (
# 287 "FStar.Tc.Tc.fst"
let _46_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_46_427) with
| (tc, f) -> begin
(
# 288 "FStar.Tc.Tc.fst"
let _46_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_46_431) with
| (_46_429, args) -> begin
(
# 289 "FStar.Tc.Tc.fst"
let _46_443 = (match (args) with
| (FStar_Util.Inl (res), _46_436)::args -> begin
(res, args)
end
| _46_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_46_443) with
| (res, args) -> begin
(
# 292 "FStar.Tc.Tc.fst"
let _46_459 = (let _135_262 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _46_3 -> (match (_46_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(
# 294 "FStar.Tc.Tc.fst"
let _46_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_46_450) with
| (env, _46_449) -> begin
(
# 295 "FStar.Tc.Tc.fst"
let _46_455 = (tc_ghost_exp env e)
in (match (_46_455) with
| (e, _46_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _135_262 FStar_List.unzip))
in (match (_46_459) with
| (flags, guards) -> begin
(let _135_264 = (FStar_Absyn_Syntax.mk_Comp (
# 298 "FStar.Tc.Tc.fst"
let _46_460 = c
in {FStar_Absyn_Syntax.effect_name = _46_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _46_460.FStar_Absyn_Syntax.flags}))
in (let _135_263 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_135_264, _135_263)))
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
let _46_472 = a
in {FStar_Absyn_Syntax.v = _46_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _46_472.FStar_Absyn_Syntax.p})
in (
# 311 "FStar.Tc.Tc.fst"
let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (
# 312 "FStar.Tc.Tc.fst"
let _46_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_46_479) with
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
let _46_484 = i
in {FStar_Absyn_Syntax.v = _46_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _46_484.FStar_Absyn_Syntax.p})
in (let _135_287 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_135_287, qk, FStar_Tc_Rel.trivial_guard)))))
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
let _46_491 = i
in {FStar_Absyn_Syntax.v = _46_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _46_491.FStar_Absyn_Syntax.p})
in (let _135_288 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_135_288, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(
# 329 "FStar.Tc.Tc.fst"
let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _46_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (
# 332 "FStar.Tc.Tc.fst"
let i = (
# 332 "FStar.Tc.Tc.fst"
let _46_501 = i
in {FStar_Absyn_Syntax.v = _46_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _46_501.FStar_Absyn_Syntax.p})
in (
# 333 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (
# 334 "FStar.Tc.Tc.fst"
let _46_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_46_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(
# 338 "FStar.Tc.Tc.fst"
let _46_516 = (tc_binders env bs)
in (match (_46_516) with
| (bs, env, g) -> begin
(
# 339 "FStar.Tc.Tc.fst"
let _46_519 = (tc_comp env cod)
in (match (_46_519) with
| (cod, f) -> begin
(
# 340 "FStar.Tc.Tc.fst"
let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (
# 341 "FStar.Tc.Tc.fst"
let _46_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _46_542; FStar_Absyn_Syntax.result_typ = _46_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _46_536)::(FStar_Util.Inl (post), _46_531)::(FStar_Util.Inr (pats), _46_526)::[]; FStar_Absyn_Syntax.flags = _46_522}) -> begin
(
# 345 "FStar.Tc.Tc.fst"
let rec extract_pats = (fun pats -> (match ((let _135_293 = (FStar_Absyn_Util.compress_exp pats)
in _135_293.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _46_557); FStar_Absyn_Syntax.tk = _46_554; FStar_Absyn_Syntax.pos = _46_552; FStar_Absyn_Syntax.fvs = _46_550; FStar_Absyn_Syntax.uvs = _46_548}, _46_572::(FStar_Util.Inr (hd), _46_569)::(FStar_Util.Inr (tl), _46_564)::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(
# 347 "FStar.Tc.Tc.fst"
let _46_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_46_578) with
| (head, args) -> begin
(
# 348 "FStar.Tc.Tc.fst"
let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _46_585 -> begin
[]
end)
in (let _135_294 = (extract_pats tl)
in (FStar_List.append pat _135_294)))
end))
end
| _46_588 -> begin
[]
end))
in (
# 354 "FStar.Tc.Tc.fst"
let pats = (let _135_295 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _135_295))
in (
# 355 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _46_594 -> (match (_46_594) with
| (b, _46_593) -> begin
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
(let _135_298 = (let _135_297 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _135_297))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _135_298))
end))))
end
| _46_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _135_300 = (let _135_299 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _135_299))
in (t, FStar_Absyn_Syntax.ktype, _135_300))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(
# 368 "FStar.Tc.Tc.fst"
let _46_613 = (tc_binders env bs)
in (match (_46_613) with
| (bs, env, g) -> begin
(
# 369 "FStar.Tc.Tc.fst"
let _46_617 = (tc_typ env t)
in (match (_46_617) with
| (t, k, f) -> begin
(
# 370 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _135_305 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _135_304 = (let _135_303 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _135_303))
in (_135_305, k, _135_304))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(
# 374 "FStar.Tc.Tc.fst"
let _46_626 = (tc_vbinder env x)
in (match (_46_626) with
| (x, env, f1) -> begin
(
# 375 "FStar.Tc.Tc.fst"
let _46_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_308 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _135_307 = (FStar_Absyn_Print.typ_to_string phi)
in (let _135_306 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _135_308 _135_307 _135_306))))
end else begin
()
end
in (
# 380 "FStar.Tc.Tc.fst"
let _46_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_46_634) with
| (phi, f2) -> begin
(let _135_315 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _135_314 = (let _135_313 = (let _135_312 = (let _135_311 = (FStar_Absyn_Syntax.v_binder x)
in (_135_311)::[])
in (FStar_Tc_Rel.close_guard _135_312 f2))
in (FStar_Tc_Rel.conj_guard f1 _135_313))
in (_135_315, FStar_Absyn_Syntax.ktype, _135_314)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(
# 384 "FStar.Tc.Tc.fst"
let _46_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_318 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _135_317 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _135_316 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _135_318 _135_317 _135_316))))
end else begin
()
end
in (
# 388 "FStar.Tc.Tc.fst"
let _46_644 = (tc_typ (no_inst env) head)
in (match (_46_644) with
| (head, k1', f1) -> begin
(
# 389 "FStar.Tc.Tc.fst"
let args0 = args
in (
# 390 "FStar.Tc.Tc.fst"
let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (
# 392 "FStar.Tc.Tc.fst"
let _46_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_322 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _135_321 = (FStar_Absyn_Print.typ_to_string head)
in (let _135_320 = (FStar_Absyn_Print.kind_to_string k1')
in (let _135_319 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _135_322 _135_321 _135_320 _135_319)))))
end else begin
()
end
in (
# 398 "FStar.Tc.Tc.fst"
let check_app = (fun _46_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_46_652) -> begin
(
# 400 "FStar.Tc.Tc.fst"
let _46_656 = (tc_args env args)
in (match (_46_656) with
| (args, g) -> begin
(
# 401 "FStar.Tc.Tc.fst"
let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (
# 402 "FStar.Tc.Tc.fst"
let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (
# 403 "FStar.Tc.Tc.fst"
let kres = (let _135_325 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _135_325 Prims.fst))
in (
# 404 "FStar.Tc.Tc.fst"
let bs = (let _135_326 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _135_326))
in (
# 405 "FStar.Tc.Tc.fst"
let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (
# 406 "FStar.Tc.Tc.fst"
let _46_662 = (let _135_327 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _135_327))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(
# 410 "FStar.Tc.Tc.fst"
let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _135_338 = (FStar_Absyn_Util.subst_kind subst kres)
in (_135_338, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit (_)))::_)) -> begin
(let _135_342 = (let _135_341 = (let _135_340 = (let _135_339 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _135_339))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _135_340))
in FStar_Absyn_Syntax.Error (_135_341))
in (Prims.raise _135_342))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_)))::rest, [])) -> begin
(
# 418 "FStar.Tc.Tc.fst"
let formal = (FStar_List.hd formals)
in (
# 419 "FStar.Tc.Tc.fst"
let _46_743 = (let _135_343 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _135_343))
in (match (_46_743) with
| (t, u) -> begin
(
# 420 "FStar.Tc.Tc.fst"
let targ = (let _135_345 = (FStar_All.pipe_left (fun _135_344 -> Some (_135_344)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inl (t), _135_345))
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
let _46_776 = (let _135_346 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _135_346))
in (match (_46_776) with
| (e, u) -> begin
(
# 429 "FStar.Tc.Tc.fst"
let varg = (let _135_348 = (FStar_All.pipe_left (fun _135_347 -> Some (_135_347)) (FStar_Absyn_Syntax.Implicit (false)))
in (FStar_Util.Inr (e), _135_348))
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
let _46_797 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_350 = (FStar_Absyn_Print.arg_to_string actual)
in (let _135_349 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _135_350 _135_349)))
end else begin
()
end
in (
# 441 "FStar.Tc.Tc.fst"
let _46_803 = (tc_typ_check (
# 441 "FStar.Tc.Tc.fst"
let _46_799 = env
in {FStar_Tc_Env.solver = _46_799.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_799.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_799.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_799.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_799.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_799.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_799.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_799.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_799.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_799.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_799.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_799.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_799.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_799.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_799.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_799.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _46_799.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_799.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_799.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_46_803) with
| (t, g') -> begin
(
# 442 "FStar.Tc.Tc.fst"
let _46_804 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_351 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _135_351))
end else begin
()
end
in (
# 444 "FStar.Tc.Tc.fst"
let actual = (FStar_Util.Inl (t), imp)
in (
# 445 "FStar.Tc.Tc.fst"
let g' = (let _135_353 = (let _135_352 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _135_352))
in (FStar_Tc_Rel.imp_guard _135_353 g'))
in (
# 446 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal actual)
in (let _135_354 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _135_354 formals actuals))))))
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
let _46_820 = env'
in {FStar_Tc_Env.solver = _46_820.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_820.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_820.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_820.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_820.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_820.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_820.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_820.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_820.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_820.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_820.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_820.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_820.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_820.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_820.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_820.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _46_820.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_820.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_820.FStar_Tc_Env.default_effects})
in (
# 453 "FStar.Tc.Tc.fst"
let _46_823 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_356 = (FStar_Absyn_Print.arg_to_string actual)
in (let _135_355 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _135_356 _135_355)))
end else begin
()
end
in (
# 454 "FStar.Tc.Tc.fst"
let _46_829 = (tc_ghost_exp env' v)
in (match (_46_829) with
| (v, _46_827, g') -> begin
(
# 455 "FStar.Tc.Tc.fst"
let actual = (FStar_Util.Inr (v), imp)
in (
# 456 "FStar.Tc.Tc.fst"
let g' = (let _135_358 = (let _135_357 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _135_357))
in (FStar_Tc_Rel.imp_guard _135_358 g'))
in (
# 457 "FStar.Tc.Tc.fst"
let subst = (maybe_extend_subst subst formal actual)
in (let _135_359 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _135_359 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _46_836), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(
# 463 "FStar.Tc.Tc.fst"
let tv = (FStar_Absyn_Util.b2t v)
in (let _135_361 = (let _135_360 = (FStar_Absyn_Syntax.targ tv)
in (_135_360)::actuals)
in (check_args outargs subst g ((formal)::formals) _135_361)))
end
| _46_846 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_46_848), _46_851), (FStar_Util.Inl (_46_854), _46_857)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_46_861, []) -> begin
(let _135_363 = (let _135_362 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _135_362))
in (_135_363, (FStar_List.rev outargs), g))
end
| ([], _46_866) -> begin
(let _135_371 = (let _135_370 = (let _135_369 = (let _135_368 = (let _135_366 = (let _135_365 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _46_4 -> (match (_46_4) with
| (_46_870, Some (FStar_Absyn_Syntax.Implicit (_46_872))) -> begin
false
end
| _46_877 -> begin
true
end))))
in (FStar_List.length _135_365))
in (FStar_All.pipe_right _135_366 FStar_Util.string_of_int))
in (let _135_367 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _135_368 _135_367)))
in (_135_369, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_370))
in (Prims.raise _135_371))
end))
in (check_args [] [] f1 formals args))
end
| _46_879 -> begin
(let _135_374 = (let _135_373 = (let _135_372 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_135_372, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_373))
in (Prims.raise _135_374))
end)
end))
in (match ((let _135_378 = (let _135_375 = (FStar_Absyn_Util.compress_typ head)
in _135_375.FStar_Absyn_Syntax.n)
in (let _135_377 = (let _135_376 = (FStar_Absyn_Util.compress_kind k1)
in _135_376.FStar_Absyn_Syntax.n)
in (_135_378, _135_377)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_46_881), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
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
| _46_892 -> begin
(
# 496 "FStar.Tc.Tc.fst"
let _46_896 = (check_app ())
in (match (_46_896) with
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
let _46_904 = (tc_kind env k1)
in (match (_46_904) with
| (k1, f1) -> begin
(
# 504 "FStar.Tc.Tc.fst"
let _46_907 = (tc_typ_check env t1 k1)
in (match (_46_907) with
| (t1, f2) -> begin
(let _135_382 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _135_381 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_135_382, k1, _135_381)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_46_909, k1) -> begin
(
# 508 "FStar.Tc.Tc.fst"
let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(
# 511 "FStar.Tc.Tc.fst"
let _46_918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _135_384 = (FStar_Absyn_Print.typ_to_string s)
in (let _135_383 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _135_384 _135_383)))
end else begin
()
end
in (let _135_387 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_135_387, k1, FStar_Tc_Rel.trivial_guard)))
end
| _46_921 -> begin
(
# 515 "FStar.Tc.Tc.fst"
let _46_922 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _135_389 = (FStar_Absyn_Print.typ_to_string s)
in (let _135_388 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _135_389 _135_388)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(
# 520 "FStar.Tc.Tc.fst"
let _46_933 = (tc_typ env t)
in (match (_46_933) with
| (t, k, f) -> begin
(let _135_390 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_135_390, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(
# 524 "FStar.Tc.Tc.fst"
let _46_944 = (tc_typ env t)
in (match (_46_944) with
| (t, k, f) -> begin
(let _135_391 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_135_391, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(
# 528 "FStar.Tc.Tc.fst"
let _46_953 = (tc_typ env t)
in (match (_46_953) with
| (t, k, f) -> begin
(let _135_392 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_135_392, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(
# 532 "FStar.Tc.Tc.fst"
let _46_961 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_46_961) with
| (quant, f) -> begin
(
# 533 "FStar.Tc.Tc.fst"
let _46_964 = (tc_pats env pats)
in (match (_46_964) with
| (pats, g) -> begin
(
# 534 "FStar.Tc.Tc.fst"
let g = (
# 534 "FStar.Tc.Tc.fst"
let _46_965 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _46_965.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _46_965.FStar_Tc_Rel.implicits})
in (let _135_395 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _135_394 = (FStar_Tc_Util.force_tk quant)
in (let _135_393 = (FStar_Tc_Rel.conj_guard f g)
in (_135_395, _135_394, _135_393)))))
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
| _46_972 -> begin
(let _135_397 = (let _135_396 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _135_396))
in (FStar_All.failwith _135_397))
end))))))
and tc_typ_check : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env t k -> (
# 545 "FStar.Tc.Tc.fst"
let _46_979 = (tc_typ env t)
in (match (_46_979) with
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
| FStar_Absyn_Syntax.Exp_uvar (_46_988, t1) -> begin
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
let _46_995 = x
in {FStar_Absyn_Syntax.v = _46_995.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _46_995.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (
# 563 "FStar.Tc.Tc.fst"
let _46_1001 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_46_1001) with
| (e, t, implicits) -> begin
(
# 564 "FStar.Tc.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _135_404 = (let _135_403 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _135_403))
in FStar_Util.Inr (_135_404))
end
in (let _135_405 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _135_405)))
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
let _46_1008 = v
in {FStar_Absyn_Syntax.v = _46_1008.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _46_1008.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (
# 570 "FStar.Tc.Tc.fst"
let _46_1014 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_46_1014) with
| (e, t, implicits) -> begin
(
# 572 "FStar.Tc.Tc.fst"
let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _135_407 = (let _135_406 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _135_406))
in FStar_Util.Inr (_135_407))
end
in (
# 573 "FStar.Tc.Tc.fst"
let is_data_ctor = (fun _46_5 -> (match (_46_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _46_1024 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _135_413 = (let _135_412 = (let _135_411 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _135_410 = (FStar_Tc_Env.get_range env)
in (_135_411, _135_410)))
in FStar_Absyn_Syntax.Error (_135_412))
in (Prims.raise _135_413))
end else begin
(let _135_414 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _135_414))
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
let fail = (fun msg t -> (let _135_419 = (let _135_418 = (let _135_417 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_135_417, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_418))
in (Prims.raise _135_419)))
in (
# 588 "FStar.Tc.Tc.fst"
let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(
# 596 "FStar.Tc.Tc.fst"
let _46_1045 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _46_1044 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 597 "FStar.Tc.Tc.fst"
let _46_1050 = (tc_binders env bs)
in (match (_46_1050) with
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
let rec as_function_typ = (fun norm t -> (match ((let _135_428 = (FStar_Absyn_Util.compress_typ t)
in _135_428.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(
# 606 "FStar.Tc.Tc.fst"
let _46_1079 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _46_1078 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 607 "FStar.Tc.Tc.fst"
let _46_1084 = (tc_binders env bs)
in (match (_46_1084) with
| (bs, envbody, g) -> begin
(
# 608 "FStar.Tc.Tc.fst"
let _46_1088 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_46_1088) with
| (envbody, _46_1087) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(
# 620 "FStar.Tc.Tc.fst"
let rec tc_binders = (fun _46_1098 bs_annot c bs -> (match (_46_1098) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _135_437 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _135_437))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_46_1113), _46_1116), (FStar_Util.Inr (_46_1119), _46_1122)) -> begin
(
# 626 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _46_1129), (FStar_Util.Inl (b), imp)) -> begin
(
# 630 "FStar.Tc.Tc.fst"
let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 631 "FStar.Tc.Tc.fst"
let _46_1147 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _46_1139 -> begin
(
# 634 "FStar.Tc.Tc.fst"
let _46_1142 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_46_1142) with
| (k, g1) -> begin
(
# 635 "FStar.Tc.Tc.fst"
let g2 = (FStar_Tc_Rel.keq env None ka k)
in (
# 636 "FStar.Tc.Tc.fst"
let g = (let _135_438 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _135_438))
in (k, g)))
end))
end)
in (match (_46_1147) with
| (k, g) -> begin
(
# 638 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inl ((
# 638 "FStar.Tc.Tc.fst"
let _46_1148 = b
in {FStar_Absyn_Syntax.v = _46_1148.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _46_1148.FStar_Absyn_Syntax.p})), imp)
in (
# 639 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 640 "FStar.Tc.Tc.fst"
let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _46_1156), (FStar_Util.Inr (y), imp)) -> begin
(
# 644 "FStar.Tc.Tc.fst"
let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 645 "FStar.Tc.Tc.fst"
let _46_1178 = (match ((let _135_439 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _135_439.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _46_1166 -> begin
(
# 648 "FStar.Tc.Tc.fst"
let _46_1167 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_440 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _135_440))
end else begin
()
end
in (
# 649 "FStar.Tc.Tc.fst"
let _46_1173 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_46_1173) with
| (t, _46_1171, g1) -> begin
(
# 650 "FStar.Tc.Tc.fst"
let g2 = (FStar_Tc_Rel.teq env tx t)
in (
# 651 "FStar.Tc.Tc.fst"
let g = (let _135_441 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _135_441))
in (t, g)))
end)))
end)
in (match (_46_1178) with
| (t, g) -> begin
(
# 653 "FStar.Tc.Tc.fst"
let b = (FStar_Util.Inr ((
# 653 "FStar.Tc.Tc.fst"
let _46_1179 = y
in {FStar_Absyn_Syntax.v = _46_1179.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _46_1179.FStar_Absyn_Syntax.p})), imp)
in (
# 654 "FStar.Tc.Tc.fst"
let env = (maybe_push_binding env b)
in (
# 655 "FStar.Tc.Tc.fst"
let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _46_1185 -> begin
(let _135_444 = (let _135_443 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _135_442 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _135_443 _135_442)))
in (fail _135_444 t))
end)
end
| ([], _46_1188) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _46_1197; FStar_Absyn_Syntax.pos = _46_1195; FStar_Absyn_Syntax.fvs = _46_1193; FStar_Absyn_Syntax.uvs = _46_1191} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _135_446 = (let _135_445 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _135_445))
in (fail _135_446 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_46_1205, []) -> begin
(
# 669 "FStar.Tc.Tc.fst"
let c = (let _135_447 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _135_447 c.FStar_Absyn_Syntax.pos))
in (let _135_448 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _135_448)))
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
let _46_1214 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_453 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _135_453))
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
let _46_1217 = env
in {FStar_Tc_Env.solver = _46_1217.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_1217.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_1217.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_1217.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_1217.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_1217.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_1217.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_1217.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_1217.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_1217.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_1217.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_1217.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_1217.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _46_1217.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_1217.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_1217.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_1217.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_1217.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_1217.FStar_Tc_Env.default_effects})
in (
# 679 "FStar.Tc.Tc.fst"
let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_46_1224), _46_1227) -> begin
[]
end
| (FStar_Util.Inr (x), _46_1232) -> begin
(match ((let _135_459 = (let _135_458 = (let _135_457 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _135_457))
in (FStar_Absyn_Util.unrefine _135_458))
in _135_459.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_46_1235) -> begin
[]
end
| _46_1238 -> begin
(let _135_460 = (FStar_Absyn_Util.bvar_to_exp x)
in (_135_460)::[])
end)
end)))))
in (
# 687 "FStar.Tc.Tc.fst"
let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (
# 688 "FStar.Tc.Tc.fst"
let as_lex_list = (fun dec -> (
# 689 "FStar.Tc.Tc.fst"
let _46_1245 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_46_1245) with
| (head, _46_1244) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _46_1248) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _46_1252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (
# 693 "FStar.Tc.Tc.fst"
let prev_dec = (
# 694 "FStar.Tc.Tc.fst"
let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _46_6 -> (match (_46_6) with
| FStar_Absyn_Syntax.DECREASES (_46_1256) -> begin
true
end
| _46_1259 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(
# 697 "FStar.Tc.Tc.fst"
let _46_1263 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _135_469 = (let _135_468 = (let _135_467 = (let _135_465 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _135_464 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _135_465 _135_464)))
in (let _135_466 = (FStar_Tc_Env.get_range env)
in (_135_467, _135_466)))
in FStar_Absyn_Syntax.Error (_135_468))
in (Prims.raise _135_469))
end else begin
()
end
in (
# 701 "FStar.Tc.Tc.fst"
let dec = (as_lex_list dec)
in (
# 702 "FStar.Tc.Tc.fst"
let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _46_1271), (FStar_Util.Inl (actual), _46_1276)) -> begin
(let _135_473 = (let _135_472 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _135_472))
in FStar_Util.Inl (_135_473))
end
| ((FStar_Util.Inr (formal), _46_1282), (FStar_Util.Inr (actual), _46_1287)) -> begin
(let _135_475 = (let _135_474 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _135_474))
in FStar_Util.Inr (_135_475))
end
| _46_1291 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _46_1294 -> begin
(
# 709 "FStar.Tc.Tc.fst"
let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _46_1299 -> begin
(mk_lex_list actual_args)
end))
end))
in (
# 714 "FStar.Tc.Tc.fst"
let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _46_1303 -> (match (_46_1303) with
| (l, t0) -> begin
(
# 715 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _135_477 = (FStar_Absyn_Util.compress_typ t)
in _135_477.FStar_Absyn_Syntax.n)) with
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
let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _46_7 -> (match (_46_7) with
| FStar_Absyn_Syntax.DECREASES (_46_1319) -> begin
true
end
| _46_1322 -> begin
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
let subst = (let _135_481 = (let _135_480 = (let _135_479 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _135_479))
in FStar_Util.Inr (_135_480))
in (_135_481)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _135_486 = (let _135_485 = (let _135_484 = (FStar_Absyn_Syntax.varg dec)
in (let _135_483 = (let _135_482 = (FStar_Absyn_Syntax.varg prev_dec)
in (_135_482)::[])
in (_135_484)::_135_483))
in (precedes, _135_485))
in (FStar_Absyn_Syntax.mk_Typ_app _135_486 None r))))
end
| _46_1330 -> begin
(
# 731 "FStar.Tc.Tc.fst"
let formal_args = (let _135_489 = (let _135_488 = (let _135_487 = (FStar_Absyn_Syntax.v_binder y)
in (_135_487)::[])
in (FStar_List.append bs _135_488))
in (FStar_All.pipe_right _135_489 filter_types_and_functions))
in (
# 732 "FStar.Tc.Tc.fst"
let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _46_1335 -> begin
(mk_lex_list formal_args)
end)
in (let _135_494 = (let _135_493 = (let _135_492 = (FStar_Absyn_Syntax.varg lhs)
in (let _135_491 = (let _135_490 = (FStar_Absyn_Syntax.varg prev_dec)
in (_135_490)::[])
in (_135_492)::_135_491))
in (precedes, _135_493))
in (FStar_Absyn_Syntax.mk_Typ_app _135_494 None r))))
end)
in (
# 737 "FStar.Tc.Tc.fst"
let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (
# 738 "FStar.Tc.Tc.fst"
let bs = (FStar_List.append bs (((FStar_Util.Inr ((
# 738 "FStar.Tc.Tc.fst"
let _46_1339 = x
in {FStar_Absyn_Syntax.v = _46_1339.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _46_1339.FStar_Absyn_Syntax.p})), imp))::[]))
in (
# 739 "FStar.Tc.Tc.fst"
let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (
# 740 "FStar.Tc.Tc.fst"
let _46_1343 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_497 = (FStar_Absyn_Print.lbname_to_string l)
in (let _135_496 = (FStar_Absyn_Print.typ_to_string t)
in (let _135_495 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _135_497 _135_496 _135_495))))
end else begin
()
end
in (
# 743 "FStar.Tc.Tc.fst"
let _46_1350 = (let _135_499 = (let _135_498 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _135_498 Prims.fst))
in (tc_typ _135_499 t'))
in (match (_46_1350) with
| (t', _46_1347, _46_1349) -> begin
(l, t')
end)))))))))
end
| _46_1352 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _46_1354 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _135_505 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _46_1359 -> (match (_46_1359) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _135_504 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _46_8 -> (match (_46_8) with
| (FStar_Util.Inl (x), t) -> begin
(let _135_503 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_135_503)::[])
end
| _46_1366 -> begin
[]
end))))
in (_135_505, _135_504)))))))))))
end))
in (
# 755 "FStar.Tc.Tc.fst"
let _46_1371 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_46_1371) with
| (bs, envbody, g, c) -> begin
(
# 756 "FStar.Tc.Tc.fst"
let _46_1374 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_46_1374) with
| (envbody, letrecs) -> begin
(
# 757 "FStar.Tc.Tc.fst"
let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _46_1378) -> begin
(
# 763 "FStar.Tc.Tc.fst"
let _46_1388 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_46_1388) with
| (_46_1382, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _46_1390 -> begin
if (not (norm)) then begin
(let _135_506 = (whnf env t)
in (as_function_typ true _135_506))
end else begin
(
# 771 "FStar.Tc.Tc.fst"
let _46_1399 = (expected_function_typ env None)
in (match (_46_1399) with
| (_46_1392, bs, _46_1395, c_opt, envbody, g) -> begin
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
let _46_1403 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_46_1403) with
| (env, topt) -> begin
(
# 777 "FStar.Tc.Tc.fst"
let _46_1410 = (expected_function_typ env topt)
in (match (_46_1410) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(
# 778 "FStar.Tc.Tc.fst"
let _46_1416 = (tc_exp (
# 778 "FStar.Tc.Tc.fst"
let _46_1411 = envbody
in {FStar_Tc_Env.solver = _46_1411.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_1411.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_1411.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_1411.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_1411.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_1411.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_1411.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_1411.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_1411.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_1411.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_1411.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_1411.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_1411.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_1411.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _46_1411.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _46_1411.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_1411.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_1411.FStar_Tc_Env.default_effects}) body)
in (match (_46_1416) with
| (body, cbody, guard_body) -> begin
(
# 779 "FStar.Tc.Tc.fst"
let _46_1417 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _135_509 = (FStar_Absyn_Print.exp_to_string body)
in (let _135_508 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _135_507 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _135_509 _135_508 _135_507))))
end else begin
()
end
in (
# 781 "FStar.Tc.Tc.fst"
let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (
# 782 "FStar.Tc.Tc.fst"
let _46_1420 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _135_510 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _135_510))
end else begin
()
end
in (
# 784 "FStar.Tc.Tc.fst"
let _46_1427 = (let _135_512 = (let _135_511 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _135_511))
in (check_expected_effect (
# 784 "FStar.Tc.Tc.fst"
let _46_1422 = envbody
in {FStar_Tc_Env.solver = _46_1422.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_1422.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_1422.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_1422.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_1422.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_1422.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_1422.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_1422.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_1422.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_1422.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_1422.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_1422.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_1422.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_1422.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_1422.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_1422.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _46_1422.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_1422.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_1422.FStar_Tc_Env.default_effects}) c_opt _135_512))
in (match (_46_1427) with
| (body, cbody, guard) -> begin
(
# 785 "FStar.Tc.Tc.fst"
let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (
# 786 "FStar.Tc.Tc.fst"
let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(
# 787 "FStar.Tc.Tc.fst"
let _46_1429 = (let _135_513 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _135_513))
in (
# 787 "FStar.Tc.Tc.fst"
let _46_1431 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _46_1431.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _46_1431.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
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
let e = (let _135_515 = (let _135_514 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_135_514, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _135_515 None top.FStar_Absyn_Syntax.pos))
in (
# 794 "FStar.Tc.Tc.fst"
let _46_1454 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(
# 796 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_46_1443) -> begin
(let _135_518 = (let _135_517 = (let _135_516 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_135_516, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _135_517 None top.FStar_Absyn_Syntax.pos))
in (_135_518, t, guard))
end
| _46_1446 -> begin
(
# 805 "FStar.Tc.Tc.fst"
let _46_1449 = if use_teq then begin
(let _135_519 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _135_519))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_46_1449) with
| (e, guard') -> begin
(let _135_521 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _135_520 = (FStar_Tc_Rel.conj_guard guard guard')
in (_135_521, t, _135_520)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_46_1454) with
| (e, tfun, guard) -> begin
(
# 813 "FStar.Tc.Tc.fst"
let _46_1455 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_524 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _135_523 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _135_522 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _135_524 _135_523 _135_522))))
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
let _46_1460 = (let _135_526 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _135_526 guard))
in (match (_46_1460) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _46_1462 -> begin
(let _135_528 = (let _135_527 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _135_527))
in (FStar_All.failwith _135_528))
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
let _46_1466 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_533 = (let _135_531 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _135_531))
in (let _135_532 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _135_533 _135_532)))
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
| FStar_Absyn_Syntax.Exp_delayed (_46_1472) -> begin
(let _135_557 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _135_557))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _46_1492) -> begin
(
# 839 "FStar.Tc.Tc.fst"
let _46_1497 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_46_1497) with
| (t1, f) -> begin
(
# 840 "FStar.Tc.Tc.fst"
let _46_1501 = (let _135_558 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _135_558 e1))
in (match (_46_1501) with
| (e1, c, g) -> begin
(
# 841 "FStar.Tc.Tc.fst"
let _46_1505 = (let _135_562 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _46_1502 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _135_562 e1 c f))
in (match (_46_1505) with
| (c, f) -> begin
(
# 842 "FStar.Tc.Tc.fst"
let _46_1509 = (let _135_566 = (let _135_565 = (w c)
in (FStar_All.pipe_left _135_565 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _135_566 c))
in (match (_46_1509) with
| (e, c, f2) -> begin
(let _135_568 = (let _135_567 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _135_567))
in (e, c, _135_568))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(
# 846 "FStar.Tc.Tc.fst"
let pats_t = (let _135_574 = (let _135_573 = (let _135_569 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _135_569))
in (let _135_572 = (let _135_571 = (let _135_570 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _135_570))
in (_135_571)::[])
in (_135_573, _135_572)))
in (FStar_Absyn_Syntax.mk_Typ_app _135_574 None FStar_Absyn_Syntax.dummyRange))
in (
# 847 "FStar.Tc.Tc.fst"
let _46_1519 = (let _135_575 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _135_575 e))
in (match (_46_1519) with
| (e, t, g) -> begin
(
# 848 "FStar.Tc.Tc.fst"
let g = (
# 848 "FStar.Tc.Tc.fst"
let _46_1520 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _46_1520.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _46_1520.FStar_Tc_Rel.implicits})
in (
# 849 "FStar.Tc.Tc.fst"
let c = (let _135_576 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _135_576 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _135_577 = (FStar_Absyn_Util.compress_exp e)
in _135_577.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_46_1530, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _46_1535; FStar_Absyn_Syntax.lbeff = _46_1533; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 855 "FStar.Tc.Tc.fst"
let _46_1546 = (let _135_578 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _135_578 e1))
in (match (_46_1546) with
| (e1, c1, g1) -> begin
(
# 856 "FStar.Tc.Tc.fst"
let _46_1550 = (tc_exp env e2)
in (match (_46_1550) with
| (e2, c2, g2) -> begin
(
# 857 "FStar.Tc.Tc.fst"
let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _135_591 = (let _135_589 = (let _135_588 = (let _135_587 = (let _135_586 = (w c)
in (let _135_585 = (let _135_584 = (let _135_583 = (let _135_582 = (let _135_581 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1))
in (_135_581)::[])
in (false, _135_582))
in (_135_583, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _135_584))
in (FStar_All.pipe_left _135_586 _135_585)))
in (_135_587, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_135_588))
in (FStar_Absyn_Syntax.mk_Exp_meta _135_589))
in (let _135_590 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_135_591, c, _135_590))))
end))
end))
end
| _46_1553 -> begin
(
# 860 "FStar.Tc.Tc.fst"
let _46_1557 = (tc_exp env e)
in (match (_46_1557) with
| (e, c, g) -> begin
(let _135_592 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_135_592, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(
# 865 "FStar.Tc.Tc.fst"
let _46_1566 = (tc_exp env e)
in (match (_46_1566) with
| (e, c, g) -> begin
(let _135_593 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_135_593, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(
# 869 "FStar.Tc.Tc.fst"
let env0 = env
in (
# 870 "FStar.Tc.Tc.fst"
let env = (let _135_595 = (let _135_594 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _135_594 Prims.fst))
in (FStar_All.pipe_right _135_595 instantiate_both))
in (
# 871 "FStar.Tc.Tc.fst"
let _46_1573 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_597 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _135_596 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _135_597 _135_596)))
end else begin
()
end
in (
# 872 "FStar.Tc.Tc.fst"
let _46_1578 = (tc_exp (no_inst env) head)
in (match (_46_1578) with
| (head, chead, g_head) -> begin
(
# 873 "FStar.Tc.Tc.fst"
let aux = (fun _46_1580 -> (match (()) with
| () -> begin
(
# 874 "FStar.Tc.Tc.fst"
let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _46_1584) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(
# 877 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _46_1596)::(FStar_Util.Inr (e2), _46_1591)::[] -> begin
(
# 880 "FStar.Tc.Tc.fst"
let _46_1602 = (tc_exp env e1)
in (match (_46_1602) with
| (e1, c1, g1) -> begin
(
# 881 "FStar.Tc.Tc.fst"
let _46_1606 = (tc_exp env e2)
in (match (_46_1606) with
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
(let _135_603 = (let _135_600 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _135_600))
in (let _135_602 = (let _135_601 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _135_601 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _135_603 c2 _135_602)))
end else begin
(let _135_607 = (let _135_604 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _135_604))
in (let _135_606 = (let _135_605 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _135_605 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _135_607 _135_606 c2)))
end
in (
# 888 "FStar.Tc.Tc.fst"
let c = (let _135_610 = (let _135_609 = (FStar_All.pipe_left (fun _135_608 -> Some (_135_608)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_135_609, c2))
in (FStar_Tc_Util.bind env None c1 _135_610))
in (
# 889 "FStar.Tc.Tc.fst"
let e = (let _135_615 = (let _135_614 = (let _135_613 = (FStar_Absyn_Syntax.varg e1)
in (let _135_612 = (let _135_611 = (FStar_Absyn_Syntax.varg e2)
in (_135_611)::[])
in (_135_613)::_135_612))
in (head, _135_614))
in (FStar_Absyn_Syntax.mk_Exp_app _135_615 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _135_617 = (let _135_616 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _135_616))
in (e, c, _135_617)))))))
end))
end))
end
| _46_1613 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _46_1615 -> begin
(
# 896 "FStar.Tc.Tc.fst"
let thead = chead.FStar_Absyn_Syntax.res_typ
in (
# 897 "FStar.Tc.Tc.fst"
let _46_1617 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_619 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _135_618 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _135_619 _135_618)))
end else begin
()
end
in (
# 898 "FStar.Tc.Tc.fst"
let rec check_function_app = (fun norm tf -> (match ((let _135_624 = (FStar_Absyn_Util.unrefine tf)
in _135_624.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(
# 901 "FStar.Tc.Tc.fst"
let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _46_1650)::_46_1646 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(
# 906 "FStar.Tc.Tc.fst"
let _46_1662 = (tc_exp env e)
in (match (_46_1662) with
| (e, c, g_e) -> begin
(
# 907 "FStar.Tc.Tc.fst"
let _46_1666 = (tc_args env tl)
in (match (_46_1666) with
| (args, comps, g_rest) -> begin
(let _135_629 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _135_629))
end))
end))
end))
in (
# 912 "FStar.Tc.Tc.fst"
let _46_1670 = (tc_args env args)
in (match (_46_1670) with
| (args, comps, g_args) -> begin
(
# 913 "FStar.Tc.Tc.fst"
let bs = (let _135_630 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _135_630))
in (
# 914 "FStar.Tc.Tc.fst"
let cres = (let _135_631 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _135_631 top.FStar_Absyn_Syntax.pos))
in (
# 915 "FStar.Tc.Tc.fst"
let _46_1673 = (let _135_633 = (let _135_632 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _135_632))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _135_633))
in (
# 916 "FStar.Tc.Tc.fst"
let comp = (let _135_636 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _135_636))
in (let _135_638 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _135_637 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_135_638, comp, _135_637)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 920 "FStar.Tc.Tc.fst"
let vars = (FStar_Tc_Env.binders env)
in (
# 922 "FStar.Tc.Tc.fst"
let rec tc_args = (fun _46_1690 bs cres args -> (match (_46_1690) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_46_1698)))::rest, (_46_1706, None)::_46_1704) -> begin
(
# 933 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 934 "FStar.Tc.Tc.fst"
let _46_1712 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (
# 935 "FStar.Tc.Tc.fst"
let _46_1716 = (let _135_648 = (let _135_647 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _135_647))
in (FStar_Tc_Rel.new_tvar _135_648 vars k))
in (match (_46_1716) with
| (targ, u) -> begin
(
# 936 "FStar.Tc.Tc.fst"
let _46_1717 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_650 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _135_649 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _135_650 _135_649)))
end else begin
()
end
in (
# 937 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (
# 938 "FStar.Tc.Tc.fst"
let arg = (let _135_651 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (targ), _135_651))
in (let _135_656 = (let _135_655 = (let _135_654 = (let _135_653 = (let _135_652 = (FStar_Tc_Util.as_uvar_t u)
in (_135_652, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_135_653))
in (add_implicit _135_654 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _135_655, fvs))
in (tc_args _135_656 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_46_1725)))::rest, (_46_1733, None)::_46_1731) -> begin
(
# 942 "FStar.Tc.Tc.fst"
let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 943 "FStar.Tc.Tc.fst"
let _46_1739 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (
# 944 "FStar.Tc.Tc.fst"
let _46_1743 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_46_1743) with
| (varg, u) -> begin
(
# 945 "FStar.Tc.Tc.fst"
let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (
# 946 "FStar.Tc.Tc.fst"
let arg = (let _135_657 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (varg), _135_657))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(
# 950 "FStar.Tc.Tc.fst"
let _46_1759 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_659 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _135_658 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _135_659 _135_658)))
end else begin
()
end
in (
# 951 "FStar.Tc.Tc.fst"
let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 952 "FStar.Tc.Tc.fst"
let _46_1762 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (
# 953 "FStar.Tc.Tc.fst"
let _46_1768 = (tc_typ_check (
# 953 "FStar.Tc.Tc.fst"
let _46_1764 = env
in {FStar_Tc_Env.solver = _46_1764.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_1764.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_1764.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_1764.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_1764.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_1764.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_1764.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_1764.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_1764.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_1764.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_1764.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_1764.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_1764.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_1764.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_1764.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_1764.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _46_1764.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_1764.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_1764.FStar_Tc_Env.default_effects}) t k)
in (match (_46_1768) with
| (t, g') -> begin
(
# 954 "FStar.Tc.Tc.fst"
let f = (let _135_660 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _135_660))
in (
# 955 "FStar.Tc.Tc.fst"
let g' = (
# 955 "FStar.Tc.Tc.fst"
let _46_1770 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _46_1770.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _46_1770.FStar_Tc_Rel.implicits})
in (
# 956 "FStar.Tc.Tc.fst"
let arg = (FStar_Util.Inl (t), aq)
in (
# 957 "FStar.Tc.Tc.fst"
let subst = (let _135_661 = (FStar_List.hd bs)
in (maybe_extend_subst subst _135_661 arg))
in (let _135_663 = (let _135_662 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _135_662, fvs))
in (tc_args _135_663 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(
# 961 "FStar.Tc.Tc.fst"
let _46_1788 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_665 = (FStar_Absyn_Print.subst_to_string subst)
in (let _135_664 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _135_665 _135_664)))
end else begin
()
end
in (
# 962 "FStar.Tc.Tc.fst"
let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 963 "FStar.Tc.Tc.fst"
let _46_1791 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_666 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _135_666))
end else begin
()
end
in (
# 964 "FStar.Tc.Tc.fst"
let _46_1793 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (
# 965 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_expected_typ env targ)
in (
# 966 "FStar.Tc.Tc.fst"
let env = (
# 966 "FStar.Tc.Tc.fst"
let _46_1796 = env
in {FStar_Tc_Env.solver = _46_1796.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_1796.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_1796.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_1796.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_1796.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_1796.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_1796.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_1796.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_1796.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_1796.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_1796.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_1796.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_1796.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_1796.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_1796.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_1796.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _46_1796.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_1796.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_1796.FStar_Tc_Env.default_effects})
in (
# 967 "FStar.Tc.Tc.fst"
let _46_1799 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _135_668 = (FStar_Absyn_Print.exp_to_string e)
in (let _135_667 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _135_668 _135_667)))
end else begin
()
end
in (
# 968 "FStar.Tc.Tc.fst"
let _46_1801 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_671 = (FStar_Absyn_Print.tag_of_exp e)
in (let _135_670 = (FStar_Absyn_Print.exp_to_string e)
in (let _135_669 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _135_671 _135_670 _135_669))))
end else begin
()
end
in (
# 969 "FStar.Tc.Tc.fst"
let _46_1806 = (tc_exp env e)
in (match (_46_1806) with
| (e, c, g_e) -> begin
(
# 970 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g g_e)
in (
# 971 "FStar.Tc.Tc.fst"
let _46_1808 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_673 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _135_672 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _135_673 _135_672)))
end else begin
()
end
in (
# 972 "FStar.Tc.Tc.fst"
let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(
# 974 "FStar.Tc.Tc.fst"
let subst = (let _135_674 = (FStar_List.hd bs)
in (maybe_extend_subst subst _135_674 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(
# 977 "FStar.Tc.Tc.fst"
let subst = (let _135_675 = (FStar_List.hd bs)
in (maybe_extend_subst subst _135_675 arg))
in (
# 978 "FStar.Tc.Tc.fst"
let _46_1815 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_46_1815) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _135_676 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _135_676)) then begin
(
# 982 "FStar.Tc.Tc.fst"
let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (
# 983 "FStar.Tc.Tc.fst"
let arg' = (let _135_677 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _135_677))
in (
# 984 "FStar.Tc.Tc.fst"
let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _135_686 = (let _135_685 = (let _135_679 = (let _135_678 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _135_678))
in (_135_679)::arg_rets)
in (let _135_684 = (let _135_682 = (let _135_681 = (FStar_All.pipe_left (fun _135_680 -> Some (_135_680)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_135_681, c))
in (_135_682)::comps)
in (let _135_683 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _135_685, _135_684, g, _135_683))))
in (tc_args _135_686 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_46_1822), _46_1825)::_46_1820, (FStar_Util.Inl (_46_1831), _46_1834)::_46_1829) -> begin
(let _135_690 = (let _135_689 = (let _135_688 = (let _135_687 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _135_687))
in ("Expected an expression; got a type", _135_688))
in FStar_Absyn_Syntax.Error (_135_689))
in (Prims.raise _135_690))
end
| ((FStar_Util.Inl (_46_1841), _46_1844)::_46_1839, (FStar_Util.Inr (_46_1850), _46_1853)::_46_1848) -> begin
(let _135_694 = (let _135_693 = (let _135_692 = (let _135_691 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _135_691))
in ("Expected a type; got an expression", _135_692))
in FStar_Absyn_Syntax.Error (_135_693))
in (Prims.raise _135_694))
end
| (_46_1858, []) -> begin
(
# 995 "FStar.Tc.Tc.fst"
let _46_1861 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (
# 996 "FStar.Tc.Tc.fst"
let _46_1879 = (match (bs) with
| [] -> begin
(
# 998 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (
# 1004 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g_head g)
in (
# 1006 "FStar.Tc.Tc.fst"
let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _46_1869 -> (match (_46_1869) with
| (_46_1867, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (
# 1012 "FStar.Tc.Tc.fst"
let cres = if refine_with_equality then begin
(let _135_696 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _135_696 cres))
end else begin
(
# 1015 "FStar.Tc.Tc.fst"
let _46_1871 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_699 = (FStar_Absyn_Print.exp_to_string head)
in (let _135_698 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _135_697 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _135_699 _135_698 _135_697))))
end else begin
()
end
in cres)
end
in (let _135_700 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_135_700, g))))))
end
| _46_1875 -> begin
(
# 1023 "FStar.Tc.Tc.fst"
let g = (let _135_701 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _135_701 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _135_707 = (let _135_706 = (let _135_705 = (let _135_704 = (let _135_703 = (let _135_702 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _135_702))
in (FStar_Absyn_Syntax.mk_Typ_fun _135_703 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _135_704))
in (FStar_Absyn_Syntax.mk_Total _135_705))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _135_706))
in (_135_707, g)))
end)
in (match (_46_1879) with
| (cres, g) -> begin
(
# 1026 "FStar.Tc.Tc.fst"
let _46_1880 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_708 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _135_708))
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
let _46_1889 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_46_1889) with
| (comp, g) -> begin
(
# 1031 "FStar.Tc.Tc.fst"
let _46_1890 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_714 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _135_713 = (let _135_712 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _135_712))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _135_714 _135_713)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_46_1894) -> begin
(
# 1036 "FStar.Tc.Tc.fst"
let rec aux = (fun norm tres -> (
# 1037 "FStar.Tc.Tc.fst"
let tres = (let _135_719 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _135_719 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(
# 1040 "FStar.Tc.Tc.fst"
let _46_1906 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_720 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _135_720))
end else begin
()
end
in (let _135_721 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _135_721 args)))
end
| _46_1909 when (not (norm)) -> begin
(let _135_722 = (whnf env tres)
in (aux true _135_722))
end
| _46_1911 -> begin
(let _135_728 = (let _135_727 = (let _135_726 = (let _135_724 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _135_723 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _135_724 _135_723)))
in (let _135_725 = (FStar_Absyn_Syntax.argpos arg)
in (_135_726, _135_725)))
in FStar_Absyn_Syntax.Error (_135_727))
in (Prims.raise _135_728))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _135_729 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _135_729 args))))
end
| _46_1913 -> begin
if (not (norm)) then begin
(let _135_730 = (whnf env tf)
in (check_function_app true _135_730))
end else begin
(let _135_733 = (let _135_732 = (let _135_731 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_135_731, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_732))
in (Prims.raise _135_733))
end
end))
in (let _135_734 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _135_734)))))
end))
end))
in (
# 1055 "FStar.Tc.Tc.fst"
let _46_1917 = (aux ())
in (match (_46_1917) with
| (e, c, g) -> begin
(
# 1056 "FStar.Tc.Tc.fst"
let _46_1918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _135_735 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _135_735))
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
let _46_1925 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_740 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _135_739 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _135_738 = (let _135_737 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _135_737 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _135_740 _135_739 _135_738))))
end else begin
()
end
in (
# 1067 "FStar.Tc.Tc.fst"
let _46_1930 = (comp_check_expected_typ env0 e c)
in (match (_46_1930) with
| (e, c, g') -> begin
(let _135_741 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _135_741))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(
# 1071 "FStar.Tc.Tc.fst"
let _46_1937 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_46_1937) with
| (env1, topt) -> begin
(
# 1072 "FStar.Tc.Tc.fst"
let env1 = (instantiate_both env1)
in (
# 1073 "FStar.Tc.Tc.fst"
let _46_1942 = (tc_exp env1 e1)
in (match (_46_1942) with
| (e1, c1, g1) -> begin
(
# 1074 "FStar.Tc.Tc.fst"
let _46_1949 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(
# 1077 "FStar.Tc.Tc.fst"
let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _135_742 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_135_742, res_t)))
end)
in (match (_46_1949) with
| (env_branches, res_t) -> begin
(
# 1079 "FStar.Tc.Tc.fst"
let guard_x = (let _135_744 = (FStar_All.pipe_left (fun _135_743 -> Some (_135_743)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _135_744))
in (
# 1080 "FStar.Tc.Tc.fst"
let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (
# 1081 "FStar.Tc.Tc.fst"
let _46_1966 = (
# 1082 "FStar.Tc.Tc.fst"
let _46_1963 = (FStar_List.fold_right (fun _46_1957 _46_1960 -> (match ((_46_1957, _46_1960)) with
| ((_46_1953, f, c, g), (caccum, gaccum)) -> begin
(let _135_747 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _135_747))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_46_1963) with
| (cases, g) -> begin
(let _135_748 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_135_748, g))
end))
in (match (_46_1966) with
| (c_branches, g_branches) -> begin
(
# 1085 "FStar.Tc.Tc.fst"
let _46_1967 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_752 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _135_751 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _135_750 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _135_749 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _135_752 _135_751 _135_750 _135_749)))))
end else begin
()
end
in (
# 1088 "FStar.Tc.Tc.fst"
let cres = (let _135_755 = (let _135_754 = (FStar_All.pipe_left (fun _135_753 -> Some (_135_753)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_135_754, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _135_755))
in (
# 1090 "FStar.Tc.Tc.fst"
let e = (let _135_762 = (w cres)
in (let _135_761 = (let _135_760 = (let _135_759 = (FStar_List.map (fun _46_1977 -> (match (_46_1977) with
| (f, _46_1972, _46_1974, _46_1976) -> begin
f
end)) t_eqns)
in (e1, _135_759))
in (FStar_Absyn_Syntax.mk_Exp_match _135_760))
in (FStar_All.pipe_left _135_762 _135_761)))
in (let _135_764 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _135_763 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_135_764, cres, _135_763))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _46_1982; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
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
| FStar_Util.Inr (_46_1995) -> begin
true
end
| _46_1998 -> begin
false
end)
in (
# 1099 "FStar.Tc.Tc.fst"
let _46_2003 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_46_2003) with
| (env1, _46_2002) -> begin
(
# 1100 "FStar.Tc.Tc.fst"
let _46_2016 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _46_2006 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _135_765 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _135_765))
end else begin
(
# 1106 "FStar.Tc.Tc.fst"
let _46_2009 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_46_2009) with
| (t, f) -> begin
(
# 1107 "FStar.Tc.Tc.fst"
let _46_2010 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _135_767 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _135_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _135_767 _135_766)))
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
in (match (_46_2016) with
| (f, env1) -> begin
(
# 1112 "FStar.Tc.Tc.fst"
let _46_2022 = (tc_exp (
# 1112 "FStar.Tc.Tc.fst"
let _46_2017 = env1
in {FStar_Tc_Env.solver = _46_2017.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_2017.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_2017.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_2017.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_2017.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_2017.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_2017.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_2017.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_2017.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_2017.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_2017.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_2017.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_2017.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_2017.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _46_2017.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_2017.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_2017.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_2017.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_2017.FStar_Tc_Env.default_effects}) e1)
in (match (_46_2022) with
| (e1, c1, g1) -> begin
(
# 1113 "FStar.Tc.Tc.fst"
let _46_2026 = (let _135_771 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _46_2023 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _135_771 e1 c1 f))
in (match (_46_2026) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_46_2028) -> begin
(
# 1116 "FStar.Tc.Tc.fst"
let _46_2042 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(
# 1118 "FStar.Tc.Tc.fst"
let _46_2032 = (let _135_772 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _135_772 c1))
in (match (_46_2032) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(
# 1121 "FStar.Tc.Tc.fst"
let _46_2033 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _135_773 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _135_773 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _135_774 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_135_774, c1)))
end
end))
end else begin
(
# 1124 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (
# 1125 "FStar.Tc.Tc.fst"
let _46_2036 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1126 "FStar.Tc.Tc.fst"
let _46_2038 = (FStar_Tc_Util.check_unresolved_implicits g)
in (let _135_775 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _135_775)))))
end
in (match (_46_2042) with
| (e2, c1) -> begin
(
# 1128 "FStar.Tc.Tc.fst"
let _46_2047 = if env.FStar_Tc_Env.generalize then begin
(let _135_776 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _135_776))
end else begin
(x, e1, c1)
end
in (match (_46_2047) with
| (_46_2044, e1, c1) -> begin
(
# 1131 "FStar.Tc.Tc.fst"
let cres = (let _135_777 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _135_777))
in (
# 1132 "FStar.Tc.Tc.fst"
let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _135_778 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _135_778 (None, cres)))
end
in (
# 1135 "FStar.Tc.Tc.fst"
let _46_2050 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _135_787 = (let _135_786 = (w cres)
in (let _135_785 = (let _135_784 = (let _135_783 = (let _135_782 = (let _135_781 = (FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1))
in (_135_781)::[])
in (false, _135_782))
in (_135_783, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _135_784))
in (FStar_All.pipe_left _135_786 _135_785)))
in (_135_787, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(
# 1139 "FStar.Tc.Tc.fst"
let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (
# 1140 "FStar.Tc.Tc.fst"
let _46_2058 = (let _135_788 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _135_788 e2))
in (match (_46_2058) with
| (e2, c2, g2) -> begin
(
# 1141 "FStar.Tc.Tc.fst"
let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (
# 1142 "FStar.Tc.Tc.fst"
let e = (let _135_796 = (w cres)
in (let _135_795 = (let _135_794 = (let _135_793 = (let _135_792 = (let _135_791 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1))
in (_135_791)::[])
in (false, _135_792))
in (_135_793, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _135_794))
in (FStar_All.pipe_left _135_796 _135_795)))
in (
# 1143 "FStar.Tc.Tc.fst"
let g2 = (let _135_805 = (let _135_798 = (let _135_797 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_135_797)::[])
in (FStar_Tc_Rel.close_guard _135_798))
in (let _135_804 = (let _135_803 = (let _135_802 = (let _135_801 = (let _135_800 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _135_800 e1))
in (FStar_All.pipe_left (fun _135_799 -> FStar_Tc_Rel.NonTrivial (_135_799)) _135_801))
in (FStar_Tc_Rel.guard_of_guard_formula _135_802))
in (FStar_Tc_Rel.imp_guard _135_803 g2))
in (FStar_All.pipe_left _135_805 _135_804)))
in (
# 1145 "FStar.Tc.Tc.fst"
let guard = (let _135_806 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _135_806))
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
let _46_2067 = (let _135_807 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _135_807))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _46_2070 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _46_2073), _46_2076) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(
# 1162 "FStar.Tc.Tc.fst"
let env = (instantiate_both env)
in (
# 1163 "FStar.Tc.Tc.fst"
let _46_2088 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_46_2088) with
| (env0, topt) -> begin
(
# 1164 "FStar.Tc.Tc.fst"
let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _46_9 -> (match (_46_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_46_2097); FStar_Absyn_Syntax.lbtyp = _46_2095; FStar_Absyn_Syntax.lbeff = _46_2093; FStar_Absyn_Syntax.lbdef = _46_2091} -> begin
true
end
| _46_2101 -> begin
false
end))))
in (
# 1166 "FStar.Tc.Tc.fst"
let _46_2126 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _46_2105 _46_2111 -> (match ((_46_2105, _46_2111)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _46_2108; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 1167 "FStar.Tc.Tc.fst"
let _46_2116 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_46_2116) with
| (_46_2113, t, check_t) -> begin
(
# 1169 "FStar.Tc.Tc.fst"
let e = (FStar_Absyn_Util.unascribe e)
in (
# 1170 "FStar.Tc.Tc.fst"
let t = if (not (check_t)) then begin
t
end else begin
(let _135_811 = (tc_typ_check_trivial (
# 1183 "FStar.Tc.Tc.fst"
let _46_2118 = env0
in {FStar_Tc_Env.solver = _46_2118.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_2118.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_2118.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_2118.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_2118.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_2118.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_2118.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_2118.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_2118.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_2118.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_2118.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_2118.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_2118.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_2118.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_2118.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _46_2118.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_2118.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_2118.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_2118.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _135_811 (norm_t env)))
end
in (
# 1184 "FStar.Tc.Tc.fst"
let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(
# 1186 "FStar.Tc.Tc.fst"
let _46_2121 = env
in {FStar_Tc_Env.solver = _46_2121.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_2121.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_2121.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_2121.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_2121.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_2121.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_2121.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_2121.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_2121.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_2121.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_2121.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_2121.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_2121.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_2121.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_2121.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_2121.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_2121.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_2121.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_2121.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_46_2126) with
| (lbs, env') -> begin
(
# 1191 "FStar.Tc.Tc.fst"
let _46_2141 = (let _135_817 = (let _135_816 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _135_816 (FStar_List.map (fun _46_2130 -> (match (_46_2130) with
| (x, t, e) -> begin
(
# 1192 "FStar.Tc.Tc.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (
# 1193 "FStar.Tc.Tc.fst"
let _46_2132 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_815 = (FStar_Absyn_Print.lbname_to_string x)
in (let _135_814 = (FStar_Absyn_Print.exp_to_string e)
in (let _135_813 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _135_815 _135_814 _135_813))))
end else begin
()
end
in (
# 1195 "FStar.Tc.Tc.fst"
let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (
# 1196 "FStar.Tc.Tc.fst"
let _46_2138 = (tc_total_exp env' e)
in (match (_46_2138) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _135_817 FStar_List.unzip))
in (match (_46_2141) with
| (lbs, gs) -> begin
(
# 1199 "FStar.Tc.Tc.fst"
let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (
# 1201 "FStar.Tc.Tc.fst"
let _46_2160 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _135_819 = (FStar_List.map (fun _46_2146 -> (match (_46_2146) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_135_819, g_lbs))
end else begin
(
# 1205 "FStar.Tc.Tc.fst"
let _46_2147 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (
# 1206 "FStar.Tc.Tc.fst"
let ecs = (let _135_822 = (FStar_All.pipe_right lbs (FStar_List.map (fun _46_2152 -> (match (_46_2152) with
| (x, t, e) -> begin
(let _135_821 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb (x, t, e)))
in (x, e, _135_821))
end))))
in (FStar_Tc_Util.generalize true env _135_822))
in (let _135_824 = (FStar_List.map (fun _46_2157 -> (match (_46_2157) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_135_824, FStar_Tc_Rel.trivial_guard))))
end
in (match (_46_2160) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(
# 1211 "FStar.Tc.Tc.fst"
let cres = (let _135_825 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _135_825))
in (
# 1212 "FStar.Tc.Tc.fst"
let _46_2162 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (
# 1213 "FStar.Tc.Tc.fst"
let _46_2164 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _135_829 = (let _135_828 = (w cres)
in (FStar_All.pipe_left _135_828 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_135_829, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(
# 1215 "FStar.Tc.Tc.fst"
let _46_2180 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _46_2168 _46_2175 -> (match ((_46_2168, _46_2175)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _46_2172; FStar_Absyn_Syntax.lbdef = _46_2170}) -> begin
(
# 1216 "FStar.Tc.Tc.fst"
let b = (binding_of_lb x t)
in (
# 1217 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_46_2180) with
| (bindings, env) -> begin
(
# 1219 "FStar.Tc.Tc.fst"
let _46_2184 = (tc_exp env e1)
in (match (_46_2184) with
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
let _46_2188 = cres
in {FStar_Absyn_Syntax.eff_name = _46_2188.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _46_2188.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _46_2188.FStar_Absyn_Syntax.comp})
in (
# 1225 "FStar.Tc.Tc.fst"
let e = (let _135_834 = (w cres)
in (FStar_All.pipe_left _135_834 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_46_2193) -> begin
(e, cres, guard)
end
| None -> begin
(
# 1229 "FStar.Tc.Tc.fst"
let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _46_10 -> (match (_46_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_46_2205); FStar_Absyn_Syntax.lbtyp = _46_2203; FStar_Absyn_Syntax.lbeff = _46_2201; FStar_Absyn_Syntax.lbdef = _46_2199} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _46_2213; FStar_Absyn_Syntax.lbeff = _46_2211; FStar_Absyn_Syntax.lbdef = _46_2209} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _46_2222; FStar_Absyn_Syntax.lbeff = _46_2220; FStar_Absyn_Syntax.lbdef = _46_2218}) -> begin
(
# 1234 "FStar.Tc.Tc.fst"
let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (
# 1235 "FStar.Tc.Tc.fst"
let _46_2228 = (let _135_836 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _135_836))
in (e, cres, guard)))
end
| _46_2231 -> begin
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
and tc_eqn : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp)  ->  ((FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun scrutinee_x pat_t env _46_2238 -> (match (_46_2238) with
| (pattern, when_clause, branch) -> begin
(
# 1249 "FStar.Tc.Tc.fst"
let tc_pat = (fun allow_implicits pat_t p0 -> (
# 1250 "FStar.Tc.Tc.fst"
let _46_2246 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_46_2246) with
| (bindings, exps, p) -> begin
(
# 1251 "FStar.Tc.Tc.fst"
let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (
# 1252 "FStar.Tc.Tc.fst"
let _46_2255 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _46_11 -> (match (_46_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _135_849 = (FStar_Absyn_Print.strBvd x)
in (let _135_848 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _135_849 _135_848)))
end
| _46_2254 -> begin
()
end))))
end else begin
()
end
in (
# 1256 "FStar.Tc.Tc.fst"
let _46_2260 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_46_2260) with
| (env1, _46_2259) -> begin
(
# 1257 "FStar.Tc.Tc.fst"
let env1 = (
# 1257 "FStar.Tc.Tc.fst"
let _46_2261 = env1
in {FStar_Tc_Env.solver = _46_2261.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_2261.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_2261.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_2261.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_2261.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_2261.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_2261.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_2261.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _46_2261.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_2261.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_2261.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_2261.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_2261.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_2261.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_2261.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_2261.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_2261.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_2261.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_2261.FStar_Tc_Env.default_effects})
in (
# 1258 "FStar.Tc.Tc.fst"
let expected_pat_t = (let _135_850 = (FStar_Tc_Rel.unrefine env pat_t)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env _135_850))
in (
# 1259 "FStar.Tc.Tc.fst"
let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (
# 1260 "FStar.Tc.Tc.fst"
let _46_2266 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_853 = (FStar_Absyn_Print.exp_to_string e)
in (let _135_852 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _135_853 _135_852)))
end else begin
()
end
in (
# 1262 "FStar.Tc.Tc.fst"
let _46_2271 = (tc_exp env1 e)
in (match (_46_2271) with
| (e, lc, g) -> begin
(
# 1263 "FStar.Tc.Tc.fst"
let _46_2272 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_855 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _135_854 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _135_855 _135_854)))
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
let _46_2276 = (let _135_856 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _135_856))
in (
# 1268 "FStar.Tc.Tc.fst"
let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (
# 1269 "FStar.Tc.Tc.fst"
let _46_2279 = if (let _135_859 = (let _135_858 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _135_857 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _135_858 _135_857)))
in (FStar_All.pipe_left Prims.op_Negation _135_859)) then begin
(let _135_864 = (let _135_863 = (let _135_862 = (let _135_861 = (FStar_Absyn_Print.exp_to_string e')
in (let _135_860 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _135_861 _135_860)))
in (_135_862, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_135_863))
in (Prims.raise _135_864))
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
let _46_2290 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _46_12 -> (match (_46_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _135_867 = (FStar_Absyn_Print.strBvd x)
in (let _135_866 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _135_867 _135_866)))
end
| _46_2289 -> begin
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
let _46_2297 = (tc_pat true pat_t pattern)
in (match (_46_2297) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(
# 1282 "FStar.Tc.Tc.fst"
let _46_2307 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(
# 1289 "FStar.Tc.Tc.fst"
let _46_2304 = (let _135_868 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _135_868 e))
in (match (_46_2304) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_46_2307) with
| (when_clause, g_when) -> begin
(
# 1291 "FStar.Tc.Tc.fst"
let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _135_870 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _135_869 -> Some (_135_869)) _135_870))
end)
in (
# 1294 "FStar.Tc.Tc.fst"
let _46_2315 = (tc_exp pat_env branch)
in (match (_46_2315) with
| (branch, c, g_branch) -> begin
(
# 1295 "FStar.Tc.Tc.fst"
let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (
# 1296 "FStar.Tc.Tc.fst"
let _46_2320 = (let _135_871 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _135_871 FStar_Tc_Env.clear_expected_typ))
in (match (_46_2320) with
| (scrutinee_env, _46_2319) -> begin
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
| _46_2334 -> begin
(
# 1305 "FStar.Tc.Tc.fst"
let clause = (let _135_875 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _135_874 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _135_875 _135_874 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _135_877 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _135_876 -> Some (_135_876)) _135_877))
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
(let _135_880 = (let _135_879 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _135_878 -> FStar_Tc_Rel.NonTrivial (_135_878)) _135_879))
in (FStar_Tc_Util.weaken_precondition env c _135_880))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (
# 1316 "FStar.Tc.Tc.fst"
let discriminate = (fun scrutinee f -> (
# 1317 "FStar.Tc.Tc.fst"
let disc = (let _135_886 = (let _135_885 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _135_885))
in (FStar_All.pipe_left _135_886 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (
# 1318 "FStar.Tc.Tc.fst"
let disc = (let _135_889 = (let _135_888 = (let _135_887 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_135_887)::[])
in (disc, _135_888))
in (FStar_Absyn_Syntax.mk_Exp_app _135_889 None scrutinee.FStar_Absyn_Syntax.pos))
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
| FStar_Absyn_Syntax.Exp_constant (_46_2392) -> begin
(let _135_898 = (let _135_897 = (let _135_896 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _135_895 = (let _135_894 = (FStar_Absyn_Syntax.varg pat_exp)
in (_135_894)::[])
in (_135_896)::_135_895))
in (FStar_Absyn_Util.teq, _135_897))
in (FStar_Absyn_Syntax.mk_Typ_app _135_898 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _46_2396) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _46_2409); FStar_Absyn_Syntax.tk = _46_2406; FStar_Absyn_Syntax.pos = _46_2404; FStar_Absyn_Syntax.fvs = _46_2402; FStar_Absyn_Syntax.uvs = _46_2400}, args) -> begin
(
# 1331 "FStar.Tc.Tc.fst"
let head = (discriminate scrutinee f)
in (
# 1332 "FStar.Tc.Tc.fst"
let sub_term_guards = (let _135_907 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_46_2420) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(
# 1335 "FStar.Tc.Tc.fst"
let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in if (let _135_901 = (FStar_Tc_Env.is_projector env projector)
in (FStar_All.pipe_left Prims.op_Negation _135_901)) then begin
[]
end else begin
(
# 1338 "FStar.Tc.Tc.fst"
let sub_term = (let _135_905 = (let _135_904 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _135_903 = (let _135_902 = (FStar_Absyn_Syntax.varg scrutinee)
in (_135_902)::[])
in (_135_904, _135_903)))
in (FStar_Absyn_Syntax.mk_Exp_app _135_905 None f.FStar_Absyn_Syntax.p))
in (let _135_906 = (mk_guard sub_term ei)
in (_135_906)::[]))
end)
end))))
in (FStar_All.pipe_right _135_907 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _46_2428 -> begin
(let _135_910 = (let _135_909 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _135_908 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _135_909 _135_908)))
in (FStar_All.failwith _135_910))
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
let _46_2437 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_46_2437) with
| (t, _46_2436) -> begin
t
end)))
end)
in (
# 1348 "FStar.Tc.Tc.fst"
let path_guard = (let _135_919 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _135_918 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _135_918)))))
in (FStar_All.pipe_right _135_919 FStar_Absyn_Util.mk_disj_l))
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
let guard = (let _135_920 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _135_920))
in (
# 1353 "FStar.Tc.Tc.fst"
let _46_2445 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _135_921 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _135_921))
end else begin
()
end
in (let _135_923 = (let _135_922 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _135_922))
in ((pattern, when_clause, branch), path_guard, c, _135_923))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1358 "FStar.Tc.Tc.fst"
let _46_2451 = (tc_kind env k)
in (match (_46_2451) with
| (k, g) -> begin
(
# 1359 "FStar.Tc.Tc.fst"
let _46_2452 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd) = (fun env t -> (
# 1363 "FStar.Tc.Tc.fst"
let _46_2459 = (tc_typ env t)
in (match (_46_2459) with
| (t, k, g) -> begin
(
# 1364 "FStar.Tc.Tc.fst"
let _46_2460 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env t k -> (
# 1368 "FStar.Tc.Tc.fst"
let _46_2467 = (tc_typ_check env t k)
in (match (_46_2467) with
| (t, f) -> begin
(
# 1369 "FStar.Tc.Tc.fst"
let _46_2468 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 1373 "FStar.Tc.Tc.fst"
let _46_2475 = (tc_exp env e)
in (match (_46_2475) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(
# 1376 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (
# 1377 "FStar.Tc.Tc.fst"
let c = (let _135_933 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _135_933 (norm_c env)))
in (match ((let _135_935 = (let _135_934 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _135_934))
in (FStar_Tc_Rel.sub_comp env c _135_935))) with
| Some (g') -> begin
(let _135_936 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _135_936))
end
| _46_2481 -> begin
(let _135_939 = (let _135_938 = (let _135_937 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_135_937, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_938))
in (Prims.raise _135_939))
end)))
end
end)))
and tc_ghost_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (
# 1383 "FStar.Tc.Tc.fst"
let _46_2487 = (tc_exp env e)
in (match (_46_2487) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(
# 1386 "FStar.Tc.Tc.fst"
let c = (let _135_942 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _135_942 (norm_c env)))
in (
# 1387 "FStar.Tc.Tc.fst"
let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (
# 1388 "FStar.Tc.Tc.fst"
let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (
# 1389 "FStar.Tc.Tc.fst"
let _46_2491 = env
in {FStar_Tc_Env.solver = _46_2491.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_2491.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_2491.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_2491.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_2491.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_2491.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_2491.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_2491.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_2491.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_2491.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_2491.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_2491.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_2491.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_2491.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_2491.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_2491.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _46_2491.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_2491.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_2491.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _135_943 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _135_943))
end
| _46_2496 -> begin
(let _135_946 = (let _135_945 = (let _135_944 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_135_944, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_135_945))
in (Prims.raise _135_946))
end))))
end
end)))

# 1395 "FStar.Tc.Tc.fst"
let tc_tparams : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env) = (fun env tps -> (
# 1396 "FStar.Tc.Tc.fst"
let _46_2502 = (tc_binders env tps)
in (match (_46_2502) with
| (tps, env, g) -> begin
(
# 1397 "FStar.Tc.Tc.fst"
let _46_2503 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

# 1400 "FStar.Tc.Tc.fst"
let a_kwp_a : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _46_2522)::(FStar_Util.Inl (wp), _46_2517)::(FStar_Util.Inl (_46_2509), _46_2512)::[], _46_2526) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _46_2530 -> begin
(let _135_959 = (let _135_958 = (let _135_957 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (_135_957, (FStar_Ident.range_of_lid m)))
in FStar_Absyn_Syntax.Error (_135_958))
in (Prims.raise _135_959))
end))

# 1406 "FStar.Tc.Tc.fst"
let rec tc_eff_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.eff_decl = (fun env m -> (
# 1407 "FStar.Tc.Tc.fst"
let _46_2536 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_46_2536) with
| (binders, env, g) -> begin
(
# 1408 "FStar.Tc.Tc.fst"
let _46_2537 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1409 "FStar.Tc.Tc.fst"
let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (
# 1410 "FStar.Tc.Tc.fst"
let _46_2542 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_46_2542) with
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
let a_kwp_b = (let _135_972 = (let _135_971 = (let _135_970 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_135_970)::[])
in (_135_971, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_972 a_typ.FStar_Absyn_Syntax.pos))
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
let expected_k = (let _135_986 = (let _135_985 = (let _135_984 = (let _135_983 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_982 = (let _135_981 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_135_981)::[])
in (_135_983)::_135_982))
in (_135_984, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_985))
in (FStar_All.pipe_left w _135_986))
in (let _135_987 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _135_987 (norm_t env))))
in (
# 1423 "FStar.Tc.Tc.fst"
let bind_wp = (
# 1424 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1002 = (let _135_1001 = (let _135_1000 = (let _135_999 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_998 = (let _135_997 = (FStar_Absyn_Syntax.t_binder b)
in (let _135_996 = (let _135_995 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _135_994 = (let _135_993 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _135_992 = (let _135_991 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _135_990 = (let _135_989 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_135_989)::[])
in (_135_991)::_135_990))
in (_135_993)::_135_992))
in (_135_995)::_135_994))
in (_135_997)::_135_996))
in (_135_999)::_135_998))
in (_135_1000, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1001))
in (FStar_All.pipe_left w _135_1002))
in (let _135_1003 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _135_1003 (norm_t env))))
in (
# 1429 "FStar.Tc.Tc.fst"
let bind_wlp = (
# 1430 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1014 = (let _135_1013 = (let _135_1012 = (let _135_1011 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1010 = (let _135_1009 = (FStar_Absyn_Syntax.t_binder b)
in (let _135_1008 = (let _135_1007 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _135_1006 = (let _135_1005 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_135_1005)::[])
in (_135_1007)::_135_1006))
in (_135_1009)::_135_1008))
in (_135_1011)::_135_1010))
in (_135_1012, kwlp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1013))
in (FStar_All.pipe_left w _135_1014))
in (let _135_1015 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _135_1015 (norm_t env))))
in (
# 1435 "FStar.Tc.Tc.fst"
let if_then_else = (
# 1436 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1026 = (let _135_1025 = (let _135_1024 = (let _135_1023 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1022 = (let _135_1021 = (FStar_Absyn_Syntax.t_binder b)
in (let _135_1020 = (let _135_1019 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _135_1018 = (let _135_1017 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_135_1017)::[])
in (_135_1019)::_135_1018))
in (_135_1021)::_135_1020))
in (_135_1023)::_135_1022))
in (_135_1024, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1025))
in (FStar_All.pipe_left w _135_1026))
in (let _135_1027 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _135_1027 (norm_t env))))
in (
# 1441 "FStar.Tc.Tc.fst"
let ite_wp = (
# 1442 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1036 = (let _135_1035 = (let _135_1034 = (let _135_1033 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1032 = (let _135_1031 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _135_1030 = (let _135_1029 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_135_1029)::[])
in (_135_1031)::_135_1030))
in (_135_1033)::_135_1032))
in (_135_1034, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1035))
in (FStar_All.pipe_left w _135_1036))
in (let _135_1037 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _135_1037 (norm_t env))))
in (
# 1447 "FStar.Tc.Tc.fst"
let ite_wlp = (
# 1448 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1044 = (let _135_1043 = (let _135_1042 = (let _135_1041 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1040 = (let _135_1039 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_135_1039)::[])
in (_135_1041)::_135_1040))
in (_135_1042, kwlp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1043))
in (FStar_All.pipe_left w _135_1044))
in (let _135_1045 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _135_1045 (norm_t env))))
in (
# 1452 "FStar.Tc.Tc.fst"
let wp_binop = (
# 1453 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1057 = (let _135_1056 = (let _135_1055 = (let _135_1054 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1053 = (let _135_1052 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _135_1051 = (let _135_1050 = (let _135_1047 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _135_1047))
in (let _135_1049 = (let _135_1048 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_135_1048)::[])
in (_135_1050)::_135_1049))
in (_135_1052)::_135_1051))
in (_135_1054)::_135_1053))
in (_135_1055, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1056))
in (FStar_All.pipe_left w _135_1057))
in (let _135_1058 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _135_1058 (norm_t env))))
in (
# 1459 "FStar.Tc.Tc.fst"
let wp_as_type = (
# 1460 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1065 = (let _135_1064 = (let _135_1063 = (let _135_1062 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1061 = (let _135_1060 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_135_1060)::[])
in (_135_1062)::_135_1061))
in (_135_1063, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1064))
in (FStar_All.pipe_left w _135_1065))
in (let _135_1066 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _135_1066 (norm_t env))))
in (
# 1464 "FStar.Tc.Tc.fst"
let close_wp = (
# 1465 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1075 = (let _135_1074 = (let _135_1073 = (let _135_1072 = (FStar_Absyn_Syntax.t_binder b)
in (let _135_1071 = (let _135_1070 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1069 = (let _135_1068 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_135_1068)::[])
in (_135_1070)::_135_1069))
in (_135_1072)::_135_1071))
in (_135_1073, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1074))
in (FStar_All.pipe_left w _135_1075))
in (let _135_1076 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _135_1076 (norm_t env))))
in (
# 1469 "FStar.Tc.Tc.fst"
let close_wp_t = (
# 1470 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1089 = (let _135_1088 = (let _135_1087 = (let _135_1086 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1085 = (let _135_1084 = (let _135_1083 = (let _135_1082 = (let _135_1081 = (let _135_1080 = (let _135_1079 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_135_1079)::[])
in (_135_1080, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1081))
in (FStar_All.pipe_left w _135_1082))
in (FStar_Absyn_Syntax.null_t_binder _135_1083))
in (_135_1084)::[])
in (_135_1086)::_135_1085))
in (_135_1087, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1088))
in (FStar_All.pipe_left w _135_1089))
in (let _135_1090 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _135_1090 (norm_t env))))
in (
# 1474 "FStar.Tc.Tc.fst"
let _46_2576 = (
# 1475 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1099 = (let _135_1098 = (let _135_1097 = (let _135_1096 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1095 = (let _135_1094 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _135_1093 = (let _135_1092 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_135_1092)::[])
in (_135_1094)::_135_1093))
in (_135_1096)::_135_1095))
in (_135_1097, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1098))
in (FStar_All.pipe_left w _135_1099))
in (let _135_1103 = (let _135_1100 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _135_1100 (norm_t env)))
in (let _135_1102 = (let _135_1101 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _135_1101 (norm_t env)))
in (_135_1103, _135_1102))))
in (match (_46_2576) with
| (assert_p, assume_p) -> begin
(
# 1479 "FStar.Tc.Tc.fst"
let null_wp = (
# 1480 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1108 = (let _135_1107 = (let _135_1106 = (let _135_1105 = (FStar_Absyn_Syntax.t_binder a)
in (_135_1105)::[])
in (_135_1106, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1107))
in (FStar_All.pipe_left w _135_1108))
in (let _135_1109 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _135_1109 (norm_t env))))
in (
# 1482 "FStar.Tc.Tc.fst"
let trivial_wp = (
# 1483 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1116 = (let _135_1115 = (let _135_1114 = (let _135_1113 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1112 = (let _135_1111 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_135_1111)::[])
in (_135_1113)::_135_1112))
in (_135_1114, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1115))
in (FStar_All.pipe_left w _135_1116))
in (let _135_1117 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _135_1117 (norm_t env))))
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
let _46_2597 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Absyn_Syntax.ResetOptions (sopt) -> begin
(
# 1517 "FStar.Tc.Tc.fst"
let _46_2601 = (let _135_1125 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _135_1125 Prims.ignore))
in (
# 1518 "FStar.Tc.Tc.fst"
let _46_2606 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (
# 1521 "FStar.Tc.Tc.fst"
let _46_2608 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
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
let _46_2623 = (let _135_1126 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _135_1126))
in (match (_46_2623) with
| (a, kwp_a_src) -> begin
(
# 1533 "FStar.Tc.Tc.fst"
let _46_2626 = (let _135_1127 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _135_1127))
in (match (_46_2626) with
| (b, kwp_b_tgt) -> begin
(
# 1534 "FStar.Tc.Tc.fst"
let kwp_a_tgt = (let _135_1131 = (let _135_1130 = (let _135_1129 = (let _135_1128 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _135_1128))
in FStar_Util.Inl (_135_1129))
in (_135_1130)::[])
in (FStar_Absyn_Util.subst_kind _135_1131 kwp_b_tgt))
in (
# 1535 "FStar.Tc.Tc.fst"
let expected_k = (let _135_1137 = (let _135_1136 = (let _135_1135 = (let _135_1134 = (FStar_Absyn_Syntax.t_binder a)
in (let _135_1133 = (let _135_1132 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_135_1132)::[])
in (_135_1134)::_135_1133))
in (_135_1135, kwp_a_tgt))
in (FStar_Absyn_Syntax.mk_Kind_arrow _135_1136))
in (FStar_All.pipe_right r _135_1137))
in (
# 1536 "FStar.Tc.Tc.fst"
let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (
# 1537 "FStar.Tc.Tc.fst"
let sub = (
# 1537 "FStar.Tc.Tc.fst"
let _46_2630 = sub
in {FStar_Absyn_Syntax.source = _46_2630.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _46_2630.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
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
let _46_2647 = (tc_tparams env tps)
in (match (_46_2647) with
| (tps, env) -> begin
(
# 1545 "FStar.Tc.Tc.fst"
let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _46_2650 -> begin
(tc_kind_trivial env k)
end)
in (
# 1548 "FStar.Tc.Tc.fst"
let _46_2652 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _135_1140 = (FStar_Absyn_Print.sli lid)
in (let _135_1139 = (let _135_1138 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _135_1138))
in (FStar_Util.print2 "Checked %s at kind %s\n" _135_1140 _135_1139)))
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
let _46_2670 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_46_2665); FStar_Absyn_Syntax.tk = _46_2663; FStar_Absyn_Syntax.pos = _46_2661; FStar_Absyn_Syntax.fvs = _46_2659; FStar_Absyn_Syntax.uvs = _46_2657} -> begin
(let _135_1141 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _135_1141))
end
| _46_2669 -> begin
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
let _46_2683 = (tc_tparams env tps)
in (match (_46_2683) with
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
let _46_2698 = (tc_tparams env tps)
in (match (_46_2698) with
| (tps, env) -> begin
(
# 1570 "FStar.Tc.Tc.fst"
let _46_2701 = (tc_comp env c)
in (match (_46_2701) with
| (c, g) -> begin
(
# 1571 "FStar.Tc.Tc.fst"
let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _46_13 -> (match (_46_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(
# 1573 "FStar.Tc.Tc.fst"
let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _135_1144 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _135_1143 -> Some (_135_1143)))
in FStar_Absyn_Syntax.DefaultEffect (_135_1144)))
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
let _46_2721 = (tc_tparams env tps)
in (match (_46_2721) with
| (tps, env') -> begin
(
# 1583 "FStar.Tc.Tc.fst"
let _46_2727 = (let _135_1148 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _135_1148 (fun _46_2724 -> (match (_46_2724) with
| (t, k) -> begin
(let _135_1147 = (norm_t env' t)
in (let _135_1146 = (norm_k env' k)
in (_135_1147, _135_1146)))
end))))
in (match (_46_2727) with
| (t, k1) -> begin
(
# 1584 "FStar.Tc.Tc.fst"
let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _46_2730 -> begin
(
# 1586 "FStar.Tc.Tc.fst"
let k2 = (let _135_1149 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _135_1149 (norm_k env)))
in (
# 1587 "FStar.Tc.Tc.fst"
let _46_2732 = (let _135_1150 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _135_1150))
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
let _46_2752 = (tc_binders env tps)
in (match (_46_2752) with
| (tps, env, g) -> begin
(
# 1595 "FStar.Tc.Tc.fst"
let tycon = (tname, tps, k)
in (
# 1596 "FStar.Tc.Tc.fst"
let _46_2754 = (FStar_Tc_Util.discharge_guard env g)
in (
# 1597 "FStar.Tc.Tc.fst"
let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (
# 1598 "FStar.Tc.Tc.fst"
let t = (norm_t env t)
in (
# 1600 "FStar.Tc.Tc.fst"
let _46_2766 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _46_2763 -> begin
([], t)
end)
in (match (_46_2766) with
| (formals, result_t) -> begin
(
# 1604 "FStar.Tc.Tc.fst"
let cardinality_and_positivity_check = (fun formal -> (
# 1605 "FStar.Tc.Tc.fst"
let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _46_2774 -> (match (_46_2774) with
| (a, _46_2773) -> begin
(match (a) with
| FStar_Util.Inl (_46_2776) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(
# 1609 "FStar.Tc.Tc.fst"
let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _135_1158 = (FStar_Absyn_Util.compress_typ t)
in _135_1158.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _135_1162 = (let _135_1161 = (let _135_1160 = (let _135_1159 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _135_1159 tname))
in (_135_1160, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_135_1161))
in (Prims.raise _135_1162))
end)
end
| _46_2789 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(
# 1621 "FStar.Tc.Tc.fst"
let _46_2792 = if (FStar_Options.warn_cardinality ()) then begin
(let _135_1163 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _135_1163))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _135_1166 = (let _135_1165 = (let _135_1164 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_135_1164, r))
in FStar_Absyn_Syntax.Error (_135_1165))
in (Prims.raise _135_1166))
end else begin
()
end
end
in (
# 1627 "FStar.Tc.Tc.fst"
let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_46_2796) -> begin
(
# 1630 "FStar.Tc.Tc.fst"
let _46_2801 = (FStar_Absyn_Util.kind_formals k)
in (match (_46_2801) with
| (formals, _46_2800) -> begin
(check_positivity formals)
end))
end
| _46_2803 -> begin
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
let _46_2810 = (let _135_1167 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _135_1167 FStar_Util.must))
in (match (_46_2810) with
| (formals, _46_2809) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (
# 1641 "FStar.Tc.Tc.fst"
let _46_2811 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (
# 1643 "FStar.Tc.Tc.fst"
let _46_2865 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _135_1171 = (let _135_1170 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _135_1170 Prims.fst))
in (FStar_List.forall2 (fun _46_2818 _46_2822 -> (match ((_46_2818, _46_2822)) with
| ((a, _46_2817), (b, _46_2821)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _46_2830; FStar_Absyn_Syntax.pos = _46_2828; FStar_Absyn_Syntax.fvs = _46_2826; FStar_Absyn_Syntax.uvs = _46_2824}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _46_2845; FStar_Absyn_Syntax.pos = _46_2843; FStar_Absyn_Syntax.fvs = _46_2841; FStar_Absyn_Syntax.uvs = _46_2839}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _46_2854 -> begin
false
end)
end)) _135_1171 tps))))) then begin
(
# 1650 "FStar.Tc.Tc.fst"
let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _46_2857 -> begin
(
# 1653 "FStar.Tc.Tc.fst"
let _46_2861 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_46_2861) with
| (_46_2859, expected_args) -> begin
(let _135_1172 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _135_1172 expected_args))
end))
end)
in (let _135_1176 = (let _135_1175 = (let _135_1174 = (let _135_1173 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _135_1173 result_t expected_t))
in (_135_1174, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_135_1175))
in (Prims.raise _135_1176)))
end else begin
()
end
end
| _46_2864 -> begin
(let _135_1181 = (let _135_1180 = (let _135_1179 = (let _135_1178 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _135_1177 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _135_1178 result_t _135_1177)))
in (_135_1179, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_135_1180))
in (Prims.raise _135_1181))
end)
in (
# 1657 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (
# 1658 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (
# 1659 "FStar.Tc.Tc.fst"
let _46_2869 = if (log env) then begin
(let _135_1183 = (let _135_1182 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _135_1182))
in (FStar_All.pipe_left FStar_Util.print_string _135_1183))
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
let t = (let _135_1184 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _135_1184 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (
# 1665 "FStar.Tc.Tc.fst"
let _46_2879 = (FStar_Tc_Util.check_uvars r t)
in (
# 1666 "FStar.Tc.Tc.fst"
let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (
# 1667 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.push_sigelt env se)
in (
# 1668 "FStar.Tc.Tc.fst"
let _46_2883 = if (log env) then begin
(let _135_1186 = (let _135_1185 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _135_1185))
in (FStar_All.pipe_left FStar_Util.print_string _135_1186))
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
let phi = (let _135_1187 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _135_1187 (norm_t env)))
in (
# 1674 "FStar.Tc.Tc.fst"
let _46_2893 = (FStar_Tc_Util.check_uvars r phi)
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
let _46_2946 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _46_2906 lb -> (match (_46_2906) with
| (gen, lbs) -> begin
(
# 1683 "FStar.Tc.Tc.fst"
let _46_2943 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_46_2915); FStar_Absyn_Syntax.lbtyp = _46_2913; FStar_Absyn_Syntax.lbeff = _46_2911; FStar_Absyn_Syntax.lbdef = _46_2909} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _46_2920; FStar_Absyn_Syntax.lbdef = e} -> begin
(
# 1686 "FStar.Tc.Tc.fst"
let _46_2940 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _46_2928) -> begin
(
# 1689 "FStar.Tc.Tc.fst"
let _46_2931 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _135_1190 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _135_1190 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _135_1191 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _135_1191))
end
| _46_2935 -> begin
(
# 1695 "FStar.Tc.Tc.fst"
let _46_2936 = if (not (deserialized)) then begin
(let _135_1193 = (let _135_1192 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _135_1192))
in (FStar_All.pipe_left FStar_Util.print_string _135_1193))
end else begin
()
end
in (let _135_1194 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _135_1194)))
end))
end)
in (match (_46_2940) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_46_2943) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_46_2946) with
| (generalize, lbs') -> begin
(
# 1700 "FStar.Tc.Tc.fst"
let lbs' = (FStar_List.rev lbs')
in (
# 1701 "FStar.Tc.Tc.fst"
let e = (let _135_1199 = (let _135_1198 = (let _135_1197 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _135_1197 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((Prims.fst lbs), lbs'), _135_1198))
in (FStar_Absyn_Syntax.mk_Exp_let _135_1199 None r))
in (
# 1702 "FStar.Tc.Tc.fst"
let _46_2981 = (match ((tc_exp (
# 1702 "FStar.Tc.Tc.fst"
let _46_2949 = env
in {FStar_Tc_Env.solver = _46_2949.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_2949.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_2949.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_2949.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_2949.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_2949.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_2949.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_2949.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_2949.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_2949.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_2949.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_2949.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _46_2949.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_2949.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_2949.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_2949.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _46_2949.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _46_2949.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _46_2949.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _46_2958; FStar_Absyn_Syntax.pos = _46_2956; FStar_Absyn_Syntax.fvs = _46_2954; FStar_Absyn_Syntax.uvs = _46_2952}, _46_2965, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(
# 1704 "FStar.Tc.Tc.fst"
let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_46_2969, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _46_2975 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _46_2978 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_46_2981) with
| (se, lbs) -> begin
(
# 1709 "FStar.Tc.Tc.fst"
let _46_2987 = if (log env) then begin
(let _135_1205 = (let _135_1204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1711 "FStar.Tc.Tc.fst"
let should_log = (match ((let _135_1201 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _135_1201))) with
| None -> begin
true
end
| _46_2985 -> begin
false
end)
in if should_log then begin
(let _135_1203 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _135_1202 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _135_1203 _135_1202)))
end else begin
""
end))))
in (FStar_All.pipe_right _135_1204 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _135_1205))
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
let _46_2999 = (tc_exp env e)
in (match (_46_2999) with
| (e, c, g1) -> begin
(
# 1724 "FStar.Tc.Tc.fst"
let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (
# 1725 "FStar.Tc.Tc.fst"
let _46_3005 = (let _135_1209 = (let _135_1206 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_135_1206))
in (let _135_1208 = (let _135_1207 = (c.FStar_Absyn_Syntax.comp ())
in (e, _135_1207))
in (check_expected_effect env _135_1209 _135_1208)))
in (match (_46_3005) with
| (e, _46_3003, g) -> begin
(
# 1726 "FStar.Tc.Tc.fst"
let _46_3006 = (let _135_1210 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _135_1210))
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
let _46_3025 = (FStar_All.pipe_right ses (FStar_List.partition (fun _46_14 -> (match (_46_14) with
| FStar_Absyn_Syntax.Sig_tycon (_46_3019) -> begin
true
end
| _46_3022 -> begin
false
end))))
in (match (_46_3025) with
| (tycons, rest) -> begin
(
# 1734 "FStar.Tc.Tc.fst"
let _46_3034 = (FStar_All.pipe_right rest (FStar_List.partition (fun _46_15 -> (match (_46_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_46_3028) -> begin
true
end
| _46_3031 -> begin
false
end))))
in (match (_46_3034) with
| (abbrevs, rest) -> begin
(
# 1735 "FStar.Tc.Tc.fst"
let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _46_16 -> (match (_46_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(
# 1737 "FStar.Tc.Tc.fst"
let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _135_1214 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _135_1214 Prims.fst))
end
| _46_3046 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _46_3049 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1742 "FStar.Tc.Tc.fst"
let _46_3053 = (FStar_List.split recs)
in (match (_46_3053) with
| (recs, abbrev_defs) -> begin
(
# 1743 "FStar.Tc.Tc.fst"
let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _135_1215 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _135_1215))
end else begin
""
end
in (
# 1746 "FStar.Tc.Tc.fst"
let _46_3055 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (
# 1747 "FStar.Tc.Tc.fst"
let _46_3060 = (tc_decls env tycons deserialized)
in (match (_46_3060) with
| (tycons, _46_3059) -> begin
(
# 1748 "FStar.Tc.Tc.fst"
let _46_3064 = (tc_decls env recs deserialized)
in (match (_46_3064) with
| (recs, _46_3063) -> begin
(
# 1749 "FStar.Tc.Tc.fst"
let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (
# 1750 "FStar.Tc.Tc.fst"
let _46_3069 = (tc_decls env1 rest deserialized)
in (match (_46_3069) with
| (rest, _46_3068) -> begin
(
# 1751 "FStar.Tc.Tc.fst"
let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(
# 1753 "FStar.Tc.Tc.fst"
let tt = (let _135_1218 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _135_1218))
in (
# 1754 "FStar.Tc.Tc.fst"
let _46_3085 = (tc_typ_trivial env1 tt)
in (match (_46_3085) with
| (tt, _46_3084) -> begin
(
# 1755 "FStar.Tc.Tc.fst"
let _46_3094 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _46_3091 -> begin
([], tt)
end)
in (match (_46_3094) with
| (tps, t) -> begin
(let _135_1220 = (let _135_1219 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _135_1219, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_135_1220))
end))
end)))
end
| _46_3096 -> begin
(let _135_1222 = (let _135_1221 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _135_1221))
in (FStar_All.failwith _135_1222))
end)) recs abbrev_defs)
in (
# 1761 "FStar.Tc.Tc.fst"
let _46_3098 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
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
let _46_3113 = (let _135_1232 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _135_1232))
in res))))))
in (
# 1775 "FStar.Tc.Tc.fst"
let _46_3128 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _46_3117 se -> (match (_46_3117) with
| (ses, env) -> begin
(
# 1777 "FStar.Tc.Tc.fst"
let _46_3119 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _135_1236 = (let _135_1235 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _135_1235))
in (FStar_Util.print_string _135_1236))
end else begin
()
end
in (
# 1779 "FStar.Tc.Tc.fst"
let _46_3123 = if (FStar_ST.read FStar_Options.timing) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_46_3123) with
| (se, env) -> begin
(
# 1783 "FStar.Tc.Tc.fst"
let _46_3124 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in ((se)::ses, env))
end)))
end)) ([], env)))
in (match (_46_3128) with
| (ses, env) -> begin
((FStar_List.rev ses), env)
end))))

# 1789 "FStar.Tc.Tc.fst"
let rec for_export : FStar_Tc_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (
# 1811 "FStar.Tc.Tc.fst"
let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _46_17 -> (match (_46_17) with
| FStar_Absyn_Syntax.Abstract -> begin
true
end
| _46_3137 -> begin
false
end)))))
in (
# 1812 "FStar.Tc.Tc.fst"
let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Absyn_Syntax.Projector (l, _)) | (FStar_Absyn_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _46_3147 -> begin
false
end))
in (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (_46_3149) -> begin
([], hidden)
end
| FStar_Absyn_Syntax.Sig_datacon (_46_3152) -> begin
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
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _46_3172, _46_3174) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _46_3180 -> (match (_46_3180) with
| (out, hidden) -> begin
(match (se) with
| FStar_Absyn_Syntax.Sig_tycon (l, bs, t, _46_3185, _46_3187, quals, r) -> begin
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
| FStar_Absyn_Syntax.Sig_assume (_46_3205, _46_3207, quals, _46_3210) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _46_18 -> (match (_46_18) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _46_3228 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Absyn_Syntax.Sig_main (_46_3230) -> begin
([], hidden)
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Absyn_Syntax.Sig_let ((false, lb::[]), _46_3246, _46_3248, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _135_1254 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _135_1253 = (let _135_1252 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_135_1252, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::quals, r))
in FStar_Absyn_Syntax.Sig_val_decl (_135_1253)))))
in (_135_1254, hidden))
end else begin
((se)::[], hidden)
end
end))))

# 1880 "FStar.Tc.Tc.fst"
let get_exports : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env modul -> (
# 1881 "FStar.Tc.Tc.fst"
let _46_3273 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.fold_left (fun _46_3265 se -> (match (_46_3265) with
| (exports, hidden) -> begin
(
# 1882 "FStar.Tc.Tc.fst"
let _46_3269 = (for_export env hidden se)
in (match (_46_3269) with
| (exports', hidden) -> begin
((exports')::exports, hidden)
end))
end)) ([], [])))
in (match (_46_3273) with
| (exports, _46_3272) -> begin
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
let _46_3278 = env
in (let _135_1265 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _46_3278.FStar_Tc_Env.solver; FStar_Tc_Env.range = _46_3278.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _46_3278.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _46_3278.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _46_3278.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _46_3278.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _46_3278.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _46_3278.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _46_3278.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _46_3278.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _46_3278.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _46_3278.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _46_3278.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _46_3278.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _46_3278.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _46_3278.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _46_3278.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _135_1265; FStar_Tc_Env.default_effects = _46_3278.FStar_Tc_Env.default_effects}))
in (
# 1890 "FStar.Tc.Tc.fst"
let _46_3281 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (
# 1891 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (
# 1892 "FStar.Tc.Tc.fst"
let _46_3286 = (tc_decls env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_46_3286) with
| (ses, env) -> begin
((
# 1893 "FStar.Tc.Tc.fst"
let _46_3287 = modul
in {FStar_Absyn_Syntax.name = _46_3287.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _46_3287.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _46_3287.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _46_3287.FStar_Absyn_Syntax.is_deserialized}), env)
end))))))))

# 1895 "FStar.Tc.Tc.fst"
let tc_more_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul decls -> (
# 1896 "FStar.Tc.Tc.fst"
let _46_3294 = (tc_decls env decls false)
in (match (_46_3294) with
| (ses, env) -> begin
(
# 1897 "FStar.Tc.Tc.fst"
let modul = (
# 1897 "FStar.Tc.Tc.fst"
let _46_3295 = modul
in {FStar_Absyn_Syntax.name = _46_3295.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _46_3295.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _46_3295.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _46_3295.FStar_Absyn_Syntax.is_deserialized})
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
let _46_3301 = modul
in {FStar_Absyn_Syntax.name = _46_3301.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _46_3301.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (
# 1903 "FStar.Tc.Tc.fst"
let env = (FStar_Tc_Env.finish_module env modul)
in (
# 1904 "FStar.Tc.Tc.fst"
let _46_3311 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(
# 1906 "FStar.Tc.Tc.fst"
let _46_3305 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (
# 1907 "FStar.Tc.Tc.fst"
let _46_3307 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
in (
# 1908 "FStar.Tc.Tc.fst"
let _46_3309 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _135_1276 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _135_1276 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

# 1913 "FStar.Tc.Tc.fst"
let tc_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (
# 1914 "FStar.Tc.Tc.fst"
let _46_3317 = (tc_partial_modul env modul)
in (match (_46_3317) with
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
let _46_3324 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (
# 1923 "FStar.Tc.Tc.fst"
let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _135_1289 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _135_1289 m)))))

# 1926 "FStar.Tc.Tc.fst"
let check_module : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env) = (fun env m -> (
# 1927 "FStar.Tc.Tc.fst"
let _46_3329 = if ((let _135_1294 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _135_1294)) <> 0) then begin
(let _135_1295 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _135_1295))
end else begin
()
end
in (
# 1930 "FStar.Tc.Tc.fst"
let _46_3333 = (tc_modul env m)
in (match (_46_3333) with
| (m, env) -> begin
(
# 1931 "FStar.Tc.Tc.fst"
let _46_3334 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _135_1296 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _135_1296))
end else begin
()
end
in ((m)::[], env))
end))))




