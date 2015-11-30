
open Prims
let syn' = (fun env k -> (let _104_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _104_11 (Some (k)))))

let log = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _104_14 = (FStar_Tc_Env.current_module env)
in (FStar_Absyn_Syntax.lid_equals FStar_Absyn_Const.prims_lid _104_14))))))

let rng = (fun env -> (FStar_Tc_Env.get_range env))

let instantiate_both = (fun env -> (let _39_24 = env
in {FStar_Tc_Env.solver = _39_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _39_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_24.FStar_Tc_Env.default_effects}))

let no_inst = (fun env -> (let _39_27 = env
in {FStar_Tc_Env.solver = _39_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _39_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_27.FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _104_34 = (let _104_33 = (let _104_32 = (let _104_27 = (let _104_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _104_25 -> FStar_Util.Inl (_104_25)) _104_26))
in (_104_27, Some (FStar_Absyn_Syntax.Implicit)))
in (let _104_31 = (let _104_30 = (FStar_Absyn_Syntax.varg v)
in (let _104_29 = (let _104_28 = (FStar_Absyn_Syntax.varg tl)
in (_104_28)::[])
in (_104_30)::_104_29))
in (_104_32)::_104_31))
in (FStar_Absyn_Util.lex_pair, _104_33))
in (FStar_Absyn_Syntax.mk_Exp_app _104_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

let is_eq = (fun _39_1 -> (match (_39_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _39_37 -> begin
false
end))

let steps = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)

let whnf = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))

let norm_t = (fun env t -> (let _104_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _104_47 env t)))

let norm_k = (fun env k -> (let _104_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _104_52 env k)))

let norm_c = (fun env c -> (let _104_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _104_57 env c)))

let fxv_check = (fun head env kt fvs -> (let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _104_76 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _104_76))
end
| FStar_Util.Inr (t) -> begin
(let _104_77 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _104_77))
end)
in (let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (norm)) then begin
(aux true kt)
end else begin
(let fail = (fun _39_61 -> (match (()) with
| () -> begin
(let escaping = (let _104_82 = (let _104_81 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _104_81 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _104_82 (FStar_String.concat ", ")))
in (let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _104_83 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _104_83))
end else begin
(let _104_84 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _104_84))
end
in (let _104_87 = (let _104_86 = (let _104_85 = (FStar_Tc_Env.get_range env)
in (msg, _104_85))
in FStar_Absyn_Syntax.Error (_104_86))
in (Prims.raise _104_87))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _39_71 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _39_78 -> begin
(fail ())
end))
end))
end
end))
end)
in (aux false kt)))

let maybe_push_binding = (fun env b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
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

let maybe_make_subst = (fun _39_2 -> (match (_39_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _39_99 -> begin
[]
end))

let maybe_alpha_subst = (fun s b1 b2 -> if (FStar_Absyn_Syntax.is_null_binder b1) then begin
s
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (FStar_Absyn_Util.bvar_eq a b) then begin
s
end else begin
(let _104_98 = (let _104_97 = (let _104_96 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _104_96))
in FStar_Util.Inl (_104_97))
in (_104_98)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _104_101 = (let _104_100 = (let _104_99 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _104_99))
in FStar_Util.Inr (_104_100))
in (_104_101)::s)
end
end
| _39_114 -> begin
(FStar_All.failwith "impossible")
end)
end)

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
| _39_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

let set_lcomp_result = (fun lc t -> (let _39_132 = lc
in {FStar_Absyn_Syntax.eff_name = _39_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _39_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _39_134 -> (match (()) with
| () -> begin
(let _104_110 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _104_110 t))
end))}))

let value_check_expected_typ = (fun env e tlc -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _104_117 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _104_117))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Absyn_Syntax.res_typ
in (let _39_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _39_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_119 = (FStar_Absyn_Print.typ_to_string t)
in (let _104_118 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.fprint2 "Computed return type %s; expected type %s\n" _104_119 _104_118)))
end else begin
()
end
in (let _39_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_39_151) with
| (e, g) -> begin
(let _39_154 = (let _104_125 = (FStar_All.pipe_left (fun _104_124 -> Some (_104_124)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _104_125 env e lc g))
in (match (_39_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_39_158) with
| (e, lc, g) -> begin
(let _39_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_126 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.fprint1 "Return comp type is %s\n" _104_126))
end else begin
()
end
in (e, lc, g))
end)))))

let comp_check_expected_typ = (fun env e lc -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t) -> begin
(FStar_Tc_Util.weaken_result_typ env e lc t)
end))

let check_expected_effect = (fun env copt _39_171 -> (match (_39_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_39_173) -> begin
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
(let flags = if (FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_Tot_lid) then begin
(FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (FStar_Absyn_Syntax.lid_equals l FStar_Absyn_Const.effect_ML_lid) then begin
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
(let _104_139 = (norm_c env c)
in (e, _104_139, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _39_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_142 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _104_141 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _104_140 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.fprint3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _104_142 _104_141 _104_140))))
end else begin
()
end
in (let c = (norm_c env c)
in (let expected_c' = (let _104_143 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _104_143))
in (let _39_195 = (let _104_144 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _104_144))
in (match (_39_195) with
| (e, _39_193, g) -> begin
(let _39_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_146 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _104_145 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.fprint2 "(%s) DONE check_expected_effect; guard is: %s\n" _104_146 _104_145)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun env _39_202 -> (match (_39_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _104_152 = (let _104_151 = (let _104_150 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _104_149 = (FStar_Tc_Env.get_range env)
in (_104_150, _104_149)))
in FStar_Absyn_Syntax.Error (_104_151))
in (Prims.raise _104_152))
end)
end))

let binding_of_lb = (fun x t -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
FStar_Tc_Env.Binding_var ((bvd, t))
end
| FStar_Util.Inr (lid) -> begin
FStar_Tc_Env.Binding_lid ((lid, t))
end))

let print_expected_ty = (fun env -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _104_159 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint1 "Expected type is %s" _104_159))
end))

let with_implicits = (fun imps _39_220 -> (match (_39_220) with
| (e, l, g) -> begin
(e, l, (let _39_221 = g
in {FStar_Tc_Rel.guard_f = _39_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _39_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun u g -> (let _39_225 = g
in {FStar_Tc_Rel.guard_f = _39_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _39_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

let rec tc_kind = (fun env k -> (let k = (FStar_Absyn_Util.compress_kind k)
in (let w = (fun f -> (f k.FStar_Absyn_Syntax.pos))
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(k, FStar_Tc_Rel.trivial_guard)
end
| FStar_Absyn_Syntax.Kind_uvar (u, args) -> begin
(let _39_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _104_212 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _104_211 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint2 "(%s) - Checking kind %s" _104_212 _104_211)))
end else begin
()
end
in (let _39_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_249) with
| (env, _39_248) -> begin
(let _39_252 = (tc_args env args)
in (match (_39_252) with
| (args, g) -> begin
(let _104_214 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_104_214, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _39_263; FStar_Absyn_Syntax.pos = _39_261; FStar_Absyn_Syntax.fvs = _39_259; FStar_Absyn_Syntax.uvs = _39_257}) -> begin
(let _39_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_39_272) with
| (_39_269, binders, body) -> begin
(let _39_275 = (tc_args env args)
in (match (_39_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _104_218 = (let _104_217 = (let _104_216 = (let _104_215 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _104_215))
in (_104_216, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_217))
in (Prims.raise _104_218))
end else begin
(let _39_308 = (FStar_List.fold_left2 (fun _39_279 b a -> (match (_39_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(let _39_289 = (let _104_222 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _104_222))
in (match (_39_289) with
| (t, g) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (let _104_224 = (let _104_223 = (FStar_Absyn_Syntax.targ t)
in (_104_223)::args)
in (subst, _104_224, (g)::guards)))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(let env = (let _104_225 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _104_225))
in (let _39_301 = (tc_ghost_exp env e)
in (match (_39_301) with
| (e, _39_299, g) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (let _104_227 = (let _104_226 = (FStar_Absyn_Syntax.varg e)
in (_104_226)::args)
in (subst, _104_227, (g)::guards)))
end)))
end
| _39_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_39_308) with
| (subst, args, guards) -> begin
(let args = (FStar_List.rev args)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _104_230 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _104_230))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _39_319 = (tc_kind env k)
in (match (_39_319) with
| (k, f) -> begin
(let _39_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_39_322) with
| (args, g) -> begin
(let kabr = ((Prims.fst kabr), args)
in (let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _104_232 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _104_232))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _39_332 = (tc_binders env bs)
in (match (_39_332) with
| (bs, env, g) -> begin
(let _39_335 = (tc_kind env k)
in (match (_39_335) with
| (k, f) -> begin
(let f = (FStar_Tc_Rel.close_guard bs f)
in (let _104_235 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _104_234 = (FStar_Tc_Rel.conj_guard g f)
in (_104_235, _104_234))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _104_236 = (FStar_Tc_Util.new_kvar env)
in (_104_236, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun env x -> (let _39_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_39_342) with
| (t, g) -> begin
(let x = (let _39_343 = x
in {FStar_Absyn_Syntax.v = _39_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_343.FStar_Absyn_Syntax.p})
in (let env' = (let _104_239 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _104_239))
in (x, env', g)))
end)))
and tc_binders = (fun env bs -> (let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _39_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_39_362) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _39_363 = a
in {FStar_Absyn_Syntax.v = _39_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_363.FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _39_370 = (aux env' bs)
in (match (_39_370) with
| (bs, env', g') -> begin
(let _104_247 = (let _104_246 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _104_246))
in ((b)::bs, env', _104_247))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _39_376 = (tc_vbinder env x)
in (match (_39_376) with
| (x, env', g) -> begin
(let b = (FStar_Util.Inr (x), imp)
in (let _39_381 = (aux env' bs)
in (match (_39_381) with
| (bs, env', g') -> begin
(let _104_249 = (let _104_248 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _104_248))
in ((b)::bs, env', _104_249))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun env args -> (FStar_List.fold_right (fun _39_386 _39_389 -> (match ((_39_386, _39_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _39_396 = (tc_typ env t)
in (match (_39_396) with
| (t, _39_394, g') -> begin
(let _104_254 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _104_254))
end))
end
| FStar_Util.Inr (e) -> begin
(let _39_403 = (tc_ghost_exp env e)
in (match (_39_403) with
| (e, _39_401, g') -> begin
(let _104_255 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _104_255))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats = (fun env pats -> (FStar_List.fold_right (fun p _39_409 -> (match (_39_409) with
| (pats, g) -> begin
(let _39_412 = (tc_args env p)
in (match (_39_412) with
| (args, g') -> begin
(let _104_260 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _104_260))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _39_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_39_419) with
| (t, g) -> begin
(let _104_263 = (FStar_Absyn_Syntax.mk_Total t)
in (_104_263, g))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (let tc = (let _104_266 = (let _104_265 = (let _104_264 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_104_264)::c.FStar_Absyn_Syntax.effect_args)
in (head, _104_265))
in (FStar_Absyn_Syntax.mk_Typ_app _104_266 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (let _39_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_39_427) with
| (tc, f) -> begin
(let _39_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_39_431) with
| (_39_429, args) -> begin
(let _39_443 = (match (args) with
| (FStar_Util.Inl (res), _39_436)::args -> begin
(res, args)
end
| _39_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_39_443) with
| (res, args) -> begin
(let _39_459 = (let _104_268 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _39_3 -> (match (_39_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _39_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_450) with
| (env, _39_449) -> begin
(let _39_455 = (tc_ghost_exp env e)
in (match (_39_455) with
| (e, _39_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _104_268 FStar_List.unzip))
in (match (_39_459) with
| (flags, guards) -> begin
(let _104_270 = (FStar_Absyn_Syntax.mk_Comp (let _39_460 = c
in {FStar_Absyn_Syntax.effect_name = _39_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _39_460.FStar_Absyn_Syntax.flags}))
in (let _104_269 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_104_270, _104_269)))
end))
end))
end))
end)))))
end))
and tc_typ = (fun env t -> (let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (let w = (fun k -> (FStar_Absyn_Syntax.syn t.FStar_Absyn_Syntax.pos (Some (k))))
in (let t = (FStar_Absyn_Util.compress_typ t)
in (let top = t
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let k = (FStar_Tc_Env.lookup_btvar env a)
in (let a = (let _39_472 = a
in {FStar_Absyn_Syntax.v = _39_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_472.FStar_Absyn_Syntax.p})
in (let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _39_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_39_479) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Absyn_Syntax.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.eqT_k k)
in (let i = (let _39_484 = i
in {FStar_Absyn_Syntax.v = _39_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _39_484.FStar_Absyn_Syntax.p})
in (let _104_293 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_104_293, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Absyn_Syntax.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Absyn_Syntax.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.allT_k k)
in (let i = (let _39_491 = i
in {FStar_Absyn_Syntax.v = _39_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _39_491.FStar_Absyn_Syntax.p})
in (let _104_294 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_104_294, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _39_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (let i = (let _39_501 = i
in {FStar_Absyn_Syntax.v = _39_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_501.FStar_Absyn_Syntax.p})
in (let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (let _39_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_39_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(let _39_516 = (tc_binders env bs)
in (match (_39_516) with
| (bs, env, g) -> begin
(let _39_519 = (tc_comp env cod)
in (match (_39_519) with
| (cod, f) -> begin
(let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _39_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _39_542; FStar_Absyn_Syntax.result_typ = _39_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _39_536)::(FStar_Util.Inl (post), _39_531)::(FStar_Util.Inr (pats), _39_526)::[]; FStar_Absyn_Syntax.flags = _39_522}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _104_299 = (FStar_Absyn_Util.compress_exp pats)
in _104_299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _39_557); FStar_Absyn_Syntax.tk = _39_554; FStar_Absyn_Syntax.pos = _39_552; FStar_Absyn_Syntax.fvs = _39_550; FStar_Absyn_Syntax.uvs = _39_548}, _39_572::(FStar_Util.Inr (hd), _39_569)::(FStar_Util.Inr (tl), _39_564)::[]) when (FStar_Absyn_Syntax.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _39_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_39_578) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _39_585 -> begin
[]
end)
in (let _104_300 = (extract_pats tl)
in (FStar_List.append pat _104_300)))
end))
end
| _39_588 -> begin
[]
end))
in (let pats = (let _104_301 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _104_301))
in (let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _39_594 -> (match (_39_594) with
| (b, _39_593) -> begin
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
(let _104_304 = (let _104_303 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _104_303))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _104_304))
end))))
end
| _39_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _104_306 = (let _104_305 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _104_305))
in (t, FStar_Absyn_Syntax.ktype, _104_306))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _39_613 = (tc_binders env bs)
in (match (_39_613) with
| (bs, env, g) -> begin
(let _39_617 = (tc_typ env t)
in (match (_39_617) with
| (t, k, f) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _104_311 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _104_310 = (let _104_309 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _104_309))
in (_104_311, k, _104_310))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let _39_626 = (tc_vbinder env x)
in (match (_39_626) with
| (x, env, f1) -> begin
(let _39_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_314 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_313 = (FStar_Absyn_Print.typ_to_string phi)
in (let _104_312 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.fprint3 "(%s) Checking refinement formula %s; env expects type %s\n" _104_314 _104_313 _104_312))))
end else begin
()
end
in (let _39_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_39_634) with
| (phi, f2) -> begin
(let _104_321 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _104_320 = (let _104_319 = (let _104_318 = (let _104_317 = (FStar_Absyn_Syntax.v_binder x)
in (_104_317)::[])
in (FStar_Tc_Rel.close_guard _104_318 f2))
in (FStar_Tc_Rel.conj_guard f1 _104_319))
in (_104_321, FStar_Absyn_Syntax.ktype, _104_320)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _39_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_324 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_323 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _104_322 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.fprint3 "(%s) Checking type application (%s): %s\n" _104_324 _104_323 _104_322))))
end else begin
()
end
in (let _39_644 = (tc_typ (no_inst env) head)
in (match (_39_644) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _39_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_328 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _104_327 = (FStar_Absyn_Print.typ_to_string head)
in (let _104_326 = (FStar_Absyn_Print.kind_to_string k1')
in (let _104_325 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.fprint4 "(%s) head %s has kind %s ... after norm %s\n" _104_328 _104_327 _104_326 _104_325)))))
end else begin
()
end
in (let check_app = (fun _39_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_39_652) -> begin
(let _39_656 = (tc_args env args)
in (match (_39_656) with
| (args, g) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _104_331 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _104_331 Prims.fst))
in (let bs = (let _104_332 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _104_332))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (let _39_662 = (let _104_333 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _104_333))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _104_344 = (FStar_Absyn_Util.subst_kind subst kres)
in (_104_344, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _104_348 = (let _104_347 = (let _104_346 = (let _104_345 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_345))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _104_346))
in FStar_Absyn_Syntax.Error (_104_347))
in (Prims.raise _104_348))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _39_735 = (let _104_349 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _104_349))
in (match (_39_735) with
| (t, u) -> begin
(let targ = (FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (FStar_Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _39_764 = (let _104_350 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _104_350))
in (match (_39_764) with
| (e, u) -> begin
(let varg = (FStar_Util.Inr (e), Some (FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (FStar_Util.Inr (u)) g)
in (let subst = (maybe_extend_subst subst formal varg)
in (check_args ((varg)::outargs) subst g rest args))))
end)))
end
| (formal::formals, actual::actuals) -> begin
(match ((formal, actual)) with
| ((FStar_Util.Inl (a), aqual), (FStar_Util.Inl (t), imp)) -> begin
(let formal_k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_785 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_352 = (FStar_Absyn_Print.arg_to_string actual)
in (let _104_351 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.fprint2 "Checking argument %s against expected kind %s\n" _104_352 _104_351)))
end else begin
()
end
in (let _39_791 = (tc_typ_check (let _39_787 = env
in {FStar_Tc_Env.solver = _39_787.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_787.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_787.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_787.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_787.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_787.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_787.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_787.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_787.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_787.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_787.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_787.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_787.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_787.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_787.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_787.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_787.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_787.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_787.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_39_791) with
| (t, g') -> begin
(let _39_792 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_353 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.fprint1 ">>>Got guard %s\n" _104_353))
end else begin
()
end
in (let actual = (FStar_Util.Inl (t), imp)
in (let g' = (let _104_355 = (let _104_354 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _104_354))
in (FStar_Tc_Rel.imp_guard _104_355 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _104_356 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _104_356 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _39_808 = env'
in {FStar_Tc_Env.solver = _39_808.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_808.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_808.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_808.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_808.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_808.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_808.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_808.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_808.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_808.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_808.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_808.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_808.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_808.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_808.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_808.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_808.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_808.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_808.FStar_Tc_Env.default_effects})
in (let _39_811 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_358 = (FStar_Absyn_Print.arg_to_string actual)
in (let _104_357 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.fprint2 "Checking argument %s against expected type %s\n" _104_358 _104_357)))
end else begin
()
end
in (let _39_817 = (tc_ghost_exp env' v)
in (match (_39_817) with
| (v, _39_815, g') -> begin
(let actual = (FStar_Util.Inr (v), imp)
in (let g' = (let _104_360 = (let _104_359 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _104_359))
in (FStar_Tc_Rel.imp_guard _104_360 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _104_361 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _104_361 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _39_824), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (FStar_Absyn_Util.b2t v)
in (let _104_363 = (let _104_362 = (FStar_Absyn_Syntax.targ tv)
in (_104_362)::actuals)
in (check_args outargs subst g ((formal)::formals) _104_363)))
end
| _39_834 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_39_836), _39_839), (FStar_Util.Inl (_39_842), _39_845)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_39_849, []) -> begin
(let _104_365 = (let _104_364 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _104_364))
in (_104_365, (FStar_List.rev outargs), g))
end
| ([], _39_854) -> begin
(let _104_373 = (let _104_372 = (let _104_371 = (let _104_370 = (let _104_368 = (let _104_367 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _39_4 -> (match (_39_4) with
| (_39_858, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _39_863 -> begin
true
end))))
in (FStar_List.length _104_367))
in (FStar_All.pipe_right _104_368 FStar_Util.string_of_int))
in (let _104_369 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _104_370 _104_369)))
in (_104_371, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_372))
in (Prims.raise _104_373))
end))
in (check_args [] [] f1 formals args))
end
| _39_865 -> begin
(let _104_376 = (let _104_375 = (let _104_374 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_104_374, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_375))
in (Prims.raise _104_376))
end)
end))
in (match ((let _104_380 = (let _104_377 = (FStar_Absyn_Util.compress_typ head)
in _104_377.FStar_Absyn_Syntax.n)
in (let _104_379 = (let _104_378 = (FStar_Absyn_Util.compress_kind k1)
in _104_378.FStar_Absyn_Syntax.n)
in (_104_380, _104_379)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_39_867), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(let result_k = (let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in (t, result_k, FStar_Tc_Rel.trivial_guard)))
end
| _39_878 -> begin
(let _39_882 = (check_app ())
in (match (_39_882) with
| (k, args, g) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(let _39_890 = (tc_kind env k1)
in (match (_39_890) with
| (k1, f1) -> begin
(let _39_893 = (tc_typ_check env t1 k1)
in (match (_39_893) with
| (t1, f2) -> begin
(let _104_384 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _104_383 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_104_384, k1, _104_383)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (u, k1) when env.FStar_Tc_Env.check_uvars -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _39_905 = (tc_kind env k1)
in (match (_39_905) with
| (k1, g) -> begin
(let _39_909 = (FStar_Tc_Rel.new_tvar s.FStar_Absyn_Syntax.pos [] k1)
in (match (_39_909) with
| (_39_907, u') -> begin
(let _39_910 = (FStar_Absyn_Util.unchecked_unify u u')
in (u', k1, g))
end))
end))
end
| _39_913 -> begin
(tc_typ env s)
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_39_915, k1) -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _39_924 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _104_386 = (FStar_Absyn_Print.typ_to_string s)
in (let _104_385 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.fprint2 "Admitting un-instantiated uvar %s at kind %s\n" _104_386 _104_385)))
end else begin
()
end
in (let _104_389 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_104_389, k1, FStar_Tc_Rel.trivial_guard)))
end
| _39_927 -> begin
(let _39_928 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _104_391 = (FStar_Absyn_Print.typ_to_string s)
in (let _104_390 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.fprint2 "Admitting instantiated uvar %s at kind %s\n" _104_391 _104_390)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(let _39_939 = (tc_typ env t)
in (match (_39_939) with
| (t, k, f) -> begin
(let _104_392 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_104_392, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(let _39_950 = (tc_typ env t)
in (match (_39_950) with
| (t, k, f) -> begin
(let _104_393 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_104_393, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(let _39_959 = (tc_typ env t)
in (match (_39_959) with
| (t, k, f) -> begin
(let _104_394 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_104_394, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(let _39_967 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_39_967) with
| (quant, f) -> begin
(let _39_970 = (tc_pats env pats)
in (match (_39_970) with
| (pats, g) -> begin
(let g = (let _39_971 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _39_971.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _39_971.FStar_Tc_Rel.implicits})
in (let _104_397 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _104_396 = (FStar_Tc_Util.force_tk quant)
in (let _104_395 = (FStar_Tc_Rel.conj_guard f g)
in (_104_397, _104_396, _104_395)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let t = (FStar_Tc_Util.new_tvar env k)
in (t, k, FStar_Tc_Rel.trivial_guard)))
end
| _39_978 -> begin
(let _104_399 = (let _104_398 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _104_398))
in (FStar_All.failwith _104_399))
end))))))
and tc_typ_check = (fun env t k -> (let _39_985 = (tc_typ env t)
in (match (_39_985) with
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
and tc_value = (fun env e -> (let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (_39_994, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (FStar_Tc_Env.lookup_bvar env x)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar (let _39_1001 = x
in {FStar_Absyn_Syntax.v = _39_1001.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_1001.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _39_1007 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_39_1007) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
FStar_Util.Inl (t)
end else begin
(let _104_406 = (let _104_405 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_405))
in FStar_Util.Inr (_104_406))
end
in (let _104_407 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _104_407)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (let e = (FStar_Absyn_Syntax.mk_Exp_fvar ((let _39_1014 = v
in {FStar_Absyn_Syntax.v = _39_1014.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_1014.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _39_1020 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_39_1020) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
FStar_Util.Inl (t)
end else begin
(let _104_409 = (let _104_408 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_408))
in FStar_Util.Inr (_104_409))
end
in (let is_data_ctor = (fun _39_5 -> (match (_39_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _39_1030 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _104_415 = (let _104_414 = (let _104_413 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.str)
in (let _104_412 = (FStar_Tc_Env.get_range env)
in (_104_413, _104_412)))
in FStar_Absyn_Syntax.Error (_104_414))
in (Prims.raise _104_415))
end else begin
(let _104_416 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _104_416))
end))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fail = (fun msg t -> (let _104_421 = (let _104_420 = (let _104_419 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_104_419, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_420))
in (Prims.raise _104_421)))
in (let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(let _39_1051 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _39_1050 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _39_1056 = (tc_binders env bs)
in (match (_39_1056) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun norm t -> (match ((let _104_430 = (FStar_Absyn_Util.compress_typ t)
in _104_430.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _39_1085 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _39_1084 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _39_1090 = (tc_binders env bs)
in (match (_39_1090) with
| (bs, envbody, g) -> begin
(let _39_1094 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_39_1094) with
| (envbody, _39_1093) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let rec tc_binders = (fun _39_1104 bs_annot c bs -> (match (_39_1104) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _104_439 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _104_439))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_39_1119), _39_1122), (FStar_Util.Inr (_39_1125), _39_1128)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _39_1135), (FStar_Util.Inl (b), imp)) -> begin
(let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_1153 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _39_1145 -> begin
(let _39_1148 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_39_1148) with
| (k, g1) -> begin
(let g2 = (FStar_Tc_Rel.keq env None ka k)
in (let g = (let _104_440 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _104_440))
in (k, g)))
end))
end)
in (match (_39_1153) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _39_1154 = b
in {FStar_Absyn_Syntax.v = _39_1154.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _39_1154.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _39_1162), (FStar_Util.Inr (y), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _39_1184 = (match ((let _104_441 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _104_441.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _39_1172 -> begin
(let _39_1173 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_442 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.fprint1 "Checking binder %s\n" _104_442))
end else begin
()
end
in (let _39_1179 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_39_1179) with
| (t, _39_1177, g1) -> begin
(let g2 = (FStar_Tc_Rel.teq env tx t)
in (let g = (let _104_443 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _104_443))
in (t, g)))
end)))
end)
in (match (_39_1184) with
| (t, g) -> begin
(let b = (FStar_Util.Inr ((let _39_1185 = y
in {FStar_Absyn_Syntax.v = _39_1185.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _39_1185.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _39_1191 -> begin
(let _104_446 = (let _104_445 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _104_444 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _104_445 _104_444)))
in (fail _104_446 t))
end)
end
| ([], _39_1194) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _39_1203; FStar_Absyn_Syntax.pos = _39_1201; FStar_Absyn_Syntax.fvs = _39_1199; FStar_Absyn_Syntax.uvs = _39_1197} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _104_448 = (let _104_447 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _104_447))
in (fail _104_448 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_39_1211, []) -> begin
(let c = (let _104_449 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _104_449 c.FStar_Absyn_Syntax.pos))
in (let _104_450 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _104_450)))
end)
end))
in (let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _39_1220 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_455 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint1 "Building let-rec environment... type of this abstraction is %s\n" _104_455))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let env = (let _39_1223 = env
in {FStar_Tc_Env.solver = _39_1223.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1223.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1223.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1223.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1223.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1223.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1223.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1223.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1223.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1223.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1223.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1223.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1223.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _39_1223.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1223.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_1223.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_1223.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1223.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1223.FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_39_1230), _39_1233) -> begin
[]
end
| (FStar_Util.Inr (x), _39_1238) -> begin
(match ((let _104_461 = (let _104_460 = (let _104_459 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _104_459))
in (FStar_Absyn_Util.unrefine _104_460))
in _104_461.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_39_1241) -> begin
[]
end
| _39_1244 -> begin
(let _104_462 = (FStar_Absyn_Util.bvar_to_exp x)
in (_104_462)::[])
end)
end)))))
in (let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun dec -> (let _39_1251 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_39_1251) with
| (head, _39_1250) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _39_1254) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _39_1258 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _39_6 -> (match (_39_6) with
| FStar_Absyn_Syntax.DECREASES (_39_1262) -> begin
true
end
| _39_1265 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _39_1269 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _104_471 = (let _104_470 = (let _104_469 = (let _104_467 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _104_466 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _104_467 _104_466)))
in (let _104_468 = (FStar_Tc_Env.get_range env)
in (_104_469, _104_468)))
in FStar_Absyn_Syntax.Error (_104_470))
in (Prims.raise _104_471))
end else begin
()
end
in (let dec = (as_lex_list dec)
in (let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _39_1277), (FStar_Util.Inl (actual), _39_1282)) -> begin
(let _104_475 = (let _104_474 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _104_474))
in FStar_Util.Inl (_104_475))
end
| ((FStar_Util.Inr (formal), _39_1288), (FStar_Util.Inr (actual), _39_1293)) -> begin
(let _104_477 = (let _104_476 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _104_476))
in FStar_Util.Inr (_104_477))
end
| _39_1297 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _39_1300 -> begin
(let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _39_1305 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _39_1309 -> (match (_39_1309) with
| (l, t0) -> begin
(let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _104_479 = (FStar_Absyn_Util.compress_typ t)
in _104_479.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _39_7 -> (match (_39_7) with
| FStar_Absyn_Syntax.DECREASES (_39_1325) -> begin
true
end
| _39_1328 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _104_483 = (let _104_482 = (let _104_481 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _104_481))
in FStar_Util.Inr (_104_482))
in (_104_483)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _104_488 = (let _104_487 = (let _104_486 = (FStar_Absyn_Syntax.varg dec)
in (let _104_485 = (let _104_484 = (FStar_Absyn_Syntax.varg prev_dec)
in (_104_484)::[])
in (_104_486)::_104_485))
in (precedes, _104_487))
in (FStar_Absyn_Syntax.mk_Typ_app _104_488 None r))))
end
| _39_1336 -> begin
(let formal_args = (let _104_491 = (let _104_490 = (let _104_489 = (FStar_Absyn_Syntax.v_binder y)
in (_104_489)::[])
in (FStar_List.append bs _104_490))
in (FStar_All.pipe_right _104_491 filter_types_and_functions))
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _39_1341 -> begin
(mk_lex_list formal_args)
end)
in (let _104_496 = (let _104_495 = (let _104_494 = (FStar_Absyn_Syntax.varg lhs)
in (let _104_493 = (let _104_492 = (FStar_Absyn_Syntax.varg prev_dec)
in (_104_492)::[])
in (_104_494)::_104_493))
in (precedes, _104_495))
in (FStar_Absyn_Syntax.mk_Typ_app _104_496 None r))))
end)
in (let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (FStar_List.append bs (((FStar_Util.Inr ((let _39_1345 = x
in {FStar_Absyn_Syntax.v = _39_1345.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _39_1345.FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _39_1349 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_499 = (FStar_Absyn_Print.lbname_to_string l)
in (let _104_498 = (FStar_Absyn_Print.typ_to_string t)
in (let _104_497 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.fprint3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _104_499 _104_498 _104_497))))
end else begin
()
end
in (let _39_1356 = (let _104_501 = (let _104_500 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _104_500 Prims.fst))
in (tc_typ _104_501 t'))
in (match (_39_1356) with
| (t', _39_1353, _39_1355) -> begin
(l, t')
end)))))))))
end
| _39_1358 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _39_1360 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _104_507 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _39_1365 -> (match (_39_1365) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _104_506 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _39_8 -> (match (_39_8) with
| (FStar_Util.Inl (x), t) -> begin
(let _104_505 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_104_505)::[])
end
| _39_1372 -> begin
[]
end))))
in (_104_507, _104_506)))))))))))
end))
in (let _39_1377 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_39_1377) with
| (bs, envbody, g, c) -> begin
(let _39_1380 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_39_1380) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _39_1384) -> begin
(let _39_1394 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_39_1394) with
| (_39_1388, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _39_1396 -> begin
if (not (norm)) then begin
(let _104_508 = (whnf env t)
in (as_function_typ true _104_508))
end else begin
(let _39_1405 = (expected_function_typ env None)
in (match (_39_1405) with
| (_39_1398, bs, _39_1401, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_Tc_Env.use_eq
in (let _39_1409 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_1409) with
| (env, topt) -> begin
(let _39_1416 = (expected_function_typ env topt)
in (match (_39_1416) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _39_1422 = (tc_exp (let _39_1417 = envbody
in {FStar_Tc_Env.solver = _39_1417.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1417.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1417.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1417.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1417.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1417.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1417.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1417.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1417.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1417.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1417.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1417.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1417.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1417.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _39_1417.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _39_1417.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1417.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1417.FStar_Tc_Env.default_effects}) body)
in (match (_39_1422) with
| (body, cbody, guard_body) -> begin
(let _39_1423 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _104_511 = (FStar_Absyn_Print.exp_to_string body)
in (let _104_510 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _104_509 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.fprint3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _104_511 _104_510 _104_509))))
end else begin
()
end
in (let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _39_1426 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _104_512 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.fprint1 "Introduced %s implicits in body of abstraction\n" _104_512))
end else begin
()
end
in (let _39_1433 = (let _104_514 = (let _104_513 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _104_513))
in (check_expected_effect (let _39_1428 = envbody
in {FStar_Tc_Env.solver = _39_1428.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1428.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1428.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1428.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1428.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1428.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1428.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1428.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1428.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1428.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1428.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1428.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1428.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1428.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_1428.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1428.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _39_1428.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1428.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1428.FStar_Tc_Env.default_effects}) c_opt _104_514))
in (match (_39_1433) with
| (body, cbody, guard) -> begin
(let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)))) then begin
(let _39_1435 = (let _104_515 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _104_515))
in (let _39_1437 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _39_1437.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _39_1437.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (let e = (let _104_517 = (let _104_516 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_104_516, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _104_517 None top.FStar_Absyn_Syntax.pos))
in (let _39_1460 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_39_1449) -> begin
(let _104_520 = (let _104_519 = (let _104_518 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_104_518, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _104_519 None top.FStar_Absyn_Syntax.pos))
in (_104_520, t, guard))
end
| _39_1452 -> begin
(let _39_1455 = if use_teq then begin
(let _104_521 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _104_521))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_39_1455) with
| (e, guard') -> begin
(let _104_523 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _104_522 = (FStar_Tc_Rel.conj_guard guard guard')
in (_104_523, t, _104_522)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_39_1460) with
| (e, tfun, guard) -> begin
(let _39_1461 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_526 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _104_525 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _104_524 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.fprint3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _104_526 _104_525 _104_524))))
end else begin
()
end
in (let c = if env.FStar_Tc_Env.top_level then begin
(FStar_Absyn_Syntax.mk_Total tfun)
end else begin
(FStar_Tc_Util.return_value env tfun e)
end
in (let _39_1466 = (let _104_528 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _104_528 guard))
in (match (_39_1466) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _39_1468 -> begin
(let _104_530 = (let _104_529 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _104_529))
in (FStar_All.failwith _104_530))
end))))
and tc_exp = (fun env e -> (let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (let _39_1472 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_535 = (let _104_533 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _104_533))
in (let _104_534 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.fprint2 "%s (%s)\n" _104_535 _104_534)))
end else begin
()
end
in (let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_39_1478) -> begin
(let _104_559 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _104_559))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _39_1498) -> begin
(let _39_1503 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_39_1503) with
| (t1, f) -> begin
(let _39_1507 = (let _104_560 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _104_560 e1))
in (match (_39_1507) with
| (e1, c, g) -> begin
(let _39_1511 = (let _104_564 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _39_1508 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _104_564 e1 c f))
in (match (_39_1511) with
| (c, f) -> begin
(let _39_1515 = (let _104_568 = (let _104_567 = (w c)
in (FStar_All.pipe_left _104_567 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _104_568 c))
in (match (_39_1515) with
| (e, c, f2) -> begin
(let _104_570 = (let _104_569 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _104_569))
in (e, c, _104_570))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(let pats_t = (let _104_576 = (let _104_575 = (let _104_571 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _104_571))
in (let _104_574 = (let _104_573 = (let _104_572 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _104_572))
in (_104_573)::[])
in (_104_575, _104_574)))
in (FStar_Absyn_Syntax.mk_Typ_app _104_576 None FStar_Absyn_Syntax.dummyRange))
in (let _39_1525 = (let _104_577 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _104_577 e))
in (match (_39_1525) with
| (e, t, g) -> begin
(let g = (let _39_1526 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _39_1526.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _39_1526.FStar_Tc_Rel.implicits})
in (let c = (let _104_578 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _104_578 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _104_579 = (FStar_Absyn_Util.compress_exp e)
in _104_579.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_39_1536, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _39_1541; FStar_Absyn_Syntax.lbeff = _39_1539; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _39_1552 = (let _104_580 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _104_580 e1))
in (match (_39_1552) with
| (e1, c1, g1) -> begin
(let _39_1556 = (tc_exp env e2)
in (match (_39_1556) with
| (e2, c2, g2) -> begin
(let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _104_593 = (let _104_591 = (let _104_590 = (let _104_589 = (let _104_588 = (w c)
in (let _104_587 = (let _104_586 = (let _104_585 = (let _104_584 = (let _104_583 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1))
in (_104_583)::[])
in (false, _104_584))
in (_104_585, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _104_586))
in (FStar_All.pipe_left _104_588 _104_587)))
in (_104_589, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_104_590))
in (FStar_Absyn_Syntax.mk_Exp_meta _104_591))
in (let _104_592 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_104_593, c, _104_592))))
end))
end))
end
| _39_1559 -> begin
(let _39_1563 = (tc_exp env e)
in (match (_39_1563) with
| (e, c, g) -> begin
(let _104_594 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_104_594, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(let _39_1572 = (tc_exp env e)
in (match (_39_1572) with
| (e, c, g) -> begin
(let _104_595 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_104_595, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let env0 = env
in (let env = (let _104_597 = (let _104_596 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _104_596 Prims.fst))
in (FStar_All.pipe_right _104_597 instantiate_both))
in (let _39_1579 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_599 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_598 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.fprint2 "(%s) Checking app %s\n" _104_599 _104_598)))
end else begin
()
end
in (let _39_1584 = (tc_exp (no_inst env) head)
in (match (_39_1584) with
| (head, chead, g_head) -> begin
(let aux = (fun _39_1586 -> (match (()) with
| () -> begin
(let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _39_1590) when (((FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _39_1602)::(FStar_Util.Inr (e2), _39_1597)::[] -> begin
(let _39_1608 = (tc_exp env e1)
in (match (_39_1608) with
| (e1, c1, g1) -> begin
(let _39_1612 = (tc_exp env e2)
in (match (_39_1612) with
| (e2, c2, g2) -> begin
(let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = if (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _104_605 = (let _104_602 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _104_602))
in (let _104_604 = (let _104_603 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _104_603 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _104_605 c2 _104_604)))
end else begin
(let _104_609 = (let _104_606 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _104_606))
in (let _104_608 = (let _104_607 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _104_607 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _104_609 _104_608 c2)))
end
in (let c = (let _104_612 = (let _104_611 = (FStar_All.pipe_left (fun _104_610 -> Some (_104_610)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_104_611, c2))
in (FStar_Tc_Util.bind env None c1 _104_612))
in (let e = (let _104_617 = (let _104_616 = (let _104_615 = (FStar_Absyn_Syntax.varg e1)
in (let _104_614 = (let _104_613 = (FStar_Absyn_Syntax.varg e2)
in (_104_613)::[])
in (_104_615)::_104_614))
in (head, _104_616))
in (FStar_Absyn_Syntax.mk_Exp_app _104_617 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _104_619 = (let _104_618 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _104_618))
in (e, c, _104_619)))))))
end))
end))
end
| _39_1619 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _39_1621 -> begin
(let thead = chead.FStar_Absyn_Syntax.res_typ
in (let _39_1623 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_621 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _104_620 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.fprint2 "(%s) Type of head is %s\n" _104_621 _104_620)))
end else begin
()
end
in (let rec check_function_app = (fun norm tf -> (match ((let _104_626 = (FStar_Absyn_Util.unrefine tf)
in _104_626.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _39_1656)::_39_1652 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(let _39_1668 = (tc_exp env e)
in (match (_39_1668) with
| (e, c, g_e) -> begin
(let _39_1672 = (tc_args env tl)
in (match (_39_1672) with
| (args, comps, g_rest) -> begin
(let _104_631 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _104_631))
end))
end))
end))
in (let _39_1676 = (tc_args env args)
in (match (_39_1676) with
| (args, comps, g_args) -> begin
(let bs = (let _104_632 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _104_632))
in (let cres = (let _104_633 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _104_633 top.FStar_Absyn_Syntax.pos))
in (let _39_1679 = (let _104_635 = (let _104_634 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _104_634))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _104_635))
in (let comp = (let _104_638 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _104_638))
in (let _104_640 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _104_639 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_104_640, comp, _104_639)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let vars = (FStar_Tc_Env.binders env)
in (let rec tc_args = (fun _39_1696 bs cres args -> (match (_39_1696) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_39_1710, None)::_39_1708) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_1716 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _39_1720 = (let _104_676 = (let _104_675 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_675))
in (FStar_Tc_Rel.new_tvar _104_676 vars k))
in (match (_39_1720) with
| (targ, u) -> begin
(let _39_1721 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_678 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _104_677 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint2 "Instantiating %s to %s" _104_678 _104_677)))
end else begin
()
end
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (let _104_679 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inl (targ), _104_679))
in (let _104_688 = (let _104_687 = (let _104_686 = (let _104_685 = (let _104_684 = (FStar_Tc_Util.as_uvar_t u)
in (_104_684, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_104_685))
in (add_implicit _104_686 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _104_687, fvs))
in (tc_args _104_688 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_39_1735, None)::_39_1733) -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _39_1741 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (let _39_1745 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_39_1745) with
| (varg, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (let _104_689 = (FStar_Absyn_Syntax.as_implicit true)
in (FStar_Util.Inr (varg), _104_689))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(let _39_1761 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_695 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _104_694 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "\tGot a type arg for %s = %s\n" _104_695 _104_694)))
end else begin
()
end
in (let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _39_1764 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _39_1770 = (tc_typ_check (let _39_1766 = env
in {FStar_Tc_Env.solver = _39_1766.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1766.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1766.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1766.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1766.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1766.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1766.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1766.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1766.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1766.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1766.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1766.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1766.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1766.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_1766.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1766.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_1766.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1766.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1766.FStar_Tc_Env.default_effects}) t k)
in (match (_39_1770) with
| (t, g') -> begin
(let f = (let _104_696 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _104_696))
in (let g' = (let _39_1772 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _39_1772.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _39_1772.FStar_Tc_Rel.implicits})
in (let arg = (FStar_Util.Inl (t), aq)
in (let subst = (let _104_697 = (FStar_List.hd bs)
in (maybe_extend_subst subst _104_697 arg))
in (let _104_703 = (let _104_702 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _104_702, fvs))
in (tc_args _104_703 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(let _39_1790 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_705 = (FStar_Absyn_Print.subst_to_string subst)
in (let _104_704 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.fprint2 "\tType of arg (before subst (%s)) = %s\n" _104_705 _104_704)))
end else begin
()
end
in (let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _39_1793 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_706 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint1 "\tType of arg (after subst) = %s\n" _104_706))
end else begin
()
end
in (let _39_1795 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (let env = (FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _39_1798 = env
in {FStar_Tc_Env.solver = _39_1798.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_1798.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_1798.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_1798.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_1798.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_1798.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_1798.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_1798.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_1798.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_1798.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_1798.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_1798.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_1798.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_1798.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_1798.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_1798.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _39_1798.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_1798.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_1798.FStar_Tc_Env.default_effects})
in (let _39_1801 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _104_708 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_707 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint2 "Checking arg %s at type %s with an equality constraint!\n" _104_708 _104_707)))
end else begin
()
end
in (let _39_1803 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_711 = (FStar_Absyn_Print.tag_of_exp e)
in (let _104_710 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_709 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.fprint3 "Checking arg (%s) %s at type %s\n" _104_711 _104_710 _104_709))))
end else begin
()
end
in (let _39_1808 = (tc_exp env e)
in (match (_39_1808) with
| (e, c, g_e) -> begin
(let g = (FStar_Tc_Rel.conj_guard g g_e)
in (let _39_1810 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_713 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _104_712 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.fprint2 "Guard on this arg is %s;\naccumulated guard is %s\n" _104_713 _104_712)))
end else begin
()
end
in (let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(let subst = (let _104_714 = (FStar_List.hd bs)
in (maybe_extend_subst subst _104_714 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(let subst = (let _104_719 = (FStar_List.hd bs)
in (maybe_extend_subst subst _104_719 arg))
in (let _39_1817 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_39_1817) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _104_724 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _104_724)) then begin
(let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _104_725 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _104_725))
in (let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _104_738 = (let _104_737 = (let _104_731 = (let _104_730 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _104_730))
in (_104_731)::arg_rets)
in (let _104_736 = (let _104_734 = (let _104_733 = (FStar_All.pipe_left (fun _104_732 -> Some (_104_732)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_104_733, c))
in (_104_734)::comps)
in (let _104_735 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _104_737, _104_736, g, _104_735))))
in (tc_args _104_738 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_39_1824), _39_1827)::_39_1822, (FStar_Util.Inl (_39_1833), _39_1836)::_39_1831) -> begin
(let _104_742 = (let _104_741 = (let _104_740 = (let _104_739 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_739))
in ("Expected an expression; got a type", _104_740))
in FStar_Absyn_Syntax.Error (_104_741))
in (Prims.raise _104_742))
end
| ((FStar_Util.Inl (_39_1843), _39_1846)::_39_1841, (FStar_Util.Inr (_39_1852), _39_1855)::_39_1850) -> begin
(let _104_746 = (let _104_745 = (let _104_744 = (let _104_743 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _104_743))
in ("Expected a type; got an expression", _104_744))
in FStar_Absyn_Syntax.Error (_104_745))
in (Prims.raise _104_746))
end
| (_39_1860, []) -> begin
(let _39_1863 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (let _39_1881 = (match (bs) with
| [] -> begin
(let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _39_1871 -> (match (_39_1871) with
| (_39_1869, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = if refine_with_equality then begin
(let _104_748 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _104_748 cres))
end else begin
(let _39_1873 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_751 = (FStar_Absyn_Print.exp_to_string head)
in (let _104_750 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _104_749 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.fprint3 "Not refining result: f=%s; cres=%s; guard=%s\n" _104_751 _104_750 _104_749))))
end else begin
()
end
in cres)
end
in (let _104_752 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_104_752, g))))))
end
| _39_1877 -> begin
(let g = (let _104_753 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _104_753 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _104_759 = (let _104_758 = (let _104_757 = (let _104_756 = (let _104_755 = (let _104_754 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _104_754))
in (FStar_Absyn_Syntax.mk_Typ_fun _104_755 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _104_756))
in (FStar_Absyn_Syntax.mk_Total _104_757))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_758))
in (_104_759, g)))
end)
in (match (_39_1881) with
| (cres, g) -> begin
(let _39_1882 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_760 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.fprint1 "\t Type of result cres is %s\n" _104_760))
end else begin
()
end
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev outargs)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _39_1891 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_39_1891) with
| (comp, g) -> begin
(let _39_1892 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_766 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _104_765 = (let _104_764 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _104_764))
in (FStar_Util.fprint2 "\t Type of app term %s is %s\n" _104_766 _104_765)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_39_1896) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _104_771 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _104_771 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(let _39_1908 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_772 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.fprint1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _104_772))
end else begin
()
end
in (let _104_777 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _104_777 args)))
end
| _39_1911 when (not (norm)) -> begin
(let _104_778 = (whnf env tres)
in (aux true _104_778))
end
| _39_1913 -> begin
(let _104_784 = (let _104_783 = (let _104_782 = (let _104_780 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _104_779 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _104_780 _104_779)))
in (let _104_781 = (FStar_Absyn_Syntax.argpos arg)
in (_104_782, _104_781)))
in FStar_Absyn_Syntax.Error (_104_783))
in (Prims.raise _104_784))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _104_785 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _104_785 args))))
end
| _39_1915 -> begin
if (not (norm)) then begin
(let _104_786 = (whnf env tf)
in (check_function_app true _104_786))
end else begin
(let _104_789 = (let _104_788 = (let _104_787 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_104_787, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_788))
in (Prims.raise _104_789))
end
end))
in (let _104_790 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _104_790)))))
end))
end))
in (let _39_1919 = (aux ())
in (match (_39_1919) with
| (e, c, g) -> begin
(let _39_1920 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _104_791 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.fprint1 "Introduced %s implicits in application\n" _104_791))
end else begin
()
end
in (let c = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (let _39_1927 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_796 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _104_795 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _104_794 = (let _104_793 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _104_793 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.fprint3 "(%s) About to check %s against expected typ %s\n" _104_796 _104_795 _104_794))))
end else begin
()
end
in (let _39_1932 = (comp_check_expected_typ env0 e c)
in (match (_39_1932) with
| (e, c, g') -> begin
(let _104_797 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _104_797))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let _39_1939 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_1939) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _39_1944 = (tc_exp env1 e1)
in (match (_39_1944) with
| (e1, c1, g1) -> begin
(let _39_1951 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _104_798 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_104_798, res_t)))
end)
in (match (_39_1951) with
| (env_branches, res_t) -> begin
(let guard_x = (let _104_800 = (FStar_All.pipe_left (fun _104_799 -> Some (_104_799)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _104_800))
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (let _39_1968 = (let _39_1965 = (FStar_List.fold_right (fun _39_1959 _39_1962 -> (match ((_39_1959, _39_1962)) with
| ((_39_1955, f, c, g), (caccum, gaccum)) -> begin
(let _104_803 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _104_803))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_39_1965) with
| (cases, g) -> begin
(let _104_804 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_104_804, g))
end))
in (match (_39_1968) with
| (c_branches, g_branches) -> begin
(let _39_1969 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_808 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_807 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _104_806 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _104_805 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.fprint4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _104_808 _104_807 _104_806 _104_805)))))
end else begin
()
end
in (let cres = (let _104_811 = (let _104_810 = (FStar_All.pipe_left (fun _104_809 -> Some (_104_809)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_104_810, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _104_811))
in (let e = (let _104_818 = (w cres)
in (let _104_817 = (let _104_816 = (let _104_815 = (FStar_List.map (fun _39_1979 -> (match (_39_1979) with
| (f, _39_1974, _39_1976, _39_1978) -> begin
f
end)) t_eqns)
in (e1, _104_815))
in (FStar_Absyn_Syntax.mk_Exp_match _104_816))
in (FStar_All.pipe_left _104_818 _104_817)))
in (let _104_820 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _104_819 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_104_820, cres, _104_819))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_1984; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| FStar_Util.Inr (_39_1997) -> begin
true
end
| _39_2000 -> begin
false
end)
in (let _39_2005 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_2005) with
| (env1, _39_2004) -> begin
(let _39_2018 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _39_2008 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _104_821 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _104_821))
end else begin
(let _39_2011 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_39_2011) with
| (t, f) -> begin
(let _39_2012 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _104_823 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _104_822 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "(%s) Checked type annotation %s\n" _104_823 _104_822)))
end else begin
()
end
in (let t = (norm_t env1 t)
in (let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end
end)
in (match (_39_2018) with
| (f, env1) -> begin
(let _39_2024 = (tc_exp (let _39_2019 = env1
in {FStar_Tc_Env.solver = _39_2019.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2019.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2019.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2019.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2019.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2019.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2019.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2019.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2019.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2019.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2019.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2019.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2019.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2019.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _39_2019.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2019.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2019.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2019.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2019.FStar_Tc_Env.default_effects}) e1)
in (match (_39_2024) with
| (e1, c1, g1) -> begin
(let _39_2028 = (let _104_827 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _39_2025 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _104_827 e1 c1 f))
in (match (_39_2028) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_39_2030) -> begin
(let _39_2041 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
(let _39_2034 = (let _104_828 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _104_828 c1))
in (match (_39_2034) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(let _39_2035 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _104_829 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _104_829 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _104_830 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_104_830, c1)))
end
end))
end else begin
(let _39_2037 = (let _104_831 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.discharge_guard env _104_831))
in (let _104_832 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _104_832)))
end
in (match (_39_2041) with
| (e2, c1) -> begin
(let _39_2046 = if env.FStar_Tc_Env.generalize then begin
(let _104_833 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _104_833))
end else begin
(x, e1, c1)
end
in (match (_39_2046) with
| (_39_2043, e1, c1) -> begin
(let cres = (let _104_834 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_834))
in (let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _104_835 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _104_835 (None, cres)))
end
in (let _39_2049 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _104_844 = (let _104_843 = (w cres)
in (let _104_842 = (let _104_841 = (let _104_840 = (let _104_839 = (let _104_838 = (FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1))
in (_104_838)::[])
in (false, _104_839))
in (_104_840, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _104_841))
in (FStar_All.pipe_left _104_843 _104_842)))
in (_104_844, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (let _39_2057 = (let _104_845 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _104_845 e2))
in (match (_39_2057) with
| (e2, c2, g2) -> begin
(let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _104_853 = (w cres)
in (let _104_852 = (let _104_851 = (let _104_850 = (let _104_849 = (let _104_848 = (FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1))
in (_104_848)::[])
in (false, _104_849))
in (_104_850, e2))
in (FStar_Absyn_Syntax.mk_Exp_let _104_851))
in (FStar_All.pipe_left _104_853 _104_852)))
in (let g2 = (let _104_862 = (let _104_855 = (let _104_854 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_104_854)::[])
in (FStar_Tc_Rel.close_guard _104_855))
in (let _104_861 = (let _104_860 = (let _104_859 = (let _104_858 = (let _104_857 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _104_857 e1))
in (FStar_All.pipe_left (fun _104_856 -> FStar_Tc_Rel.NonTrivial (_104_856)) _104_858))
in (FStar_Tc_Rel.guard_of_guard_formula _104_859))
in (FStar_Tc_Rel.imp_guard _104_860 g2))
in (FStar_All.pipe_left _104_862 _104_861)))
in (let guard = (let _104_863 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _104_863))
in (match (topt) with
| None -> begin
(let tres = cres.FStar_Absyn_Syntax.res_typ
in (let fvs = (FStar_Absyn_Util.freevars_typ tres)
in if (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs) then begin
(let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _39_2066 = (let _104_864 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _104_864))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _39_2069 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _39_2072), _39_2075) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(let env = (instantiate_both env)
in (let _39_2087 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_39_2087) with
| (env0, topt) -> begin
(let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _39_9 -> (match (_39_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_39_2096); FStar_Absyn_Syntax.lbtyp = _39_2094; FStar_Absyn_Syntax.lbeff = _39_2092; FStar_Absyn_Syntax.lbdef = _39_2090} -> begin
true
end
| _39_2100 -> begin
false
end))))
in (let _39_2127 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _39_2104 _39_2110 -> (match ((_39_2104, _39_2110)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_2107; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _39_2115 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_39_2115) with
| (_39_2112, t, check_t) -> begin
(let e = (FStar_Absyn_Util.unascribe e)
in (let t = if (not (check_t)) then begin
t
end else begin
if ((not (is_inner_let)) && (not (env.FStar_Tc_Env.generalize))) then begin
(let _39_2117 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _104_868 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint1 "Type %s is marked as no-generalize\n" _104_868))
end else begin
()
end
in t)
end else begin
(let _104_869 = (tc_typ_check_trivial (let _39_2119 = env0
in {FStar_Tc_Env.solver = _39_2119.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2119.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2119.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2119.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2119.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2119.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2119.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2119.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2119.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2119.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2119.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2119.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2119.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2119.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2119.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _39_2119.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2119.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2119.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2119.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _104_869 (norm_t env)))
end
end
in (let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)) then begin
(let _39_2122 = env
in {FStar_Tc_Env.solver = _39_2122.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2122.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2122.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2122.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2122.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2122.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2122.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2122.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2122.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2122.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2122.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2122.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2122.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2122.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2122.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2122.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2122.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2122.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2122.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_39_2127) with
| (lbs, env') -> begin
(let _39_2142 = (let _104_875 = (let _104_874 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _104_874 (FStar_List.map (fun _39_2131 -> (match (_39_2131) with
| (x, t, e) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (let _39_2133 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_873 = (FStar_Absyn_Print.lbname_to_string x)
in (let _104_872 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_871 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint3 "Checking %s = %s against type %s\n" _104_873 _104_872 _104_871))))
end else begin
()
end
in (let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (let _39_2139 = (tc_total_exp env' e)
in (match (_39_2139) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _104_875 FStar_List.unzip))
in (match (_39_2142) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (let _39_2161 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _104_877 = (FStar_List.map (fun _39_2147 -> (match (_39_2147) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_104_877, g_lbs))
end else begin
(let _39_2148 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _104_881 = (FStar_All.pipe_right lbs (FStar_List.map (fun _39_2153 -> (match (_39_2153) with
| (x, t, e) -> begin
(let _104_880 = (let _104_879 = (FStar_Absyn_Util.range_of_lb (x, t, e))
in (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) _104_879))
in (x, e, _104_880))
end))))
in (FStar_Tc_Util.generalize true env _104_881))
in (let _104_883 = (FStar_List.map (fun _39_2158 -> (match (_39_2158) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_104_883, FStar_Tc_Rel.trivial_guard))))
end
in (match (_39_2161) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(let cres = (let _104_884 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _104_884))
in (let _39_2163 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let _39_2165 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _104_888 = (let _104_887 = (w cres)
in (FStar_All.pipe_left _104_887 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_104_888, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(let _39_2181 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _39_2169 _39_2176 -> (match ((_39_2169, _39_2176)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_2173; FStar_Absyn_Syntax.lbdef = _39_2171}) -> begin
(let b = (binding_of_lb x t)
in (let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_39_2181) with
| (bindings, env) -> begin
(let _39_2185 = (tc_exp env e1)
in (match (_39_2185) with
| (e1, cres, g1) -> begin
(let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (let cres = (let _39_2189 = cres
in {FStar_Absyn_Syntax.eff_name = _39_2189.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _39_2189.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _39_2189.FStar_Absyn_Syntax.comp})
in (let e = (let _104_893 = (w cres)
in (FStar_All.pipe_left _104_893 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_39_2194) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _39_10 -> (match (_39_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_39_2206); FStar_Absyn_Syntax.lbtyp = _39_2204; FStar_Absyn_Syntax.lbeff = _39_2202; FStar_Absyn_Syntax.lbdef = _39_2200} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _39_2214; FStar_Absyn_Syntax.lbeff = _39_2212; FStar_Absyn_Syntax.lbdef = _39_2210} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _39_2223; FStar_Absyn_Syntax.lbeff = _39_2221; FStar_Absyn_Syntax.lbdef = _39_2219}) -> begin
(let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _39_2229 = (let _104_895 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _104_895))
in (e, cres, guard)))
end
| _39_2232 -> begin
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
and tc_eqn = (fun scrutinee_x pat_t env _39_2239 -> (match (_39_2239) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _39_2247 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_39_2247) with
| (bindings, exps, p) -> begin
(let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (let _39_2256 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _39_11 -> (match (_39_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _104_908 = (FStar_Absyn_Print.strBvd x)
in (let _104_907 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.fprint2 "Before tc ... pattern var %s  : %s\n" _104_908 _104_907)))
end
| _39_2255 -> begin
()
end))))
end else begin
()
end
in (let _39_2261 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_39_2261) with
| (env1, _39_2260) -> begin
(let env1 = (let _39_2262 = env1
in {FStar_Tc_Env.solver = _39_2262.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2262.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2262.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2262.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2262.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2262.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2262.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2262.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _39_2262.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2262.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2262.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2262.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2262.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2262.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2262.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2262.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2262.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2262.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2262.FStar_Tc_Env.default_effects})
in (let expected_pat_t = (FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _39_2267 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_911 = (FStar_Absyn_Print.exp_to_string e)
in (let _104_910 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.fprint2 "Checking pattern expression %s against expected type %s\n" _104_911 _104_910)))
end else begin
()
end
in (let _39_2272 = (tc_exp env1 e)
in (match (_39_2272) with
| (e, lc, g) -> begin
(let _39_2273 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_913 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _104_912 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.fprint2 "Pre-checked pattern expression %s at type %s\n" _104_913 _104_912)))
end else begin
()
end
in (let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (FStar_Tc_Rel.conj_guard g g')
in (let _39_2277 = (let _104_914 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _104_914))
in (let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (let _39_2280 = if (let _104_917 = (let _104_916 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _104_915 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _104_916 _104_915)))
in (FStar_All.pipe_left Prims.op_Negation _104_917)) then begin
(let _104_922 = (let _104_921 = (let _104_920 = (let _104_919 = (FStar_Absyn_Print.exp_to_string e')
in (let _104_918 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _104_919 _104_918)))
in (_104_920, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_104_921))
in (Prims.raise _104_922))
end else begin
()
end
in (let _39_2282 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_923 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.fprint1 "Done checking pattern expression %s\n" _104_923))
end else begin
()
end
in e)))))))
end))))))
in (let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (let _39_2293 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _39_12 -> (match (_39_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _104_926 = (FStar_Absyn_Print.strBvd x)
in (let _104_925 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.fprint2 "Pattern var %s  : %s\n" _104_926 _104_925)))
end
| _39_2292 -> begin
()
end))))
end else begin
()
end
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _39_2300 = (tc_pat true pat_t pattern)
in (match (_39_2300) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _39_2310 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(let _39_2307 = (let _104_927 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _104_927 e))
in (match (_39_2307) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_39_2310) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _104_929 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _104_928 -> Some (_104_928)) _104_929))
end)
in (let _39_2318 = (tc_exp pat_env branch)
in (match (_39_2318) with
| (branch, c, g_branch) -> begin
(let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _39_2323 = (let _104_930 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _104_930 FStar_Tc_Env.clear_expected_typ))
in (match (_39_2323) with
| (scrutinee_env, _39_2322) -> begin
(let c = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _39_2337 -> begin
(let clause = (let _104_934 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _104_933 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _104_934 _104_933 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _104_936 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _104_935 -> Some (_104_935)) _104_936))
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
(let _104_939 = (let _104_938 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _104_937 -> FStar_Tc_Rel.NonTrivial (_104_937)) _104_938))
in (FStar_Tc_Util.weaken_precondition env c _104_939))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun scrutinee f -> (let disc = (let _104_946 = (let _104_944 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _104_944))
in (let _104_945 = (FStar_Absyn_Syntax.range_of_lid f.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_left _104_946 _104_945)))
in (let disc = (let _104_949 = (let _104_948 = (let _104_947 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_104_947)::[])
in (disc, _104_948))
in (FStar_Absyn_Syntax.mk_Exp_app _104_949 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun scrutinee pat_exp -> (let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Absyn_Syntax.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_39_2395) -> begin
(let _104_958 = (let _104_957 = (let _104_956 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _104_955 = (let _104_954 = (FStar_Absyn_Syntax.varg pat_exp)
in (_104_954)::[])
in (_104_956)::_104_955))
in (FStar_Absyn_Util.teq, _104_957))
in (FStar_Absyn_Syntax.mk_Typ_app _104_958 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _39_2399) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _39_2412); FStar_Absyn_Syntax.tk = _39_2409; FStar_Absyn_Syntax.pos = _39_2407; FStar_Absyn_Syntax.fvs = _39_2405; FStar_Absyn_Syntax.uvs = _39_2403}, args) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _104_966 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_39_2423) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in (let sub_term = (let _104_964 = (let _104_963 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _104_962 = (let _104_961 = (FStar_Absyn_Syntax.varg scrutinee)
in (_104_961)::[])
in (_104_963, _104_962)))
in (FStar_Absyn_Syntax.mk_Exp_app _104_964 None f.FStar_Absyn_Syntax.p))
in (let _104_965 = (mk_guard sub_term ei)
in (_104_965)::[])))
end))))
in (FStar_All.pipe_right _104_966 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _39_2431 -> begin
(let _104_969 = (let _104_968 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _104_967 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _104_968 _104_967)))
in (FStar_All.failwith _104_969))
end)))
in (let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(let t = (mk_guard s pat)
in (let _39_2440 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_39_2440) with
| (t, _39_2439) -> begin
t
end)))
end)
in (let path_guard = (let _104_978 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _104_977 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _104_977)))))
in (FStar_All.pipe_right _104_978 FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _104_979 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _104_979))
in (let _39_2448 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _104_980 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.fprint1 "Carrying guard from match: %s\n") _104_980))
end else begin
()
end
in (let _104_982 = (let _104_981 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _104_981))
in ((pattern, when_clause, branch), path_guard, c, _104_982))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun env k -> (let _39_2454 = (tc_kind env k)
in (match (_39_2454) with
| (k, g) -> begin
(let _39_2455 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun env t -> (let _39_2462 = (tc_typ env t)
in (match (_39_2462) with
| (t, k, g) -> begin
(let _39_2463 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun env t k -> (let _39_2470 = (tc_typ_check env t k)
in (match (_39_2470) with
| (t, f) -> begin
(let _39_2471 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun env e -> (let _39_2478 = (tc_exp env e)
in (match (_39_2478) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _104_992 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _104_992 (norm_c env)))
in (match ((let _104_994 = (let _104_993 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _104_993))
in (FStar_Tc_Rel.sub_comp env c _104_994))) with
| Some (g') -> begin
(let _104_995 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _104_995))
end
| _39_2484 -> begin
(let _104_998 = (let _104_997 = (let _104_996 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_104_996, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_997))
in (Prims.raise _104_998))
end)))
end
end)))
and tc_ghost_exp = (fun env e -> (let _39_2490 = (tc_exp env e)
in (match (_39_2490) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let c = (let _104_1001 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _104_1001 (norm_c env)))
in (let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (let _39_2494 = env
in {FStar_Tc_Env.solver = _39_2494.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2494.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2494.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2494.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2494.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2494.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2494.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2494.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2494.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2494.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2494.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2494.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_2494.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_2494.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2494.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2494.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _39_2494.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2494.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2494.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _104_1002 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _104_1002))
end
| _39_2499 -> begin
(let _104_1005 = (let _104_1004 = (let _104_1003 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_104_1003, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_104_1004))
in (Prims.raise _104_1005))
end))))
end
end)))

let tc_tparams = (fun env tps -> (let _39_2505 = (tc_binders env tps)
in (match (_39_2505) with
| (tps, env, g) -> begin
(let _39_2506 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _39_2525)::(FStar_Util.Inl (wp), _39_2520)::(FStar_Util.Inl (_39_2512), _39_2515)::[], _39_2529) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _39_2533 -> begin
(let _104_1019 = (let _104_1018 = (let _104_1017 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (let _104_1016 = (FStar_Absyn_Syntax.range_of_lid m)
in (_104_1017, _104_1016)))
in FStar_Absyn_Syntax.Error (_104_1018))
in (Prims.raise _104_1019))
end))

let rec tc_eff_decl = (fun env m -> (let _39_2539 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_39_2539) with
| (binders, env, g) -> begin
(let _39_2540 = (FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (let _39_2545 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_39_2545) with
| (a, kwp_a) -> begin
(let a_typ = (FStar_Absyn_Util.btvar_to_typ a)
in (let b = (let _104_1033 = (FStar_Absyn_Syntax.range_of_lid m.FStar_Absyn_Syntax.mname)
in (FStar_Absyn_Util.gen_bvar_p _104_1033 FStar_Absyn_Syntax.ktype))
in (let b_typ = (FStar_Absyn_Util.btvar_to_typ b)
in (let kwp_b = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b_typ)))::[]) kwp_a)
in (let kwlp_a = kwp_a
in (let kwlp_b = kwp_b
in (let a_kwp_b = (let _104_1036 = (let _104_1035 = (let _104_1034 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_104_1034)::[])
in (_104_1035, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1036 a_typ.FStar_Absyn_Syntax.pos))
in (let a_kwlp_b = a_kwp_b
in (let w = (fun k -> (let _104_1044 = (FStar_Absyn_Syntax.range_of_lid m.FStar_Absyn_Syntax.mname)
in (k _104_1044)))
in (let ret = (let expected_k = (let _104_1051 = (let _104_1050 = (let _104_1049 = (let _104_1048 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1047 = (let _104_1046 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_104_1046)::[])
in (_104_1048)::_104_1047))
in (_104_1049, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1050))
in (FStar_All.pipe_left w _104_1051))
in (let _104_1052 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _104_1052 (norm_t env))))
in (let bind_wp = (let expected_k = (let _104_1067 = (let _104_1066 = (let _104_1065 = (let _104_1064 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1063 = (let _104_1062 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1061 = (let _104_1060 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _104_1059 = (let _104_1058 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _104_1057 = (let _104_1056 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _104_1055 = (let _104_1054 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_104_1054)::[])
in (_104_1056)::_104_1055))
in (_104_1058)::_104_1057))
in (_104_1060)::_104_1059))
in (_104_1062)::_104_1061))
in (_104_1064)::_104_1063))
in (_104_1065, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1066))
in (FStar_All.pipe_left w _104_1067))
in (let _104_1068 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _104_1068 (norm_t env))))
in (let bind_wlp = (let expected_k = (let _104_1079 = (let _104_1078 = (let _104_1077 = (let _104_1076 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1075 = (let _104_1074 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1073 = (let _104_1072 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _104_1071 = (let _104_1070 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_104_1070)::[])
in (_104_1072)::_104_1071))
in (_104_1074)::_104_1073))
in (_104_1076)::_104_1075))
in (_104_1077, kwlp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1078))
in (FStar_All.pipe_left w _104_1079))
in (let _104_1080 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _104_1080 (norm_t env))))
in (let if_then_else = (let expected_k = (let _104_1091 = (let _104_1090 = (let _104_1089 = (let _104_1088 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1087 = (let _104_1086 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1085 = (let _104_1084 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _104_1083 = (let _104_1082 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1082)::[])
in (_104_1084)::_104_1083))
in (_104_1086)::_104_1085))
in (_104_1088)::_104_1087))
in (_104_1089, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1090))
in (FStar_All.pipe_left w _104_1091))
in (let _104_1092 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _104_1092 (norm_t env))))
in (let ite_wp = (let expected_k = (let _104_1101 = (let _104_1100 = (let _104_1099 = (let _104_1098 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1097 = (let _104_1096 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _104_1095 = (let _104_1094 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1094)::[])
in (_104_1096)::_104_1095))
in (_104_1098)::_104_1097))
in (_104_1099, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1100))
in (FStar_All.pipe_left w _104_1101))
in (let _104_1102 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _104_1102 (norm_t env))))
in (let ite_wlp = (let expected_k = (let _104_1109 = (let _104_1108 = (let _104_1107 = (let _104_1106 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1105 = (let _104_1104 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_104_1104)::[])
in (_104_1106)::_104_1105))
in (_104_1107, kwlp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1108))
in (FStar_All.pipe_left w _104_1109))
in (let _104_1110 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _104_1110 (norm_t env))))
in (let wp_binop = (let expected_k = (let _104_1122 = (let _104_1121 = (let _104_1120 = (let _104_1119 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1118 = (let _104_1117 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _104_1116 = (let _104_1115 = (let _104_1112 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _104_1112))
in (let _104_1114 = (let _104_1113 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1113)::[])
in (_104_1115)::_104_1114))
in (_104_1117)::_104_1116))
in (_104_1119)::_104_1118))
in (_104_1120, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1121))
in (FStar_All.pipe_left w _104_1122))
in (let _104_1123 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _104_1123 (norm_t env))))
in (let wp_as_type = (let expected_k = (let _104_1130 = (let _104_1129 = (let _104_1128 = (let _104_1127 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1126 = (let _104_1125 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1125)::[])
in (_104_1127)::_104_1126))
in (_104_1128, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1129))
in (FStar_All.pipe_left w _104_1130))
in (let _104_1131 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _104_1131 (norm_t env))))
in (let close_wp = (let expected_k = (let _104_1140 = (let _104_1139 = (let _104_1138 = (let _104_1137 = (FStar_Absyn_Syntax.t_binder b)
in (let _104_1136 = (let _104_1135 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1134 = (let _104_1133 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_104_1133)::[])
in (_104_1135)::_104_1134))
in (_104_1137)::_104_1136))
in (_104_1138, kwp_b))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1139))
in (FStar_All.pipe_left w _104_1140))
in (let _104_1141 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _104_1141 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _104_1154 = (let _104_1153 = (let _104_1152 = (let _104_1151 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1150 = (let _104_1149 = (let _104_1148 = (let _104_1147 = (let _104_1146 = (let _104_1145 = (let _104_1144 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_104_1144)::[])
in (_104_1145, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1146))
in (FStar_All.pipe_left w _104_1147))
in (FStar_Absyn_Syntax.null_t_binder _104_1148))
in (_104_1149)::[])
in (_104_1151)::_104_1150))
in (_104_1152, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1153))
in (FStar_All.pipe_left w _104_1154))
in (let _104_1155 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _104_1155 (norm_t env))))
in (let _39_2579 = (let expected_k = (let _104_1164 = (let _104_1163 = (let _104_1162 = (let _104_1161 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1160 = (let _104_1159 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _104_1158 = (let _104_1157 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1157)::[])
in (_104_1159)::_104_1158))
in (_104_1161)::_104_1160))
in (_104_1162, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1163))
in (FStar_All.pipe_left w _104_1164))
in (let _104_1168 = (let _104_1165 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _104_1165 (norm_t env)))
in (let _104_1167 = (let _104_1166 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _104_1166 (norm_t env)))
in (_104_1168, _104_1167))))
in (match (_39_2579) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (let _104_1173 = (let _104_1172 = (let _104_1171 = (let _104_1170 = (FStar_Absyn_Syntax.t_binder a)
in (_104_1170)::[])
in (_104_1171, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1172))
in (FStar_All.pipe_left w _104_1173))
in (let _104_1174 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _104_1174 (norm_t env))))
in (let trivial_wp = (let expected_k = (let _104_1181 = (let _104_1180 = (let _104_1179 = (let _104_1178 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1177 = (let _104_1176 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_104_1176)::[])
in (_104_1178)::_104_1177))
in (_104_1179, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1180))
in (FStar_All.pipe_left w _104_1181))
in (let _104_1182 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _104_1182 (norm_t env))))
in {FStar_Absyn_Syntax.mname = m.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = m.FStar_Absyn_Syntax.qualifiers; FStar_Absyn_Syntax.signature = mk; FStar_Absyn_Syntax.ret = ret; FStar_Absyn_Syntax.bind_wp = bind_wp; FStar_Absyn_Syntax.bind_wlp = bind_wlp; FStar_Absyn_Syntax.if_then_else = if_then_else; FStar_Absyn_Syntax.ite_wp = ite_wp; FStar_Absyn_Syntax.ite_wlp = ite_wlp; FStar_Absyn_Syntax.wp_binop = wp_binop; FStar_Absyn_Syntax.wp_as_type = wp_as_type; FStar_Absyn_Syntax.close_wp = close_wp; FStar_Absyn_Syntax.close_wp_t = close_wp_t; FStar_Absyn_Syntax.assert_p = assert_p; FStar_Absyn_Syntax.assume_p = assume_p; FStar_Absyn_Syntax.null_wp = null_wp; FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl = (fun env se deserialized -> (match (se) with
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
(let _39_2598 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _39_2600 = (let _104_1186 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _104_1186 Prims.ignore))
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
(let _39_2615 = (let _104_1187 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _104_1187))
in (match (_39_2615) with
| (a, kwp_a_src) -> begin
(let _39_2618 = (let _104_1188 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _104_1188))
in (match (_39_2618) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _104_1192 = (let _104_1191 = (let _104_1190 = (let _104_1189 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _104_1189))
in FStar_Util.Inl (_104_1190))
in (_104_1191)::[])
in (FStar_Absyn_Util.subst_kind _104_1192 kwp_b_tgt))
in (let expected_k = (let _104_1198 = (let _104_1197 = (let _104_1196 = (let _104_1195 = (FStar_Absyn_Syntax.t_binder a)
in (let _104_1194 = (let _104_1193 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_104_1193)::[])
in (_104_1195)::_104_1194))
in (_104_1196, kwp_a_tgt))
in (FStar_Absyn_Syntax.mk_Kind_arrow _104_1197))
in (FStar_All.pipe_right r _104_1198))
in (let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _39_2622 = sub
in {FStar_Absyn_Syntax.source = _39_2622.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _39_2622.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_2639 = (tc_tparams env tps)
in (match (_39_2639) with
| (tps, env) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _39_2642 -> begin
(tc_kind_trivial env k)
end)
in (let _39_2644 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _104_1201 = (FStar_Absyn_Print.sli lid)
in (let _104_1200 = (let _104_1199 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _104_1199))
in (FStar_Util.fprint2 "Checked %s at kind %s\n" _104_1201 _104_1200)))
end else begin
()
end
in (let k = (norm_k env k)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _39_2662 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_39_2657); FStar_Absyn_Syntax.tk = _39_2655; FStar_Absyn_Syntax.pos = _39_2653; FStar_Absyn_Syntax.fvs = _39_2651; FStar_Absyn_Syntax.uvs = _39_2649} -> begin
(let _104_1202 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _104_1202))
end
| _39_2661 -> begin
()
end)
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _39_2675 = (tc_tparams env tps)
in (match (_39_2675) with
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
in (let _39_2690 = (tc_tparams env tps)
in (match (_39_2690) with
| (tps, env) -> begin
(let _39_2693 = (tc_comp env c)
in (match (_39_2693) with
| (c, g) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _39_13 -> (match (_39_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _104_1205 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _104_1204 -> Some (_104_1204)))
in FStar_Absyn_Syntax.DefaultEffect (_104_1205)))
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
in (let _39_2713 = (tc_tparams env tps)
in (match (_39_2713) with
| (tps, env') -> begin
(let _39_2719 = (let _104_1209 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _104_1209 (fun _39_2716 -> (match (_39_2716) with
| (t, k) -> begin
(let _104_1208 = (norm_t env' t)
in (let _104_1207 = (norm_k env' k)
in (_104_1208, _104_1207)))
end))))
in (match (_39_2719) with
| (t, k1) -> begin
(let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _39_2722 -> begin
(let k2 = (let _104_1210 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _104_1210 (norm_k env)))
in (let _39_2724 = (let _104_1211 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _104_1211))
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
in (let _39_2744 = (tc_binders env tps)
in (match (_39_2744) with
| (tps, env, g) -> begin
(let tycon = (tname, tps, k)
in (let _39_2746 = (FStar_Tc_Util.discharge_guard env g)
in (let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _39_2758 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _39_2755 -> begin
([], t)
end)
in (match (_39_2758) with
| (formals, result_t) -> begin
(let cardinality_and_positivity_check = (fun formal -> (let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _39_2766 -> (match (_39_2766) with
| (a, _39_2765) -> begin
(match (a) with
| FStar_Util.Inl (_39_2768) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _104_1219 = (FStar_Absyn_Util.compress_typ t)
in _104_1219.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Absyn_Syntax.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _104_1225 = (let _104_1224 = (let _104_1223 = (let _104_1221 = (let _104_1220 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid _104_1220))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _104_1221 tname))
in (let _104_1222 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_104_1223, _104_1222)))
in FStar_Absyn_Syntax.Error (_104_1224))
in (Prims.raise _104_1225))
end)
end
| _39_2781 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(let _39_2784 = if (FStar_Options.warn_cardinality ()) then begin
(let _104_1226 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _104_1226))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _104_1229 = (let _104_1228 = (let _104_1227 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_104_1227, r))
in FStar_Absyn_Syntax.Error (_104_1228))
in (Prims.raise _104_1229))
end else begin
()
end
end
in (let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_39_2788) -> begin
(let _39_2793 = (FStar_Absyn_Util.kind_formals k)
in (match (_39_2793) with
| (formals, _39_2792) -> begin
(check_positivity formals)
end))
end
| _39_2795 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(let _39_2802 = (let _104_1230 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _104_1230 FStar_Util.must))
in (match (_39_2802) with
| (formals, _39_2801) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (let _39_2803 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (let _39_2857 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _104_1234 = (let _104_1233 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _104_1233 Prims.fst))
in (FStar_List.forall2 (fun _39_2810 _39_2814 -> (match ((_39_2810, _39_2814)) with
| ((a, _39_2809), (b, _39_2813)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _39_2822; FStar_Absyn_Syntax.pos = _39_2820; FStar_Absyn_Syntax.fvs = _39_2818; FStar_Absyn_Syntax.uvs = _39_2816}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _39_2837; FStar_Absyn_Syntax.pos = _39_2835; FStar_Absyn_Syntax.fvs = _39_2833; FStar_Absyn_Syntax.uvs = _39_2831}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _39_2846 -> begin
false
end)
end)) _104_1234 tps))))) then begin
(let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _39_2849 -> begin
(let _39_2853 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_39_2853) with
| (_39_2851, expected_args) -> begin
(let _104_1235 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _104_1235 expected_args))
end))
end)
in (let _104_1241 = (let _104_1240 = (let _104_1239 = (let _104_1237 = (let _104_1236 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid _104_1236))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _104_1237 result_t expected_t))
in (let _104_1238 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_104_1239, _104_1238)))
in FStar_Absyn_Syntax.Error (_104_1240))
in (Prims.raise _104_1241)))
end else begin
()
end
end
| _39_2856 -> begin
(let _104_1248 = (let _104_1247 = (let _104_1246 = (let _104_1244 = (let _104_1242 = (FStar_Absyn_Syntax.range_of_lid lid)
in (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid _104_1242))
in (let _104_1243 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _104_1244 result_t _104_1243)))
in (let _104_1245 = (FStar_Absyn_Syntax.range_of_lid lid)
in (_104_1246, _104_1245)))
in FStar_Absyn_Syntax.Error (_104_1247))
in (Prims.raise _104_1248))
end)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _39_2861 = if (log env) then begin
(let _104_1250 = (let _104_1249 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Absyn_Syntax.str _104_1249))
in (FStar_All.pipe_left FStar_Util.print_string _104_1250))
end else begin
()
end
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let t = (let _104_1251 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _104_1251 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _39_2871 = (FStar_Tc_Util.check_uvars r t)
in (let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _39_2875 = if (log env) then begin
(let _104_1253 = (let _104_1252 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Absyn_Syntax.str _104_1252))
in (FStar_All.pipe_left FStar_Util.print_string _104_1253))
end else begin
()
end
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let phi = (let _104_1254 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _104_1254 (norm_t env)))
in (let _39_2885 = (FStar_Tc_Util.check_uvars r phi)
in (let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_2938 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _39_2898 lb -> (match (_39_2898) with
| (gen, lbs) -> begin
(let _39_2935 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_39_2907); FStar_Absyn_Syntax.lbtyp = _39_2905; FStar_Absyn_Syntax.lbeff = _39_2903; FStar_Absyn_Syntax.lbdef = _39_2901} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _39_2912; FStar_Absyn_Syntax.lbdef = e} -> begin
(let _39_2932 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _39_2920) -> begin
(let _39_2923 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _104_1257 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.fprint2 "Using annotation %s for let binding %s\n" _104_1257 l.FStar_Absyn_Syntax.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _104_1258 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _104_1258))
end
| _39_2927 -> begin
(let _39_2928 = if (not (deserialized)) then begin
(let _104_1260 = (let _104_1259 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _104_1259))
in (FStar_All.pipe_left FStar_Util.print_string _104_1260))
end else begin
()
end
in (let _104_1261 = (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))
in (false, _104_1261)))
end))
end)
in (match (_39_2932) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_39_2935) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_39_2938) with
| (generalize, lbs') -> begin
(let lbs' = (FStar_List.rev lbs')
in (let e = (let _104_1266 = (let _104_1265 = (let _104_1264 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _104_1264 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit)))
in (((Prims.fst lbs), lbs'), _104_1265))
in (FStar_Absyn_Syntax.mk_Exp_let _104_1266 None r))
in (let _39_2973 = (match ((tc_exp (let _39_2941 = env
in {FStar_Tc_Env.solver = _39_2941.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_2941.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_2941.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_2941.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_2941.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_2941.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_2941.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_2941.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_2941.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_2941.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_2941.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_2941.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _39_2941.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_2941.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_2941.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_2941.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _39_2941.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _39_2941.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _39_2941.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _39_2950; FStar_Absyn_Syntax.pos = _39_2948; FStar_Absyn_Syntax.fvs = _39_2946; FStar_Absyn_Syntax.uvs = _39_2944}, _39_2957, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_39_2961, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _39_2967 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _39_2970 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_39_2973) with
| (se, lbs) -> begin
(let _39_2979 = if (log env) then begin
(let _104_1272 = (let _104_1271 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _104_1268 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _104_1268))) with
| None -> begin
true
end
| _39_2977 -> begin
false
end)
in if should_log then begin
(let _104_1270 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _104_1269 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _104_1270 _104_1269)))
end else begin
""
end))))
in (FStar_All.pipe_right _104_1271 (FStar_String.concat "\n")))
in (FStar_Util.fprint1 "%s\n" _104_1272))
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
in (let _39_2991 = (tc_exp env e)
in (match (_39_2991) with
| (e, c, g1) -> begin
(let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _39_2997 = (let _104_1276 = (let _104_1273 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_104_1273))
in (let _104_1275 = (let _104_1274 = (c.FStar_Absyn_Syntax.comp ())
in (e, _104_1274))
in (check_expected_effect env _104_1276 _104_1275)))
in (match (_39_2997) with
| (e, _39_2995, g) -> begin
(let _39_2998 = (let _104_1277 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _104_1277))
in (let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _39_3017 = (FStar_All.pipe_right ses (FStar_List.partition (fun _39_14 -> (match (_39_14) with
| FStar_Absyn_Syntax.Sig_tycon (_39_3011) -> begin
true
end
| _39_3014 -> begin
false
end))))
in (match (_39_3017) with
| (tycons, rest) -> begin
(let _39_3026 = (FStar_All.pipe_right rest (FStar_List.partition (fun _39_15 -> (match (_39_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_39_3020) -> begin
true
end
| _39_3023 -> begin
false
end))))
in (match (_39_3026) with
| (abbrevs, rest) -> begin
(let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _39_16 -> (match (_39_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _104_1281 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _104_1281 Prims.fst))
end
| _39_3038 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _39_3041 -> begin
(FStar_All.failwith "impossible")
end))))
in (let _39_3045 = (FStar_List.split recs)
in (match (_39_3045) with
| (recs, abbrev_defs) -> begin
(let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _104_1282 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _104_1282))
end else begin
""
end
in (let _39_3047 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (let _39_3054 = (tc_decls false env tycons deserialized)
in (match (_39_3054) with
| (tycons, _39_3051, _39_3053) -> begin
(let _39_3060 = (tc_decls false env recs deserialized)
in (match (_39_3060) with
| (recs, _39_3057, _39_3059) -> begin
(let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (let _39_3067 = (tc_decls false env1 rest deserialized)
in (match (_39_3067) with
| (rest, _39_3064, _39_3066) -> begin
(let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(let tt = (let _104_1285 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _104_1285))
in (let _39_3083 = (tc_typ_trivial env1 tt)
in (match (_39_3083) with
| (tt, _39_3082) -> begin
(let _39_3092 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _39_3089 -> begin
([], tt)
end)
in (match (_39_3092) with
| (tps, t) -> begin
(let _104_1287 = (let _104_1286 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _104_1286, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_104_1287))
end))
end)))
end
| _39_3094 -> begin
(let _104_1289 = (let _104_1288 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _104_1288))
in (FStar_All.failwith _104_1289))
end)) recs abbrev_defs)
in (let _39_3096 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
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
and tc_decls = (fun for_export env ses deserialized -> (let _39_3120 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _39_3107 se -> (match (_39_3107) with
| (ses, all_non_private, env) -> begin
(let _39_3109 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _104_1297 = (let _104_1296 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _104_1296))
in (FStar_Util.print_string _104_1297))
end else begin
()
end
in (let _39_3113 = (tc_decl env se deserialized)
in (match (_39_3113) with
| (se, env) -> begin
(let _39_3114 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in (let non_private_decls = if for_export then begin
(non_private env se)
end else begin
[]
end
in ((se)::ses, (non_private_decls)::all_non_private, env)))
end)))
end)) ([], [], env)))
in (match (_39_3120) with
| (ses, all_non_private, env) -> begin
(let _104_1298 = (FStar_All.pipe_right (FStar_List.rev all_non_private) FStar_List.flatten)
in ((FStar_List.rev ses), _104_1298, env))
end)))
and non_private = (fun env se -> (let is_private = (fun quals -> (FStar_List.contains FStar_Absyn_Syntax.Private quals))
in (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _39_3128, _39_3130) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_tycon (_39_3134, _39_3136, _39_3138, _39_3140, _39_3142, quals, r) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (l, bs, k, t, quals, r) -> begin
if (is_private quals) then begin
(FStar_Absyn_Syntax.Sig_tycon ((l, bs, k, [], [], (FStar_Absyn_Syntax.Assumption)::quals, r)))::[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_assume (_39_3156, _39_3158, quals, _39_3161) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_val_decl (_39_3165, _39_3167, quals, _39_3170) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_main (_39_3174) -> begin
[]
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_datacon (_39_3192) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, _39_3198) -> begin
(let check_priv = (fun lbs -> (let is_priv = (fun _39_17 -> (match (_39_17) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _39_3209; FStar_Absyn_Syntax.lbeff = _39_3207; FStar_Absyn_Syntax.lbdef = _39_3205} -> begin
(match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some (_39_3214, qs) -> begin
(FStar_List.contains FStar_Absyn_Syntax.Private qs)
end
| _39_3219 -> begin
false
end)
end
| _39_3221 -> begin
false
end))
in (let some_priv = (FStar_All.pipe_right lbs (FStar_Util.for_some is_priv))
in if some_priv then begin
if (FStar_All.pipe_right lbs (FStar_Util.for_some (fun x -> (let _104_1308 = (is_priv x)
in (FStar_All.pipe_right _104_1308 Prims.op_Negation))))) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Some but not all functions in this mutually recursive nest are marked private", r))))
end else begin
true
end
end else begin
false
end)))
in (let _39_3228 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.partition (fun lb -> ((FStar_Absyn_Util.is_pure_or_ghost_function lb.FStar_Absyn_Syntax.lbtyp) && (let _104_1310 = (FStar_Absyn_Util.is_lemma lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_left Prims.op_Negation _104_1310))))))
in (match (_39_3228) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_39_3232::_39_3230, _39_3237::_39_3235) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_39_3243::_39_3241, []) -> begin
if (check_priv pure_funs) then begin
[]
end else begin
(se)::[]
end
end
| ([], _39_3251::_39_3249) -> begin
if (check_priv rest) then begin
[]
end else begin
(FStar_All.pipe_right rest (FStar_List.collect (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_39_3256) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (l) -> begin
(let _104_1314 = (let _104_1313 = (let _104_1312 = (FStar_Absyn_Syntax.range_of_lid l)
in (l, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::[], _104_1312))
in FStar_Absyn_Syntax.Sig_val_decl (_104_1313))
in (_104_1314)::[])
end))))
end
end
| ([], []) -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end)))

let get_exports = (fun env modul non_private_decls -> (let assume_vals = (fun decls -> (FStar_All.pipe_right decls (FStar_List.map (fun _39_18 -> (match (_39_18) with
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((lid, t, (FStar_Absyn_Syntax.Assumption)::quals, r))
end
| s -> begin
s
end)))))
in if modul.FStar_Absyn_Syntax.is_interface then begin
non_private_decls
end else begin
(let exports = (let _104_1326 = (FStar_Tc_Env.modules env)
in (FStar_Util.find_map _104_1326 (fun m -> if (m.FStar_Absyn_Syntax.is_interface && (FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name m.FStar_Absyn_Syntax.name)) then begin
(let _104_1325 = (FStar_All.pipe_right m.FStar_Absyn_Syntax.exports assume_vals)
in Some (_104_1325))
end else begin
None
end)))
in (match (exports) with
| None -> begin
non_private_decls
end
| Some (e) -> begin
e
end))
end))

let tc_partial_modul = (fun env modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let msg = (Prims.strcat "Internals for " name)
in (let env = (let _39_3285 = env
in (let _104_1331 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)))
in {FStar_Tc_Env.solver = _39_3285.FStar_Tc_Env.solver; FStar_Tc_Env.range = _39_3285.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _39_3285.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _39_3285.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _39_3285.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _39_3285.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _39_3285.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _39_3285.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _39_3285.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _39_3285.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _39_3285.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _39_3285.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _39_3285.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _39_3285.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _39_3285.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _39_3285.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _39_3285.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _104_1331; FStar_Tc_Env.default_effects = _39_3285.FStar_Tc_Env.default_effects}))
in (let _39_3288 = if (not ((FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (let _39_3294 = (tc_decls true env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_39_3294) with
| (ses, non_private_decls, env) -> begin
((let _39_3295 = modul
in {FStar_Absyn_Syntax.name = _39_3295.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _39_3295.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _39_3295.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _39_3295.FStar_Absyn_Syntax.is_deserialized}), non_private_decls, env)
end))))))))

let tc_more_partial_modul = (fun env modul decls -> (let _39_3303 = (tc_decls true env decls false)
in (match (_39_3303) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _39_3304 = modul
in {FStar_Absyn_Syntax.name = _39_3304.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _39_3304.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _39_3304.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _39_3304.FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun env modul npds -> (let exports = (get_exports env modul npds)
in (let modul = (let _39_3311 = modul
in {FStar_Absyn_Syntax.name = _39_3311.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _39_3311.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (let env = (FStar_Tc_Env.finish_module env modul)
in (let _39_3321 = if (not ((FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(let _39_3315 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str))
in (let _39_3317 = if ((not (modul.FStar_Absyn_Syntax.is_interface)) || (let _104_1344 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str _104_1344))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
end else begin
()
end
in (let _39_3319 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _104_1345 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _104_1345 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

let tc_modul = (fun env modul -> (let _39_3328 = (tc_partial_modul env modul)
in (match (_39_3328) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_Tc_Env.push_sigelt en elt)
in (let _39_3335 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _104_1358 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _104_1358 m)))))

let check_module = (fun env m -> (let _39_3340 = if ((let _104_1363 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _104_1363)) <> 0) then begin
(let _104_1364 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.fprint2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _104_1364))
end else begin
()
end
in (let _39_3353 = if m.FStar_Absyn_Syntax.is_deserialized then begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end else begin
(let _39_3345 = (tc_modul env m)
in (match (_39_3345) with
| (m, env) -> begin
(let _39_3349 = if (FStar_ST.read FStar_Options.serialize_mods) then begin
(let c_file_name = (let _104_1370 = (let _104_1369 = (let _104_1367 = (let _104_1366 = (let _104_1365 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _104_1365 "/"))
in (Prims.strcat _104_1366 FStar_Options.cache_dir))
in (Prims.strcat _104_1367 "/"))
in (let _104_1368 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (Prims.strcat _104_1369 _104_1368)))
in (Prims.strcat _104_1370 ".cache"))
in (let _39_3347 = (let _104_1373 = (let _104_1372 = (let _104_1371 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (Prims.strcat "Serializing module " _104_1371))
in (Prims.strcat _104_1372 "\n"))
in (FStar_Util.print_string _104_1373))
in (let _104_1374 = (FStar_Util.get_owriter c_file_name)
in (FStar_Absyn_SSyntax.serialize_modul _104_1374 m))))
end else begin
()
end
in (m, env))
end))
end
in (match (_39_3353) with
| (m, env) -> begin
(let _39_3354 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str) then begin
(let _104_1375 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.fprint1 "%s\n" _104_1375))
end else begin
()
end
in ((m)::[], env))
end))))




