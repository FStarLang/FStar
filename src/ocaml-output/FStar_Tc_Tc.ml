
open Prims
let syn' = (fun env k -> (let _145_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _145_11 (Some (k)))))

let log = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _145_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _145_14))))))

let rng = (fun env -> (FStar_Tc_Env.get_range env))

let instantiate_both = (fun env -> (let _54_24 = env
in {FStar_Tc_Env.solver = _54_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _54_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_24.FStar_Tc_Env.default_effects}))

let no_inst = (fun env -> (let _54_27 = env
in {FStar_Tc_Env.solver = _54_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _54_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_27.FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _145_30 = (let _145_29 = (let _145_28 = (let _145_27 = (let _145_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _145_25 -> FStar_Util.Inl (_145_25)) _145_26))
in (_145_27, Some (FStar_Absyn_Syntax.Implicit)))
in (_145_28)::((FStar_Absyn_Syntax.varg v))::((FStar_Absyn_Syntax.varg tl))::[])
in (FStar_Absyn_Util.lex_pair, _145_29))
in (FStar_Absyn_Syntax.mk_Exp_app _145_30 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

let is_eq = (fun _54_1 -> (match (_54_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _54_37 -> begin
false
end))

let steps = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)

let whnf = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))

let norm_t = (fun env t -> (let _145_43 = (steps env)
in (FStar_Tc_Normalize.norm_typ _145_43 env t)))

let norm_k = (fun env k -> (let _145_48 = (steps env)
in (FStar_Tc_Normalize.norm_kind _145_48 env k)))

let norm_c = (fun env c -> (let _145_53 = (steps env)
in (FStar_Tc_Normalize.norm_comp _145_53 env c)))

let fxv_check = (fun head env kt fvs -> (let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _145_72 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _145_72))
end
| FStar_Util.Inr (t) -> begin
(let _145_73 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _145_73))
end)
in (let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (norm)) then begin
(aux true kt)
end else begin
(let fail = (fun _54_61 -> (match (()) with
| () -> begin
(let escaping = (let _145_78 = (let _145_77 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _145_77 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _145_78 (FStar_String.concat ", ")))
in (let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _145_79 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _145_79))
end else begin
(let _145_80 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _145_80))
end
in (let _145_83 = (let _145_82 = (let _145_81 = (FStar_Tc_Env.get_range env)
in (msg, _145_81))
in FStar_Absyn_Syntax.Error (_145_82))
in (Prims.raise _145_83))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _54_71 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _54_78 -> begin
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

let maybe_make_subst = (fun _54_2 -> (match (_54_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _54_99 -> begin
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
(let _145_94 = (let _145_93 = (let _145_92 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _145_92))
in FStar_Util.Inl (_145_93))
in (_145_94)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _145_97 = (let _145_96 = (let _145_95 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _145_95))
in FStar_Util.Inr (_145_96))
in (_145_97)::s)
end
end
| _54_114 -> begin
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
| _54_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

let set_lcomp_result = (fun lc t -> (let _54_132 = lc
in {FStar_Absyn_Syntax.eff_name = _54_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _54_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _54_134 -> (match (()) with
| () -> begin
(let _145_106 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _145_106 t))
end))}))

let value_check_expected_typ = (fun env e tlc -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _145_113 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _145_113))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Absyn_Syntax.res_typ
in (let _54_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _54_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_115 = (FStar_Absyn_Print.typ_to_string t)
in (let _145_114 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _145_115 _145_114)))
end else begin
()
end
in (let _54_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_54_151) with
| (e, g) -> begin
(let _54_154 = (let _145_121 = (FStar_All.pipe_left (fun _145_120 -> Some (_145_120)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _145_121 env e lc g))
in (match (_54_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_54_158) with
| (e, lc, g) -> begin
(let _54_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_122 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _145_122))
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

let check_expected_effect = (fun env copt _54_171 -> (match (_54_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_54_173) -> begin
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
(let _145_135 = (norm_c env c)
in (e, _145_135, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _54_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_138 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _145_137 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _145_136 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _145_138 _145_137 _145_136))))
end else begin
()
end
in (let c = (norm_c env c)
in (let expected_c' = (let _145_139 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _145_139))
in (let _54_195 = (let _145_140 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _145_140))
in (match (_54_195) with
| (e, _54_193, g) -> begin
(let _54_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_142 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _145_141 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _145_142 _145_141)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun env _54_202 -> (match (_54_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _145_148 = (let _145_147 = (let _145_146 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _145_145 = (FStar_Tc_Env.get_range env)
in (_145_146, _145_145)))
in FStar_Absyn_Syntax.Error (_145_147))
in (Prims.raise _145_148))
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
(let _145_155 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _145_155))
end))

let with_implicits = (fun imps _54_220 -> (match (_54_220) with
| (e, l, g) -> begin
(e, l, (let _54_221 = g
in {FStar_Tc_Rel.guard_f = _54_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _54_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun u g -> (let _54_225 = g
in {FStar_Tc_Rel.guard_f = _54_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _54_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

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
(let _54_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_208 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _145_207 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _145_208 _145_207)))
end else begin
()
end
in (let _54_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_54_249) with
| (env, _54_248) -> begin
(let _54_252 = (tc_args env args)
in (match (_54_252) with
| (args, g) -> begin
(let _145_210 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_145_210, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _54_263; FStar_Absyn_Syntax.pos = _54_261; FStar_Absyn_Syntax.fvs = _54_259; FStar_Absyn_Syntax.uvs = _54_257}) -> begin
(let _54_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_54_272) with
| (_54_269, binders, body) -> begin
(let _54_275 = (tc_args env args)
in (match (_54_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _145_214 = (let _145_213 = (let _145_212 = (let _145_211 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _145_211))
in (_145_212, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_213))
in (Prims.raise _145_214))
end else begin
(let _54_308 = (FStar_List.fold_left2 (fun _54_279 b a -> (match (_54_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(let _54_289 = (let _145_218 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _145_218))
in (match (_54_289) with
| (t, g) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (subst, ((FStar_Absyn_Syntax.targ t))::args, (g)::guards))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(let env = (let _145_219 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _145_219))
in (let _54_301 = (tc_ghost_exp env e)
in (match (_54_301) with
| (e, _54_299, g) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (subst, ((FStar_Absyn_Syntax.varg e))::args, (g)::guards))
end)))
end
| _54_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_54_308) with
| (subst, args, guards) -> begin
(let args = (FStar_List.rev args)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _145_222 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _145_222))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _54_319 = (tc_kind env k)
in (match (_54_319) with
| (k, f) -> begin
(let _54_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_54_322) with
| (args, g) -> begin
(let kabr = ((Prims.fst kabr), args)
in (let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _145_224 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _145_224))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _54_332 = (tc_binders env bs)
in (match (_54_332) with
| (bs, env, g) -> begin
(let _54_335 = (tc_kind env k)
in (match (_54_335) with
| (k, f) -> begin
(let f = (FStar_Tc_Rel.close_guard bs f)
in (let _145_227 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _145_226 = (FStar_Tc_Rel.conj_guard g f)
in (_145_227, _145_226))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _145_228 = (FStar_Tc_Util.new_kvar env)
in (_145_228, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun env x -> (let _54_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_54_342) with
| (t, g) -> begin
(let x = (let _54_343 = x
in {FStar_Absyn_Syntax.v = _54_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _54_343.FStar_Absyn_Syntax.p})
in (let env' = (maybe_push_binding env (FStar_Absyn_Syntax.v_binder x))
in (x, env', g)))
end)))
and tc_binders = (fun env bs -> (let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_Tc_Rel.trivial_guard)
end
| (b, imp)::bs -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _54_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_54_362) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _54_363 = a
in {FStar_Absyn_Syntax.v = _54_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _54_363.FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _54_370 = (aux env' bs)
in (match (_54_370) with
| (bs, env', g') -> begin
(let _145_238 = (let _145_237 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _145_237))
in ((b)::bs, env', _145_238))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _54_376 = (tc_vbinder env x)
in (match (_54_376) with
| (x, env', g) -> begin
(let b = (FStar_Util.Inr (x), imp)
in (let _54_381 = (aux env' bs)
in (match (_54_381) with
| (bs, env', g') -> begin
(let _145_240 = (let _145_239 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _145_239))
in ((b)::bs, env', _145_240))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun env args -> (FStar_List.fold_right (fun _54_386 _54_389 -> (match ((_54_386, _54_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _54_396 = (tc_typ env t)
in (match (_54_396) with
| (t, _54_394, g') -> begin
(let _145_245 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _145_245))
end))
end
| FStar_Util.Inr (e) -> begin
(let _54_403 = (tc_ghost_exp env e)
in (match (_54_403) with
| (e, _54_401, g') -> begin
(let _145_246 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _145_246))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats = (fun env pats -> (FStar_List.fold_right (fun p _54_409 -> (match (_54_409) with
| (pats, g) -> begin
(let _54_412 = (tc_args env p)
in (match (_54_412) with
| (args, g') -> begin
(let _145_251 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _145_251))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _54_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_54_419) with
| (t, g) -> begin
(let _145_254 = (FStar_Absyn_Syntax.mk_Total t)
in (_145_254, g))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (let tc = (FStar_Absyn_Syntax.mk_Typ_app (head, ((FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ))::c.FStar_Absyn_Syntax.effect_args) None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let _54_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_54_427) with
| (tc, f) -> begin
(let _54_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_54_431) with
| (_54_429, args) -> begin
(let _54_443 = (match (args) with
| (FStar_Util.Inl (res), _54_436)::args -> begin
(res, args)
end
| _54_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_54_443) with
| (res, args) -> begin
(let _54_459 = (let _145_256 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _54_3 -> (match (_54_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _54_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_54_450) with
| (env, _54_449) -> begin
(let _54_455 = (tc_ghost_exp env e)
in (match (_54_455) with
| (e, _54_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _145_256 FStar_List.unzip))
in (match (_54_459) with
| (flags, guards) -> begin
(let _145_258 = (FStar_Absyn_Syntax.mk_Comp (let _54_460 = c
in {FStar_Absyn_Syntax.effect_name = _54_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _54_460.FStar_Absyn_Syntax.flags}))
in (let _145_257 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_145_258, _145_257)))
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
in (let a = (let _54_472 = a
in {FStar_Absyn_Syntax.v = _54_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _54_472.FStar_Absyn_Syntax.p})
in (let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _54_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_54_479) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.eqT_k k)
in (let i = (let _54_484 = i
in {FStar_Absyn_Syntax.v = _54_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _54_484.FStar_Absyn_Syntax.p})
in (let _145_281 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_145_281, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.allT_k k)
in (let i = (let _54_491 = i
in {FStar_Absyn_Syntax.v = _54_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _54_491.FStar_Absyn_Syntax.p})
in (let _145_282 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_145_282, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _54_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (let i = (let _54_501 = i
in {FStar_Absyn_Syntax.v = _54_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _54_501.FStar_Absyn_Syntax.p})
in (let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (let _54_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_54_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(let _54_516 = (tc_binders env bs)
in (match (_54_516) with
| (bs, env, g) -> begin
(let _54_519 = (tc_comp env cod)
in (match (_54_519) with
| (cod, f) -> begin
(let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _54_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _54_542; FStar_Absyn_Syntax.result_typ = _54_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _54_536)::(FStar_Util.Inl (post), _54_531)::(FStar_Util.Inr (pats), _54_526)::[]; FStar_Absyn_Syntax.flags = _54_522}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _145_287 = (FStar_Absyn_Util.compress_exp pats)
in _145_287.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _54_557); FStar_Absyn_Syntax.tk = _54_554; FStar_Absyn_Syntax.pos = _54_552; FStar_Absyn_Syntax.fvs = _54_550; FStar_Absyn_Syntax.uvs = _54_548}, _54_572::(FStar_Util.Inr (hd), _54_569)::(FStar_Util.Inr (tl), _54_564)::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _54_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_54_578) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _54_585 -> begin
[]
end)
in (let _145_288 = (extract_pats tl)
in (FStar_List.append pat _145_288)))
end))
end
| _54_588 -> begin
[]
end))
in (let pats = (let _145_289 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _145_289))
in (let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _54_594 -> (match (_54_594) with
| (b, _54_593) -> begin
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
(let _145_292 = (let _145_291 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _145_291))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _145_292))
end))))
end
| _54_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _145_294 = (let _145_293 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _145_293))
in (t, FStar_Absyn_Syntax.ktype, _145_294))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _54_613 = (tc_binders env bs)
in (match (_54_613) with
| (bs, env, g) -> begin
(let _54_617 = (tc_typ env t)
in (match (_54_617) with
| (t, k, f) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _145_299 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _145_298 = (let _145_297 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _145_297))
in (_145_299, k, _145_298))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let _54_626 = (tc_vbinder env x)
in (match (_54_626) with
| (x, env, f1) -> begin
(let _54_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_302 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _145_301 = (FStar_Absyn_Print.typ_to_string phi)
in (let _145_300 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _145_302 _145_301 _145_300))))
end else begin
()
end
in (let _54_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_54_634) with
| (phi, f2) -> begin
(let _145_307 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _145_306 = (let _145_305 = (FStar_Tc_Rel.close_guard (((FStar_Absyn_Syntax.v_binder x))::[]) f2)
in (FStar_Tc_Rel.conj_guard f1 _145_305))
in (_145_307, FStar_Absyn_Syntax.ktype, _145_306)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _54_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_310 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _145_309 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _145_308 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _145_310 _145_309 _145_308))))
end else begin
()
end
in (let _54_644 = (tc_typ (no_inst env) head)
in (match (_54_644) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _54_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_314 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _145_313 = (FStar_Absyn_Print.typ_to_string head)
in (let _145_312 = (FStar_Absyn_Print.kind_to_string k1')
in (let _145_311 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _145_314 _145_313 _145_312 _145_311)))))
end else begin
()
end
in (let check_app = (fun _54_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_54_652) -> begin
(let _54_656 = (tc_args env args)
in (match (_54_656) with
| (args, g) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _145_317 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _145_317 Prims.fst))
in (let bs = (let _145_318 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _145_318))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (let _54_662 = (let _145_319 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _145_319))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _145_330 = (FStar_Absyn_Util.subst_kind subst kres)
in (_145_330, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _145_334 = (let _145_333 = (let _145_332 = (let _145_331 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _145_331))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _145_332))
in FStar_Absyn_Syntax.Error (_145_333))
in (Prims.raise _145_334))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _54_735 = (let _145_335 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _145_335))
in (match (_54_735) with
| (t, u) -> begin
(let targ = (FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (FStar_Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _54_764 = (let _145_336 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _145_336))
in (match (_54_764) with
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
in (let _54_785 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_338 = (FStar_Absyn_Print.arg_to_string actual)
in (let _145_337 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _145_338 _145_337)))
end else begin
()
end
in (let _54_791 = (tc_typ_check (let _54_787 = env
in {FStar_Tc_Env.solver = _54_787.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_787.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_787.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_787.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_787.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_787.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_787.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_787.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_787.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_787.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_787.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_787.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_787.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_787.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_787.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_787.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _54_787.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_787.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_787.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_54_791) with
| (t, g') -> begin
(let _54_792 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_339 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _145_339))
end else begin
()
end
in (let actual = (FStar_Util.Inl (t), imp)
in (let g' = (let _145_341 = (let _145_340 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _145_340))
in (FStar_Tc_Rel.imp_guard _145_341 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _145_342 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _145_342 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _54_808 = env'
in {FStar_Tc_Env.solver = _54_808.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_808.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_808.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_808.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_808.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_808.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_808.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_808.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_808.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_808.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_808.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_808.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_808.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_808.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_808.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_808.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _54_808.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_808.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_808.FStar_Tc_Env.default_effects})
in (let _54_811 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_344 = (FStar_Absyn_Print.arg_to_string actual)
in (let _145_343 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _145_344 _145_343)))
end else begin
()
end
in (let _54_817 = (tc_ghost_exp env' v)
in (match (_54_817) with
| (v, _54_815, g') -> begin
(let actual = (FStar_Util.Inr (v), imp)
in (let g' = (let _145_346 = (let _145_345 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _145_345))
in (FStar_Tc_Rel.imp_guard _145_346 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _145_347 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _145_347 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _54_824), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (FStar_Absyn_Util.b2t v)
in (check_args outargs subst g ((formal)::formals) (((FStar_Absyn_Syntax.targ tv))::actuals)))
end
| _54_834 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_54_836), _54_839), (FStar_Util.Inl (_54_842), _54_845)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_54_849, []) -> begin
(let _145_349 = (let _145_348 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _145_348))
in (_145_349, (FStar_List.rev outargs), g))
end
| ([], _54_854) -> begin
(let _145_357 = (let _145_356 = (let _145_355 = (let _145_354 = (let _145_352 = (let _145_351 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _54_4 -> (match (_54_4) with
| (_54_858, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _54_863 -> begin
true
end))))
in (FStar_List.length _145_351))
in (FStar_All.pipe_right _145_352 FStar_Util.string_of_int))
in (let _145_353 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _145_354 _145_353)))
in (_145_355, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_356))
in (Prims.raise _145_357))
end))
in (check_args [] [] f1 formals args))
end
| _54_865 -> begin
(let _145_360 = (let _145_359 = (let _145_358 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_145_358, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_359))
in (Prims.raise _145_360))
end)
end))
in (match ((let _145_364 = (let _145_361 = (FStar_Absyn_Util.compress_typ head)
in _145_361.FStar_Absyn_Syntax.n)
in (let _145_363 = (let _145_362 = (FStar_Absyn_Util.compress_kind k1)
in _145_362.FStar_Absyn_Syntax.n)
in (_145_364, _145_363)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_54_867), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(let result_k = (let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in (t, result_k, FStar_Tc_Rel.trivial_guard)))
end
| _54_878 -> begin
(let _54_882 = (check_app ())
in (match (_54_882) with
| (k, args, g) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(let _54_890 = (tc_kind env k1)
in (match (_54_890) with
| (k1, f1) -> begin
(let _54_893 = (tc_typ_check env t1 k1)
in (match (_54_893) with
| (t1, f2) -> begin
(let _145_368 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _145_367 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_145_368, k1, _145_367)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_54_895, k1) -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _54_904 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _145_370 = (FStar_Absyn_Print.typ_to_string s)
in (let _145_369 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _145_370 _145_369)))
end else begin
()
end
in (let _145_373 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_145_373, k1, FStar_Tc_Rel.trivial_guard)))
end
| _54_907 -> begin
(let _54_908 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _145_375 = (FStar_Absyn_Print.typ_to_string s)
in (let _145_374 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _145_375 _145_374)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(let _54_919 = (tc_typ env t)
in (match (_54_919) with
| (t, k, f) -> begin
(let _145_376 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_145_376, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(let _54_930 = (tc_typ env t)
in (match (_54_930) with
| (t, k, f) -> begin
(let _145_377 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_145_377, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(let _54_939 = (tc_typ env t)
in (match (_54_939) with
| (t, k, f) -> begin
(let _145_378 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_145_378, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(let _54_947 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_54_947) with
| (quant, f) -> begin
(let _54_950 = (tc_pats env pats)
in (match (_54_950) with
| (pats, g) -> begin
(let g = (let _54_951 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _54_951.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _54_951.FStar_Tc_Rel.implicits})
in (let _145_381 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _145_380 = (FStar_Tc_Util.force_tk quant)
in (let _145_379 = (FStar_Tc_Rel.conj_guard f g)
in (_145_381, _145_380, _145_379)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let t = (FStar_Tc_Util.new_tvar env k)
in (t, k, FStar_Tc_Rel.trivial_guard)))
end
| _54_958 -> begin
(let _145_383 = (let _145_382 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _145_382))
in (FStar_All.failwith _145_383))
end))))))
and tc_typ_check = (fun env t k -> (let _54_965 = (tc_typ env t)
in (match (_54_965) with
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
| FStar_Absyn_Syntax.Exp_uvar (_54_974, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (FStar_Tc_Env.lookup_bvar env x)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar (let _54_981 = x
in {FStar_Absyn_Syntax.v = _54_981.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _54_981.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _54_987 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_54_987) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _145_390 = (let _145_389 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _145_389))
in FStar_Util.Inr (_145_390))
end
in (let _145_391 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _145_391)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (let e = (FStar_Absyn_Syntax.mk_Exp_fvar ((let _54_994 = v
in {FStar_Absyn_Syntax.v = _54_994.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _54_994.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _54_1000 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_54_1000) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _145_393 = (let _145_392 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _145_392))
in FStar_Util.Inr (_145_393))
end
in (let is_data_ctor = (fun _54_5 -> (match (_54_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _54_1010 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _145_399 = (let _145_398 = (let _145_397 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _145_396 = (FStar_Tc_Env.get_range env)
in (_145_397, _145_396)))
in FStar_Absyn_Syntax.Error (_145_398))
in (Prims.raise _145_399))
end else begin
(let _145_400 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _145_400))
end))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fail = (fun msg t -> (let _145_405 = (let _145_404 = (let _145_403 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_145_403, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_404))
in (Prims.raise _145_405)))
in (let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(let _54_1031 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _54_1030 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _54_1036 = (tc_binders env bs)
in (match (_54_1036) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun norm t -> (match ((let _145_414 = (FStar_Absyn_Util.compress_typ t)
in _145_414.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _54_1065 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _54_1064 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _54_1070 = (tc_binders env bs)
in (match (_54_1070) with
| (bs, envbody, g) -> begin
(let _54_1074 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_54_1074) with
| (envbody, _54_1073) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let rec tc_binders = (fun _54_1084 bs_annot c bs -> (match (_54_1084) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _145_423 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _145_423))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_54_1099), _54_1102), (FStar_Util.Inr (_54_1105), _54_1108)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _54_1115), (FStar_Util.Inl (b), imp)) -> begin
(let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _54_1133 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _54_1125 -> begin
(let _54_1128 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_54_1128) with
| (k, g1) -> begin
(let g2 = (FStar_Tc_Rel.keq env None ka k)
in (let g = (let _145_424 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _145_424))
in (k, g)))
end))
end)
in (match (_54_1133) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _54_1134 = b
in {FStar_Absyn_Syntax.v = _54_1134.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _54_1134.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _54_1142), (FStar_Util.Inr (y), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _54_1164 = (match ((let _145_425 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _145_425.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _54_1152 -> begin
(let _54_1153 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_426 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _145_426))
end else begin
()
end
in (let _54_1159 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_54_1159) with
| (t, _54_1157, g1) -> begin
(let g2 = (FStar_Tc_Rel.teq env tx t)
in (let g = (let _145_427 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _145_427))
in (t, g)))
end)))
end)
in (match (_54_1164) with
| (t, g) -> begin
(let b = (FStar_Util.Inr ((let _54_1165 = y
in {FStar_Absyn_Syntax.v = _54_1165.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _54_1165.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _54_1171 -> begin
(let _145_430 = (let _145_429 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _145_428 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _145_429 _145_428)))
in (fail _145_430 t))
end)
end
| ([], _54_1174) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _54_1183; FStar_Absyn_Syntax.pos = _54_1181; FStar_Absyn_Syntax.fvs = _54_1179; FStar_Absyn_Syntax.uvs = _54_1177} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _145_432 = (let _145_431 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _145_431))
in (fail _145_432 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_54_1191, []) -> begin
(let c = (let _145_433 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _145_433 c.FStar_Absyn_Syntax.pos))
in (let _145_434 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _145_434)))
end)
end))
in (let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _54_1200 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_439 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _145_439))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let env = (let _54_1203 = env
in {FStar_Tc_Env.solver = _54_1203.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_1203.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_1203.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_1203.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_1203.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_1203.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_1203.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_1203.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_1203.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_1203.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_1203.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_1203.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_1203.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _54_1203.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_1203.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_1203.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_1203.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_1203.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_1203.FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_54_1210), _54_1213) -> begin
[]
end
| (FStar_Util.Inr (x), _54_1218) -> begin
(match ((let _145_445 = (let _145_444 = (let _145_443 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _145_443))
in (FStar_Absyn_Util.unrefine _145_444))
in _145_445.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_54_1221) -> begin
[]
end
| _54_1224 -> begin
(let _145_446 = (FStar_Absyn_Util.bvar_to_exp x)
in (_145_446)::[])
end)
end)))))
in (let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun dec -> (let _54_1231 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_54_1231) with
| (head, _54_1230) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _54_1234) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _54_1238 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _54_6 -> (match (_54_6) with
| FStar_Absyn_Syntax.DECREASES (_54_1242) -> begin
true
end
| _54_1245 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _54_1249 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _145_455 = (let _145_454 = (let _145_453 = (let _145_451 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _145_450 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _145_451 _145_450)))
in (let _145_452 = (FStar_Tc_Env.get_range env)
in (_145_453, _145_452)))
in FStar_Absyn_Syntax.Error (_145_454))
in (Prims.raise _145_455))
end else begin
()
end
in (let dec = (as_lex_list dec)
in (let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _54_1257), (FStar_Util.Inl (actual), _54_1262)) -> begin
(let _145_459 = (let _145_458 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _145_458))
in FStar_Util.Inl (_145_459))
end
| ((FStar_Util.Inr (formal), _54_1268), (FStar_Util.Inr (actual), _54_1273)) -> begin
(let _145_461 = (let _145_460 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _145_460))
in FStar_Util.Inr (_145_461))
end
| _54_1277 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _54_1280 -> begin
(let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _54_1285 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _54_1289 -> (match (_54_1289) with
| (l, t0) -> begin
(let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _145_463 = (FStar_Absyn_Util.compress_typ t)
in _145_463.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _54_7 -> (match (_54_7) with
| FStar_Absyn_Syntax.DECREASES (_54_1305) -> begin
true
end
| _54_1308 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _145_467 = (let _145_466 = (let _145_465 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _145_465))
in FStar_Util.Inr (_145_466))
in (_145_467)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (FStar_Absyn_Syntax.mk_Typ_app (precedes, ((FStar_Absyn_Syntax.varg dec))::((FStar_Absyn_Syntax.varg prev_dec))::[]) None r)))
end
| _54_1316 -> begin
(let formal_args = (FStar_All.pipe_right (FStar_List.append bs (((FStar_Absyn_Syntax.v_binder y))::[])) filter_types_and_functions)
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _54_1321 -> begin
(mk_lex_list formal_args)
end)
in (FStar_Absyn_Syntax.mk_Typ_app (precedes, ((FStar_Absyn_Syntax.varg lhs))::((FStar_Absyn_Syntax.varg prev_dec))::[]) None r)))
end)
in (let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (FStar_List.append bs (((FStar_Util.Inr ((let _54_1325 = x
in {FStar_Absyn_Syntax.v = _54_1325.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _54_1325.FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _54_1329 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_470 = (FStar_Absyn_Print.lbname_to_string l)
in (let _145_469 = (FStar_Absyn_Print.typ_to_string t)
in (let _145_468 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _145_470 _145_469 _145_468))))
end else begin
()
end
in (let _54_1336 = (let _145_472 = (let _145_471 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _145_471 Prims.fst))
in (tc_typ _145_472 t'))
in (match (_54_1336) with
| (t', _54_1333, _54_1335) -> begin
(l, t')
end)))))))))
end
| _54_1338 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _54_1340 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _145_477 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _54_1345 -> (match (_54_1345) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _145_476 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _54_8 -> (match (_54_8) with
| (FStar_Util.Inl (x), t) -> begin
((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::[]
end
| _54_1352 -> begin
[]
end))))
in (_145_477, _145_476)))))))))))
end))
in (let _54_1357 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_54_1357) with
| (bs, envbody, g, c) -> begin
(let _54_1360 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_54_1360) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _54_1364) -> begin
(let _54_1374 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_54_1374) with
| (_54_1368, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _54_1376 -> begin
if (not (norm)) then begin
(let _145_478 = (whnf env t)
in (as_function_typ true _145_478))
end else begin
(let _54_1385 = (expected_function_typ env None)
in (match (_54_1385) with
| (_54_1378, bs, _54_1381, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_Tc_Env.use_eq
in (let _54_1389 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_54_1389) with
| (env, topt) -> begin
(let _54_1396 = (expected_function_typ env topt)
in (match (_54_1396) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _54_1402 = (tc_exp (let _54_1397 = envbody
in {FStar_Tc_Env.solver = _54_1397.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_1397.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_1397.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_1397.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_1397.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_1397.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_1397.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_1397.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_1397.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_1397.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_1397.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_1397.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_1397.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_1397.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _54_1397.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _54_1397.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_1397.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_1397.FStar_Tc_Env.default_effects}) body)
in (match (_54_1402) with
| (body, cbody, guard_body) -> begin
(let _54_1403 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_481 = (FStar_Absyn_Print.exp_to_string body)
in (let _145_480 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _145_479 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _145_481 _145_480 _145_479))))
end else begin
()
end
in (let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _54_1406 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _145_482 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _145_482))
end else begin
()
end
in (let _54_1413 = (let _145_484 = (let _145_483 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _145_483))
in (check_expected_effect (let _54_1408 = envbody
in {FStar_Tc_Env.solver = _54_1408.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_1408.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_1408.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_1408.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_1408.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_1408.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_1408.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_1408.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_1408.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_1408.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_1408.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_1408.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_1408.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_1408.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_1408.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_1408.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _54_1408.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_1408.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_1408.FStar_Tc_Env.default_effects}) c_opt _145_484))
in (match (_54_1413) with
| (body, cbody, guard) -> begin
(let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(let _54_1415 = (let _145_485 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _145_485))
in (let _54_1417 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _54_1417.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _54_1417.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (let e = (let _145_487 = (let _145_486 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_145_486, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _145_487 None top.FStar_Absyn_Syntax.pos))
in (let _54_1440 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_54_1429) -> begin
(let _145_490 = (let _145_489 = (let _145_488 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_145_488, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _145_489 None top.FStar_Absyn_Syntax.pos))
in (_145_490, t, guard))
end
| _54_1432 -> begin
(let _54_1435 = if use_teq then begin
(let _145_491 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _145_491))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_54_1435) with
| (e, guard') -> begin
(let _145_493 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _145_492 = (FStar_Tc_Rel.conj_guard guard guard')
in (_145_493, t, _145_492)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_54_1440) with
| (e, tfun, guard) -> begin
(let _54_1441 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_496 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _145_495 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _145_494 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _145_496 _145_495 _145_494))))
end else begin
()
end
in (let c = if env.FStar_Tc_Env.top_level then begin
(FStar_Absyn_Syntax.mk_Total tfun)
end else begin
(FStar_Tc_Util.return_value env tfun e)
end
in (let _54_1446 = (let _145_498 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _145_498 guard))
in (match (_54_1446) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _54_1448 -> begin
(let _145_500 = (let _145_499 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _145_499))
in (FStar_All.failwith _145_500))
end))))
and tc_exp = (fun env e -> (let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (let _54_1452 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_505 = (let _145_503 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _145_503))
in (let _145_504 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _145_505 _145_504)))
end else begin
()
end
in (let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_54_1458) -> begin
(let _145_529 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _145_529))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _54_1478) -> begin
(let _54_1483 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_54_1483) with
| (t1, f) -> begin
(let _54_1487 = (let _145_530 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _145_530 e1))
in (match (_54_1487) with
| (e1, c, g) -> begin
(let _54_1491 = (let _145_534 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _54_1488 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _145_534 e1 c f))
in (match (_54_1491) with
| (c, f) -> begin
(let _54_1495 = (let _145_538 = (let _145_537 = (w c)
in (FStar_All.pipe_left _145_537 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _145_538 c))
in (match (_54_1495) with
| (e, c, f2) -> begin
(let _145_540 = (let _145_539 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _145_539))
in (e, c, _145_540))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(let pats_t = (let _145_546 = (let _145_545 = (let _145_541 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _145_541))
in (let _145_544 = (let _145_543 = (let _145_542 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _145_542))
in (_145_543)::[])
in (_145_545, _145_544)))
in (FStar_Absyn_Syntax.mk_Typ_app _145_546 None FStar_Absyn_Syntax.dummyRange))
in (let _54_1505 = (let _145_547 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _145_547 e))
in (match (_54_1505) with
| (e, t, g) -> begin
(let g = (let _54_1506 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _54_1506.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _54_1506.FStar_Tc_Rel.implicits})
in (let c = (let _145_548 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _145_548 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _145_549 = (FStar_Absyn_Util.compress_exp e)
in _145_549.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_54_1516, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _54_1521; FStar_Absyn_Syntax.lbeff = _54_1519; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _54_1532 = (let _145_550 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _145_550 e1))
in (match (_54_1532) with
| (e1, c1, g1) -> begin
(let _54_1536 = (tc_exp env e2)
in (match (_54_1536) with
| (e2, c2, g2) -> begin
(let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _145_558 = (let _145_556 = (let _145_555 = (let _145_554 = (let _145_553 = (w c)
in (FStar_All.pipe_left _145_553 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1)))::[]), e2))))
in (_145_554, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_145_555))
in (FStar_Absyn_Syntax.mk_Exp_meta _145_556))
in (let _145_557 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_145_558, c, _145_557))))
end))
end))
end
| _54_1539 -> begin
(let _54_1543 = (tc_exp env e)
in (match (_54_1543) with
| (e, c, g) -> begin
(let _145_559 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_145_559, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(let _54_1552 = (tc_exp env e)
in (match (_54_1552) with
| (e, c, g) -> begin
(let _145_560 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_145_560, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let env0 = env
in (let env = (let _145_562 = (let _145_561 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _145_561 Prims.fst))
in (FStar_All.pipe_right _145_562 instantiate_both))
in (let _54_1559 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_564 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _145_563 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _145_564 _145_563)))
end else begin
()
end
in (let _54_1564 = (tc_exp (no_inst env) head)
in (match (_54_1564) with
| (head, chead, g_head) -> begin
(let aux = (fun _54_1566 -> (match (()) with
| () -> begin
(let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _54_1570) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _54_1582)::(FStar_Util.Inr (e2), _54_1577)::[] -> begin
(let _54_1588 = (tc_exp env e1)
in (match (_54_1588) with
| (e1, c1, g1) -> begin
(let _54_1592 = (tc_exp env e2)
in (match (_54_1592) with
| (e2, c2, g2) -> begin
(let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _145_570 = (let _145_567 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _145_567))
in (let _145_569 = (let _145_568 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _145_568 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _145_570 c2 _145_569)))
end else begin
(let _145_574 = (let _145_571 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _145_571))
in (let _145_573 = (let _145_572 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _145_572 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _145_574 _145_573 c2)))
end
in (let c = (let _145_577 = (let _145_576 = (FStar_All.pipe_left (fun _145_575 -> Some (_145_575)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_145_576, c2))
in (FStar_Tc_Util.bind env None c1 _145_577))
in (let e = (FStar_Absyn_Syntax.mk_Exp_app (head, ((FStar_Absyn_Syntax.varg e1))::((FStar_Absyn_Syntax.varg e2))::[]) (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos)
in (let _145_579 = (let _145_578 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _145_578))
in (e, c, _145_579)))))))
end))
end))
end
| _54_1599 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _54_1601 -> begin
(let thead = chead.FStar_Absyn_Syntax.res_typ
in (let _54_1603 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_581 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _145_580 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _145_581 _145_580)))
end else begin
()
end
in (let rec check_function_app = (fun norm tf -> (match ((let _145_586 = (FStar_Absyn_Util.unrefine tf)
in _145_586.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _54_1636)::_54_1632 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(let _54_1648 = (tc_exp env e)
in (match (_54_1648) with
| (e, c, g_e) -> begin
(let _54_1652 = (tc_args env tl)
in (match (_54_1652) with
| (args, comps, g_rest) -> begin
(let _145_591 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _145_591))
end))
end))
end))
in (let _54_1656 = (tc_args env args)
in (match (_54_1656) with
| (args, comps, g_args) -> begin
(let bs = (let _145_592 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _145_592))
in (let cres = (let _145_593 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _145_593 top.FStar_Absyn_Syntax.pos))
in (let _54_1659 = (let _145_595 = (let _145_594 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _145_594))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _145_595))
in (let comp = (let _145_598 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _145_598))
in (let _145_600 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _145_599 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_145_600, comp, _145_599)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let vars = (FStar_Tc_Env.binders env)
in (let rec tc_args = (fun _54_1676 bs cres args -> (match (_54_1676) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_54_1690, None)::_54_1688) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _54_1696 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _54_1700 = (let _145_636 = (let _145_635 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _145_635))
in (FStar_Tc_Rel.new_tvar _145_636 vars k))
in (match (_54_1700) with
| (targ, u) -> begin
(let _54_1701 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_638 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _145_637 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _145_638 _145_637)))
end else begin
()
end
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (FStar_Util.Inl (targ), (FStar_Absyn_Syntax.as_implicit true))
in (let _145_647 = (let _145_646 = (let _145_645 = (let _145_644 = (let _145_643 = (FStar_Tc_Util.as_uvar_t u)
in (_145_643, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_145_644))
in (add_implicit _145_645 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _145_646, fvs))
in (tc_args _145_647 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_54_1715, None)::_54_1713) -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _54_1721 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (let _54_1725 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_54_1725) with
| (varg, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (FStar_Util.Inr (varg), (FStar_Absyn_Syntax.as_implicit true))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(let _54_1741 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_653 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _145_652 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _145_653 _145_652)))
end else begin
()
end
in (let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _54_1744 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _54_1750 = (tc_typ_check (let _54_1746 = env
in {FStar_Tc_Env.solver = _54_1746.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_1746.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_1746.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_1746.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_1746.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_1746.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_1746.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_1746.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_1746.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_1746.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_1746.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_1746.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_1746.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_1746.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_1746.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_1746.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _54_1746.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_1746.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_1746.FStar_Tc_Env.default_effects}) t k)
in (match (_54_1750) with
| (t, g') -> begin
(let f = (let _145_654 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _145_654))
in (let g' = (let _54_1752 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _54_1752.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _54_1752.FStar_Tc_Rel.implicits})
in (let arg = (FStar_Util.Inl (t), aq)
in (let subst = (let _145_655 = (FStar_List.hd bs)
in (maybe_extend_subst subst _145_655 arg))
in (let _145_661 = (let _145_660 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _145_660, fvs))
in (tc_args _145_661 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(let _54_1770 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_663 = (FStar_Absyn_Print.subst_to_string subst)
in (let _145_662 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _145_663 _145_662)))
end else begin
()
end
in (let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _54_1773 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_664 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _145_664))
end else begin
()
end
in (let _54_1775 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (let env = (FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _54_1778 = env
in {FStar_Tc_Env.solver = _54_1778.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_1778.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_1778.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_1778.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_1778.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_1778.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_1778.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_1778.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_1778.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_1778.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_1778.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_1778.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_1778.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_1778.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_1778.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_1778.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _54_1778.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_1778.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_1778.FStar_Tc_Env.default_effects})
in (let _54_1781 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _145_666 = (FStar_Absyn_Print.exp_to_string e)
in (let _145_665 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _145_666 _145_665)))
end else begin
()
end
in (let _54_1783 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_669 = (FStar_Absyn_Print.tag_of_exp e)
in (let _145_668 = (FStar_Absyn_Print.exp_to_string e)
in (let _145_667 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _145_669 _145_668 _145_667))))
end else begin
()
end
in (let _54_1788 = (tc_exp env e)
in (match (_54_1788) with
| (e, c, g_e) -> begin
(let g = (FStar_Tc_Rel.conj_guard g g_e)
in (let _54_1790 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_671 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _145_670 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _145_671 _145_670)))
end else begin
()
end
in (let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(let subst = (let _145_672 = (FStar_List.hd bs)
in (maybe_extend_subst subst _145_672 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(let subst = (let _145_677 = (FStar_List.hd bs)
in (maybe_extend_subst subst _145_677 arg))
in (let _54_1797 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_54_1797) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _145_682 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _145_682)) then begin
(let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _145_683 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _145_683))
in (let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _145_696 = (let _145_695 = (let _145_689 = (let _145_688 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _145_688))
in (_145_689)::arg_rets)
in (let _145_694 = (let _145_692 = (let _145_691 = (FStar_All.pipe_left (fun _145_690 -> Some (_145_690)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_145_691, c))
in (_145_692)::comps)
in (let _145_693 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _145_695, _145_694, g, _145_693))))
in (tc_args _145_696 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_54_1804), _54_1807)::_54_1802, (FStar_Util.Inl (_54_1813), _54_1816)::_54_1811) -> begin
(let _145_700 = (let _145_699 = (let _145_698 = (let _145_697 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _145_697))
in ("Expected an expression; got a type", _145_698))
in FStar_Absyn_Syntax.Error (_145_699))
in (Prims.raise _145_700))
end
| ((FStar_Util.Inl (_54_1823), _54_1826)::_54_1821, (FStar_Util.Inr (_54_1832), _54_1835)::_54_1830) -> begin
(let _145_704 = (let _145_703 = (let _145_702 = (let _145_701 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _145_701))
in ("Expected a type; got an expression", _145_702))
in FStar_Absyn_Syntax.Error (_145_703))
in (Prims.raise _145_704))
end
| (_54_1840, []) -> begin
(let _54_1843 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (let _54_1861 = (match (bs) with
| [] -> begin
(let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _54_1851 -> (match (_54_1851) with
| (_54_1849, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = if refine_with_equality then begin
(let _145_706 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _145_706 cres))
end else begin
(let _54_1853 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_709 = (FStar_Absyn_Print.exp_to_string head)
in (let _145_708 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _145_707 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _145_709 _145_708 _145_707))))
end else begin
()
end
in cres)
end
in (let _145_710 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_145_710, g))))))
end
| _54_1857 -> begin
(let g = (let _145_711 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _145_711 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _145_717 = (let _145_716 = (let _145_715 = (let _145_714 = (let _145_713 = (let _145_712 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _145_712))
in (FStar_Absyn_Syntax.mk_Typ_fun _145_713 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _145_714))
in (FStar_Absyn_Syntax.mk_Total _145_715))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _145_716))
in (_145_717, g)))
end)
in (match (_54_1861) with
| (cres, g) -> begin
(let _54_1862 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_718 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _145_718))
end else begin
()
end
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev outargs)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _54_1871 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_54_1871) with
| (comp, g) -> begin
(let _54_1872 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_724 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _145_723 = (let _145_722 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _145_722))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _145_724 _145_723)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_54_1876) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _145_729 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _145_729 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(let _54_1888 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_730 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _145_730))
end else begin
()
end
in (let _145_735 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _145_735 args)))
end
| _54_1891 when (not (norm)) -> begin
(let _145_736 = (whnf env tres)
in (aux true _145_736))
end
| _54_1893 -> begin
(let _145_741 = (let _145_740 = (let _145_739 = (let _145_738 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _145_737 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _145_738 _145_737)))
in (_145_739, (FStar_Absyn_Syntax.argpos arg)))
in FStar_Absyn_Syntax.Error (_145_740))
in (Prims.raise _145_741))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _145_742 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _145_742 args))))
end
| _54_1895 -> begin
if (not (norm)) then begin
(let _145_743 = (whnf env tf)
in (check_function_app true _145_743))
end else begin
(let _145_746 = (let _145_745 = (let _145_744 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_145_744, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_745))
in (Prims.raise _145_746))
end
end))
in (let _145_747 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _145_747)))))
end))
end))
in (let _54_1899 = (aux ())
in (match (_54_1899) with
| (e, c, g) -> begin
(let _54_1900 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _145_748 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _145_748))
end else begin
()
end
in (let c = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (let _54_1907 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_753 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _145_752 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _145_751 = (let _145_750 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _145_750 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _145_753 _145_752 _145_751))))
end else begin
()
end
in (let _54_1912 = (comp_check_expected_typ env0 e c)
in (match (_54_1912) with
| (e, c, g') -> begin
(let _145_754 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _145_754))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let _54_1919 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_54_1919) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _54_1924 = (tc_exp env1 e1)
in (match (_54_1924) with
| (e1, c1, g1) -> begin
(let _54_1931 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _145_755 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_145_755, res_t)))
end)
in (match (_54_1931) with
| (env_branches, res_t) -> begin
(let guard_x = (let _145_757 = (FStar_All.pipe_left (fun _145_756 -> Some (_145_756)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _145_757))
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (let _54_1948 = (let _54_1945 = (FStar_List.fold_right (fun _54_1939 _54_1942 -> (match ((_54_1939, _54_1942)) with
| ((_54_1935, f, c, g), (caccum, gaccum)) -> begin
(let _145_760 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _145_760))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_54_1945) with
| (cases, g) -> begin
(let _145_761 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_145_761, g))
end))
in (match (_54_1948) with
| (c_branches, g_branches) -> begin
(let _54_1949 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_765 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _145_764 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _145_763 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _145_762 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _145_765 _145_764 _145_763 _145_762)))))
end else begin
()
end
in (let cres = (let _145_768 = (let _145_767 = (FStar_All.pipe_left (fun _145_766 -> Some (_145_766)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_145_767, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _145_768))
in (let e = (let _145_775 = (w cres)
in (let _145_774 = (let _145_773 = (let _145_772 = (FStar_List.map (fun _54_1959 -> (match (_54_1959) with
| (f, _54_1954, _54_1956, _54_1958) -> begin
f
end)) t_eqns)
in (e1, _145_772))
in (FStar_Absyn_Syntax.mk_Exp_match _145_773))
in (FStar_All.pipe_left _145_775 _145_774)))
in (let _145_777 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _145_776 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_145_777, cres, _145_776))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _54_1964; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| FStar_Util.Inr (_54_1977) -> begin
true
end
| _54_1980 -> begin
false
end)
in (let _54_1985 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_54_1985) with
| (env1, _54_1984) -> begin
(let _54_1998 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _54_1988 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _145_778 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _145_778))
end else begin
(let _54_1991 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_54_1991) with
| (t, f) -> begin
(let _54_1992 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_780 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _145_779 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _145_780 _145_779)))
end else begin
()
end
in (let t = (norm_t env1 t)
in (let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end
end)
in (match (_54_1998) with
| (f, env1) -> begin
(let _54_2004 = (tc_exp (let _54_1999 = env1
in {FStar_Tc_Env.solver = _54_1999.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_1999.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_1999.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_1999.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_1999.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_1999.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_1999.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_1999.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_1999.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_1999.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_1999.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_1999.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_1999.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_1999.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _54_1999.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_1999.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_1999.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_1999.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_1999.FStar_Tc_Env.default_effects}) e1)
in (match (_54_2004) with
| (e1, c1, g1) -> begin
(let _54_2008 = (let _145_784 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _54_2005 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _145_784 e1 c1 f))
in (match (_54_2008) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_54_2010) -> begin
(let _54_2021 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(let _54_2014 = (let _145_785 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _145_785 c1))
in (match (_54_2014) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(let _54_2015 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _145_786 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _145_786 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _145_787 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_145_787, c1)))
end
end))
end else begin
(let _54_2017 = (let _145_788 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.discharge_guard env _145_788))
in (let _145_789 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _145_789)))
end
in (match (_54_2021) with
| (e2, c1) -> begin
(let _54_2026 = if env.FStar_Tc_Env.generalize then begin
(let _145_790 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _145_790))
end else begin
(x, e1, c1)
end
in (match (_54_2026) with
| (_54_2023, e1, c1) -> begin
(let cres = (let _145_791 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _145_791))
in (let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _145_792 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _145_792 (None, cres)))
end
in (let _54_2029 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _145_796 = (let _145_795 = (w cres)
in (FStar_All.pipe_left _145_795 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1)))::[]), e2))))
in (_145_796, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (let _54_2037 = (let _145_797 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _145_797 e2))
in (match (_54_2037) with
| (e2, c2, g2) -> begin
(let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _145_800 = (w cres)
in (FStar_All.pipe_left _145_800 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1)))::[]), e2))))
in (let g2 = (let _145_806 = (let _145_805 = (let _145_804 = (let _145_803 = (let _145_802 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _145_802 e1))
in (FStar_All.pipe_left (fun _145_801 -> FStar_Tc_Rel.NonTrivial (_145_801)) _145_803))
in (FStar_Tc_Rel.guard_of_guard_formula _145_804))
in (FStar_Tc_Rel.imp_guard _145_805 g2))
in (FStar_All.pipe_left (FStar_Tc_Rel.close_guard (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ)))::[])) _145_806))
in (let guard = (let _145_807 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _145_807))
in (match (topt) with
| None -> begin
(let tres = cres.FStar_Absyn_Syntax.res_typ
in (let fvs = (FStar_Absyn_Util.freevars_typ tres)
in if (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs) then begin
(let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _54_2046 = (let _145_808 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _145_808))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _54_2049 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _54_2052), _54_2055) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(let env = (instantiate_both env)
in (let _54_2067 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_54_2067) with
| (env0, topt) -> begin
(let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _54_9 -> (match (_54_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_54_2076); FStar_Absyn_Syntax.lbtyp = _54_2074; FStar_Absyn_Syntax.lbeff = _54_2072; FStar_Absyn_Syntax.lbdef = _54_2070} -> begin
true
end
| _54_2080 -> begin
false
end))))
in (let _54_2105 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _54_2084 _54_2090 -> (match ((_54_2084, _54_2090)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _54_2087; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _54_2095 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_54_2095) with
| (_54_2092, t, check_t) -> begin
(let e = (FStar_Absyn_Util.unascribe e)
in (let t = if (not (check_t)) then begin
t
end else begin
(let _145_812 = (tc_typ_check_trivial (let _54_2097 = env0
in {FStar_Tc_Env.solver = _54_2097.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_2097.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_2097.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_2097.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_2097.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_2097.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_2097.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_2097.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_2097.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_2097.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_2097.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_2097.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_2097.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_2097.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_2097.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _54_2097.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_2097.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_2097.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_2097.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_812 (norm_t env)))
end
in (let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(let _54_2100 = env
in {FStar_Tc_Env.solver = _54_2100.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_2100.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_2100.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_2100.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_2100.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_2100.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_2100.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_2100.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_2100.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_2100.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_2100.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_2100.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_2100.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_2100.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_2100.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_2100.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_2100.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_2100.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_2100.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_54_2105) with
| (lbs, env') -> begin
(let _54_2120 = (let _145_818 = (let _145_817 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _145_817 (FStar_List.map (fun _54_2109 -> (match (_54_2109) with
| (x, t, e) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (let _54_2111 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_816 = (FStar_Absyn_Print.lbname_to_string x)
in (let _145_815 = (FStar_Absyn_Print.exp_to_string e)
in (let _145_814 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _145_816 _145_815 _145_814))))
end else begin
()
end
in (let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (let _54_2117 = (tc_total_exp env' e)
in (match (_54_2117) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _145_818 FStar_List.unzip))
in (match (_54_2120) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (let _54_2139 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _145_820 = (FStar_List.map (fun _54_2125 -> (match (_54_2125) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_145_820, g_lbs))
end else begin
(let _54_2126 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _145_823 = (FStar_All.pipe_right lbs (FStar_List.map (fun _54_2131 -> (match (_54_2131) with
| (x, t, e) -> begin
(let _145_822 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb (x, t, e)))
in (x, e, _145_822))
end))))
in (FStar_Tc_Util.generalize true env _145_823))
in (let _145_825 = (FStar_List.map (fun _54_2136 -> (match (_54_2136) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_145_825, FStar_Tc_Rel.trivial_guard))))
end
in (match (_54_2139) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(let cres = (let _145_826 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _145_826))
in (let _54_2141 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let _54_2143 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _145_830 = (let _145_829 = (w cres)
in (FStar_All.pipe_left _145_829 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_145_830, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(let _54_2159 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _54_2147 _54_2154 -> (match ((_54_2147, _54_2154)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _54_2151; FStar_Absyn_Syntax.lbdef = _54_2149}) -> begin
(let b = (binding_of_lb x t)
in (let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_54_2159) with
| (bindings, env) -> begin
(let _54_2163 = (tc_exp env e1)
in (match (_54_2163) with
| (e1, cres, g1) -> begin
(let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (let cres = (let _54_2167 = cres
in {FStar_Absyn_Syntax.eff_name = _54_2167.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _54_2167.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _54_2167.FStar_Absyn_Syntax.comp})
in (let e = (let _145_835 = (w cres)
in (FStar_All.pipe_left _145_835 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_54_2172) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _54_10 -> (match (_54_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_54_2184); FStar_Absyn_Syntax.lbtyp = _54_2182; FStar_Absyn_Syntax.lbeff = _54_2180; FStar_Absyn_Syntax.lbdef = _54_2178} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _54_2192; FStar_Absyn_Syntax.lbeff = _54_2190; FStar_Absyn_Syntax.lbdef = _54_2188} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _54_2201; FStar_Absyn_Syntax.lbeff = _54_2199; FStar_Absyn_Syntax.lbdef = _54_2197}) -> begin
(let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _54_2207 = (let _145_837 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _145_837))
in (e, cres, guard)))
end
| _54_2210 -> begin
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
and tc_eqn = (fun scrutinee_x pat_t env _54_2217 -> (match (_54_2217) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _54_2225 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_54_2225) with
| (bindings, exps, p) -> begin
(let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (let _54_2234 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _54_11 -> (match (_54_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _145_850 = (FStar_Absyn_Print.strBvd x)
in (let _145_849 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _145_850 _145_849)))
end
| _54_2233 -> begin
()
end))))
end else begin
()
end
in (let _54_2239 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_54_2239) with
| (env1, _54_2238) -> begin
(let env1 = (let _54_2240 = env1
in {FStar_Tc_Env.solver = _54_2240.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_2240.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_2240.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_2240.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_2240.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_2240.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_2240.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_2240.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _54_2240.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_2240.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_2240.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_2240.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_2240.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_2240.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_2240.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_2240.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_2240.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_2240.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_2240.FStar_Tc_Env.default_effects})
in (let expected_pat_t = (FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _54_2245 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_853 = (FStar_Absyn_Print.exp_to_string e)
in (let _145_852 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _145_853 _145_852)))
end else begin
()
end
in (let _54_2250 = (tc_exp env1 e)
in (match (_54_2250) with
| (e, lc, g) -> begin
(let _54_2251 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_855 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _145_854 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _145_855 _145_854)))
end else begin
()
end
in (let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (FStar_Tc_Rel.conj_guard g g')
in (let _54_2255 = (let _145_856 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _145_856))
in (let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (let _54_2258 = if (let _145_859 = (let _145_858 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _145_857 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _145_858 _145_857)))
in (FStar_All.pipe_left Prims.op_Negation _145_859)) then begin
(let _145_864 = (let _145_863 = (let _145_862 = (let _145_861 = (FStar_Absyn_Print.exp_to_string e')
in (let _145_860 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _145_861 _145_860)))
in (_145_862, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_145_863))
in (Prims.raise _145_864))
end else begin
()
end
in (let _54_2260 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_865 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _145_865))
end else begin
()
end
in e)))))))
end))))))
in (let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (let _54_2271 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _54_12 -> (match (_54_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _145_868 = (FStar_Absyn_Print.strBvd x)
in (let _145_867 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _145_868 _145_867)))
end
| _54_2270 -> begin
()
end))))
end else begin
()
end
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _54_2278 = (tc_pat true pat_t pattern)
in (match (_54_2278) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _54_2288 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(let _54_2285 = (let _145_869 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _145_869 e))
in (match (_54_2285) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_54_2288) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _145_871 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _145_870 -> Some (_145_870)) _145_871))
end)
in (let _54_2296 = (tc_exp pat_env branch)
in (match (_54_2296) with
| (branch, c, g_branch) -> begin
(let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _54_2301 = (let _145_872 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _145_872 FStar_Tc_Env.clear_expected_typ))
in (match (_54_2301) with
| (scrutinee_env, _54_2300) -> begin
(let c = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _54_2315 -> begin
(let clause = (let _145_876 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _145_875 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _145_876 _145_875 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _145_878 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _145_877 -> Some (_145_877)) _145_878))
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
(let _145_881 = (let _145_880 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _145_879 -> FStar_Tc_Rel.NonTrivial (_145_879)) _145_880))
in (FStar_Tc_Util.weaken_precondition env c _145_881))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun scrutinee f -> (let disc = (let _145_887 = (let _145_886 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _145_886))
in (FStar_All.pipe_left _145_887 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (let disc = (let _145_890 = (let _145_889 = (let _145_888 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_145_888)::[])
in (disc, _145_889))
in (FStar_Absyn_Syntax.mk_Exp_app _145_890 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun scrutinee pat_exp -> (let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_54_2373) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (FStar_Absyn_Util.teq, ((FStar_Absyn_Syntax.varg scrutinee))::((FStar_Absyn_Syntax.varg pat_exp))::[]) None scrutinee.FStar_Absyn_Syntax.pos)
end
| FStar_Absyn_Syntax.Exp_fvar (f, _54_2377) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _54_2390); FStar_Absyn_Syntax.tk = _54_2387; FStar_Absyn_Syntax.pos = _54_2385; FStar_Absyn_Syntax.fvs = _54_2383; FStar_Absyn_Syntax.uvs = _54_2381}, args) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _145_900 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_54_2401) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in (let sub_term = (let _145_898 = (let _145_897 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (_145_897, ((FStar_Absyn_Syntax.varg scrutinee))::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _145_898 None f.FStar_Absyn_Syntax.p))
in (let _145_899 = (mk_guard sub_term ei)
in (_145_899)::[])))
end))))
in (FStar_All.pipe_right _145_900 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _54_2409 -> begin
(let _145_903 = (let _145_902 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _145_901 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _145_902 _145_901)))
in (FStar_All.failwith _145_903))
end)))
in (let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(let t = (mk_guard s pat)
in (let _54_2418 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_54_2418) with
| (t, _54_2417) -> begin
t
end)))
end)
in (let path_guard = (let _145_912 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _145_911 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _145_911)))))
in (FStar_All.pipe_right _145_912 FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _145_913 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _145_913))
in (let _54_2426 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _145_914 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _145_914))
end else begin
()
end
in (let _145_916 = (let _145_915 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _145_915))
in ((pattern, when_clause, branch), path_guard, c, _145_916))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun env k -> (let _54_2432 = (tc_kind env k)
in (match (_54_2432) with
| (k, g) -> begin
(let _54_2433 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun env t -> (let _54_2440 = (tc_typ env t)
in (match (_54_2440) with
| (t, k, g) -> begin
(let _54_2441 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun env t k -> (let _54_2448 = (tc_typ_check env t k)
in (match (_54_2448) with
| (t, f) -> begin
(let _54_2449 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun env e -> (let _54_2456 = (tc_exp env e)
in (match (_54_2456) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _145_926 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _145_926 (norm_c env)))
in (match ((let _145_928 = (let _145_927 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _145_927))
in (FStar_Tc_Rel.sub_comp env c _145_928))) with
| Some (g') -> begin
(let _145_929 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _145_929))
end
| _54_2462 -> begin
(let _145_932 = (let _145_931 = (let _145_930 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_145_930, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_931))
in (Prims.raise _145_932))
end)))
end
end)))
and tc_ghost_exp = (fun env e -> (let _54_2468 = (tc_exp env e)
in (match (_54_2468) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let c = (let _145_935 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _145_935 (norm_c env)))
in (let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (let _54_2472 = env
in {FStar_Tc_Env.solver = _54_2472.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_2472.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_2472.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_2472.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_2472.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_2472.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_2472.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_2472.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_2472.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_2472.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_2472.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_2472.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_2472.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_2472.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_2472.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_2472.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _54_2472.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_2472.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_2472.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _145_936 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _145_936))
end
| _54_2477 -> begin
(let _145_939 = (let _145_938 = (let _145_937 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_145_937, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_145_938))
in (Prims.raise _145_939))
end))))
end
end)))

let tc_tparams = (fun env tps -> (let _54_2483 = (tc_binders env tps)
in (match (_54_2483) with
| (tps, env, g) -> begin
(let _54_2484 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _54_2503)::(FStar_Util.Inl (wp), _54_2498)::(FStar_Util.Inl (_54_2490), _54_2493)::[], _54_2507) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _54_2511 -> begin
(let _145_952 = (let _145_951 = (let _145_950 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (_145_950, (FStar_Ident.range_of_lid m)))
in FStar_Absyn_Syntax.Error (_145_951))
in (Prims.raise _145_952))
end))

let rec tc_eff_decl = (fun env m -> (let _54_2517 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_54_2517) with
| (binders, env, g) -> begin
(let _54_2518 = (FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (let _54_2523 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_54_2523) with
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
in (let _145_974 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _145_974 (norm_t env))))
in (let bind_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder a_kwp_b))::((FStar_Absyn_Syntax.null_t_binder a_kwlp_b))::[], kwp_b)))
in (let _145_976 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _145_976 (norm_t env))))
in (let bind_wlp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder a_kwlp_b))::[], kwlp_b)))
in (let _145_978 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _145_978 (norm_t env))))
in (let if_then_else = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _145_980 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _145_980 (norm_t env))))
in (let ite_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _145_982 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _145_982 (norm_t env))))
in (let ite_wlp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::[], kwlp_a)))
in (let _145_984 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _145_984 (norm_t env))))
in (let wp_binop = (let expected_k = (let _145_992 = (let _145_991 = (let _145_990 = (let _145_989 = (let _145_988 = (let _145_987 = (let _145_986 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _145_986))
in (_145_987)::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[])
in ((FStar_Absyn_Syntax.null_t_binder kwp_a))::_145_988)
in ((FStar_Absyn_Syntax.t_binder a))::_145_989)
in (_145_990, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _145_991))
in (FStar_All.pipe_left w _145_992))
in (let _145_993 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _145_993 (norm_t env))))
in (let wp_as_type = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], FStar_Absyn_Syntax.ktype)))
in (let _145_995 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _145_995 (norm_t env))))
in (let close_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder a_kwp_b))::[], kwp_b)))
in (let _145_997 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _145_997 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _145_1005 = (let _145_1004 = (let _145_1003 = (let _145_1002 = (let _145_1001 = (let _145_1000 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype))::[], kwp_a)))
in (FStar_Absyn_Syntax.null_t_binder _145_1000))
in (_145_1001)::[])
in ((FStar_Absyn_Syntax.t_binder a))::_145_1002)
in (_145_1003, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _145_1004))
in (FStar_All.pipe_left w _145_1005))
in (let _145_1006 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _145_1006 (norm_t env))))
in (let _54_2557 = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _145_1011 = (let _145_1008 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _145_1008 (norm_t env)))
in (let _145_1010 = (let _145_1009 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _145_1009 (norm_t env)))
in (_145_1011, _145_1010))))
in (match (_54_2557) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::[], kwp_a)))
in (let _145_1013 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _145_1013 (norm_t env))))
in (let trivial_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], FStar_Absyn_Syntax.ktype)))
in (let _145_1015 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _145_1015 (norm_t env))))
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
(let _54_2576 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _54_2578 = (let _145_1019 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _145_1019 Prims.ignore))
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
(let _54_2593 = (let _145_1020 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _145_1020))
in (match (_54_2593) with
| (a, kwp_a_src) -> begin
(let _54_2596 = (let _145_1021 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _145_1021))
in (match (_54_2596) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _145_1025 = (let _145_1024 = (let _145_1023 = (let _145_1022 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _145_1022))
in FStar_Util.Inl (_145_1023))
in (_145_1024)::[])
in (FStar_Absyn_Util.subst_kind _145_1025 kwp_b_tgt))
in (let expected_k = (FStar_All.pipe_right r (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a_src))::[], kwp_a_tgt)))
in (let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _54_2600 = sub
in {FStar_Absyn_Syntax.source = _54_2600.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _54_2600.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _54_2617 = (tc_tparams env tps)
in (match (_54_2617) with
| (tps, env) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _54_2620 -> begin
(tc_kind_trivial env k)
end)
in (let _54_2622 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _145_1028 = (FStar_Absyn_Print.sli lid)
in (let _145_1027 = (let _145_1026 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _145_1026))
in (FStar_Util.print2 "Checked %s at kind %s\n" _145_1028 _145_1027)))
end else begin
()
end
in (let k = (norm_k env k)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _54_2640 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_54_2635); FStar_Absyn_Syntax.tk = _54_2633; FStar_Absyn_Syntax.pos = _54_2631; FStar_Absyn_Syntax.fvs = _54_2629; FStar_Absyn_Syntax.uvs = _54_2627} -> begin
(let _145_1029 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _145_1029))
end
| _54_2639 -> begin
()
end)
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _54_2653 = (tc_tparams env tps)
in (match (_54_2653) with
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
in (let _54_2668 = (tc_tparams env tps)
in (match (_54_2668) with
| (tps, env) -> begin
(let _54_2671 = (tc_comp env c)
in (match (_54_2671) with
| (c, g) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _54_13 -> (match (_54_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _145_1032 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _145_1031 -> Some (_145_1031)))
in FStar_Absyn_Syntax.DefaultEffect (_145_1032)))
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
in (let _54_2691 = (tc_tparams env tps)
in (match (_54_2691) with
| (tps, env') -> begin
(let _54_2697 = (let _145_1036 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _145_1036 (fun _54_2694 -> (match (_54_2694) with
| (t, k) -> begin
(let _145_1035 = (norm_t env' t)
in (let _145_1034 = (norm_k env' k)
in (_145_1035, _145_1034)))
end))))
in (match (_54_2697) with
| (t, k1) -> begin
(let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _54_2700 -> begin
(let k2 = (let _145_1037 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _145_1037 (norm_k env)))
in (let _54_2702 = (let _145_1038 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _145_1038))
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
in (let _54_2722 = (tc_binders env tps)
in (match (_54_2722) with
| (tps, env, g) -> begin
(let tycon = (tname, tps, k)
in (let _54_2724 = (FStar_Tc_Util.discharge_guard env g)
in (let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _54_2736 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _54_2733 -> begin
([], t)
end)
in (match (_54_2736) with
| (formals, result_t) -> begin
(let cardinality_and_positivity_check = (fun formal -> (let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _54_2744 -> (match (_54_2744) with
| (a, _54_2743) -> begin
(match (a) with
| FStar_Util.Inl (_54_2746) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _145_1046 = (FStar_Absyn_Util.compress_typ t)
in _145_1046.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _145_1050 = (let _145_1049 = (let _145_1048 = (let _145_1047 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _145_1047 tname))
in (_145_1048, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_145_1049))
in (Prims.raise _145_1050))
end)
end
| _54_2759 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(let _54_2762 = if (FStar_Options.warn_cardinality ()) then begin
(let _145_1051 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _145_1051))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _145_1054 = (let _145_1053 = (let _145_1052 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_145_1052, r))
in FStar_Absyn_Syntax.Error (_145_1053))
in (Prims.raise _145_1054))
end else begin
()
end
end
in (let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_54_2766) -> begin
(let _54_2771 = (FStar_Absyn_Util.kind_formals k)
in (match (_54_2771) with
| (formals, _54_2770) -> begin
(check_positivity formals)
end))
end
| _54_2773 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(let _54_2780 = (let _145_1055 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _145_1055 FStar_Util.must))
in (match (_54_2780) with
| (formals, _54_2779) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (let _54_2781 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (let _54_2835 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _145_1059 = (let _145_1058 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _145_1058 Prims.fst))
in (FStar_List.forall2 (fun _54_2788 _54_2792 -> (match ((_54_2788, _54_2792)) with
| ((a, _54_2787), (b, _54_2791)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _54_2800; FStar_Absyn_Syntax.pos = _54_2798; FStar_Absyn_Syntax.fvs = _54_2796; FStar_Absyn_Syntax.uvs = _54_2794}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _54_2815; FStar_Absyn_Syntax.pos = _54_2813; FStar_Absyn_Syntax.fvs = _54_2811; FStar_Absyn_Syntax.uvs = _54_2809}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _54_2824 -> begin
false
end)
end)) _145_1059 tps))))) then begin
(let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _54_2827 -> begin
(let _54_2831 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_54_2831) with
| (_54_2829, expected_args) -> begin
(let _145_1060 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _145_1060 expected_args))
end))
end)
in (let _145_1064 = (let _145_1063 = (let _145_1062 = (let _145_1061 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _145_1061 result_t expected_t))
in (_145_1062, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_145_1063))
in (Prims.raise _145_1064)))
end else begin
()
end
end
| _54_2834 -> begin
(let _145_1069 = (let _145_1068 = (let _145_1067 = (let _145_1066 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _145_1065 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _145_1066 result_t _145_1065)))
in (_145_1067, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_145_1068))
in (Prims.raise _145_1069))
end)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _54_2839 = if (log env) then begin
(let _145_1071 = (let _145_1070 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _145_1070))
in (FStar_All.pipe_left FStar_Util.print_string _145_1071))
end else begin
()
end
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let t = (let _145_1072 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_1072 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _54_2849 = (FStar_Tc_Util.check_uvars r t)
in (let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _54_2853 = if (log env) then begin
(let _145_1074 = (let _145_1073 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _145_1073))
in (FStar_All.pipe_left FStar_Util.print_string _145_1074))
end else begin
()
end
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let phi = (let _145_1075 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _145_1075 (norm_t env)))
in (let _54_2863 = (FStar_Tc_Util.check_uvars r phi)
in (let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _54_2916 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _54_2876 lb -> (match (_54_2876) with
| (gen, lbs) -> begin
(let _54_2913 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_54_2885); FStar_Absyn_Syntax.lbtyp = _54_2883; FStar_Absyn_Syntax.lbeff = _54_2881; FStar_Absyn_Syntax.lbdef = _54_2879} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _54_2890; FStar_Absyn_Syntax.lbdef = e} -> begin
(let _54_2910 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _54_2898) -> begin
(let _54_2901 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _145_1078 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _145_1078 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(false, (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e)))
end
| _54_2905 -> begin
(let _54_2906 = if (not (deserialized)) then begin
(let _145_1080 = (let _145_1079 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _145_1079))
in (FStar_All.pipe_left FStar_Util.print_string _145_1080))
end else begin
()
end
in (false, (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))))
end))
end)
in (match (_54_2910) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_54_2913) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_54_2916) with
| (generalize, lbs') -> begin
(let lbs' = (FStar_List.rev lbs')
in (let e = (let _145_1085 = (let _145_1084 = (let _145_1083 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _145_1083 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((Prims.fst lbs), lbs'), _145_1084))
in (FStar_Absyn_Syntax.mk_Exp_let _145_1085 None r))
in (let _54_2951 = (match ((tc_exp (let _54_2919 = env
in {FStar_Tc_Env.solver = _54_2919.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_2919.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_2919.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_2919.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_2919.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_2919.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_2919.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_2919.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_2919.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_2919.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_2919.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_2919.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _54_2919.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_2919.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_2919.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_2919.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _54_2919.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _54_2919.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _54_2919.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _54_2928; FStar_Absyn_Syntax.pos = _54_2926; FStar_Absyn_Syntax.fvs = _54_2924; FStar_Absyn_Syntax.uvs = _54_2922}, _54_2935, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_54_2939, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _54_2945 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _54_2948 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_54_2951) with
| (se, lbs) -> begin
(let _54_2957 = if (log env) then begin
(let _145_1091 = (let _145_1090 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _145_1087 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _145_1087))) with
| None -> begin
true
end
| _54_2955 -> begin
false
end)
in if should_log then begin
(let _145_1089 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _145_1088 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _145_1089 _145_1088)))
end else begin
""
end))))
in (FStar_All.pipe_right _145_1090 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _145_1091))
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
in (let _54_2969 = (tc_exp env e)
in (match (_54_2969) with
| (e, c, g1) -> begin
(let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _54_2975 = (let _145_1095 = (let _145_1092 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_145_1092))
in (let _145_1094 = (let _145_1093 = (c.FStar_Absyn_Syntax.comp ())
in (e, _145_1093))
in (check_expected_effect env _145_1095 _145_1094)))
in (match (_54_2975) with
| (e, _54_2973, g) -> begin
(let _54_2976 = (let _145_1096 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _145_1096))
in (let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _54_2995 = (FStar_All.pipe_right ses (FStar_List.partition (fun _54_14 -> (match (_54_14) with
| FStar_Absyn_Syntax.Sig_tycon (_54_2989) -> begin
true
end
| _54_2992 -> begin
false
end))))
in (match (_54_2995) with
| (tycons, rest) -> begin
(let _54_3004 = (FStar_All.pipe_right rest (FStar_List.partition (fun _54_15 -> (match (_54_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_54_2998) -> begin
true
end
| _54_3001 -> begin
false
end))))
in (match (_54_3004) with
| (abbrevs, rest) -> begin
(let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _54_16 -> (match (_54_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _145_1100 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _145_1100 Prims.fst))
end
| _54_3016 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _54_3019 -> begin
(FStar_All.failwith "impossible")
end))))
in (let _54_3023 = (FStar_List.split recs)
in (match (_54_3023) with
| (recs, abbrev_defs) -> begin
(let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _145_1101 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _145_1101))
end else begin
""
end
in (let _54_3025 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (let _54_3032 = (tc_decls false env tycons deserialized)
in (match (_54_3032) with
| (tycons, _54_3029, _54_3031) -> begin
(let _54_3038 = (tc_decls false env recs deserialized)
in (match (_54_3038) with
| (recs, _54_3035, _54_3037) -> begin
(let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (let _54_3045 = (tc_decls false env1 rest deserialized)
in (match (_54_3045) with
| (rest, _54_3042, _54_3044) -> begin
(let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(let tt = (let _145_1104 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _145_1104))
in (let _54_3061 = (tc_typ_trivial env1 tt)
in (match (_54_3061) with
| (tt, _54_3060) -> begin
(let _54_3070 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _54_3067 -> begin
([], tt)
end)
in (match (_54_3070) with
| (tps, t) -> begin
(let _145_1106 = (let _145_1105 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _145_1105, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_145_1106))
end))
end)))
end
| _54_3072 -> begin
(let _145_1108 = (let _145_1107 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _145_1107))
in (FStar_All.failwith _145_1108))
end)) recs abbrev_defs)
in (let _54_3074 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
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
and tc_decls = (fun for_export env ses deserialized -> (let time_tc_decl = (fun env se ds -> (let start = (FStar_Util.now ())
in (let res = (tc_decl env se ds)
in (let stop = (FStar_Util.now ())
in (let diff = (FStar_Util.time_diff start stop)
in (let _54_3090 = (let _145_1119 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _145_1119))
in res))))))
in (let _54_3108 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _54_3095 se -> (match (_54_3095) with
| (ses, all_non_private, env) -> begin
(let _54_3097 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _145_1123 = (let _145_1122 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _145_1122))
in (FStar_Util.print_string _145_1123))
end else begin
()
end
in (let _54_3101 = if (FStar_ST.read FStar_Options.timing) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_54_3101) with
| (se, env) -> begin
(let _54_3102 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in (let non_private_decls = if for_export then begin
(non_private env se)
end else begin
[]
end
in ((se)::ses, (non_private_decls)::all_non_private, env)))
end)))
end)) ([], [], env)))
in (match (_54_3108) with
| (ses, all_non_private, env) -> begin
(let _145_1124 = (FStar_All.pipe_right (FStar_List.rev all_non_private) FStar_List.flatten)
in ((FStar_List.rev ses), _145_1124, env))
end))))
and non_private = (fun env se -> (let is_private = (fun quals -> (FStar_List.contains FStar_Absyn_Syntax.Private quals))
in (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _54_3116, _54_3118) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_tycon (_54_3122, _54_3124, _54_3126, _54_3128, _54_3130, quals, r) -> begin
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
| FStar_Absyn_Syntax.Sig_assume (_54_3144, _54_3146, quals, _54_3149) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_val_decl (_54_3153, _54_3155, quals, _54_3158) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_main (_54_3162) -> begin
[]
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_datacon (_54_3180) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, _54_3186) -> begin
(let check_priv = (fun lbs -> (let is_priv = (fun _54_17 -> (match (_54_17) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _54_3197; FStar_Absyn_Syntax.lbeff = _54_3195; FStar_Absyn_Syntax.lbdef = _54_3193} -> begin
(match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some (_54_3202, qs) -> begin
(FStar_List.contains FStar_Absyn_Syntax.Private qs)
end
| _54_3207 -> begin
false
end)
end
| _54_3209 -> begin
false
end))
in (let some_priv = (FStar_All.pipe_right lbs (FStar_Util.for_some is_priv))
in if some_priv then begin
if (FStar_All.pipe_right lbs (FStar_Util.for_some (fun x -> (let _145_1134 = (is_priv x)
in (FStar_All.pipe_right _145_1134 Prims.op_Negation))))) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Some but not all functions in this mutually recursive nest are marked private", r))))
end else begin
true
end
end else begin
false
end)))
in (let _54_3216 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.partition (fun lb -> ((FStar_Absyn_Util.is_pure_or_ghost_function lb.FStar_Absyn_Syntax.lbtyp) && (let _145_1136 = (FStar_Absyn_Util.is_lemma lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_left Prims.op_Negation _145_1136))))))
in (match (_54_3216) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_54_3220::_54_3218, _54_3225::_54_3223) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_54_3231::_54_3229, []) -> begin
if (check_priv pure_funs) then begin
[]
end else begin
(se)::[]
end
end
| ([], _54_3239::_54_3237) -> begin
if (check_priv rest) then begin
[]
end else begin
(FStar_All.pipe_right rest (FStar_List.collect (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_54_3244) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Util.Inr (l) -> begin
(FStar_Absyn_Syntax.Sig_val_decl ((l, lb.FStar_Absyn_Syntax.lbtyp, (FStar_Absyn_Syntax.Assumption)::[], (FStar_Ident.range_of_lid l))))::[]
end))))
end
end
| ([], []) -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end)))

let get_exports = (fun env modul non_private_decls -> (let assume_vals = (fun decls -> (FStar_All.pipe_right decls (FStar_List.map (fun _54_18 -> (match (_54_18) with
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((lid, t, (FStar_Absyn_Syntax.Assumption)::quals, r))
end
| s -> begin
s
end)))))
in if modul.FStar_Absyn_Syntax.is_interface then begin
non_private_decls
end else begin
(let exports = (let _145_1149 = (FStar_Tc_Env.modules env)
in (FStar_Util.find_map _145_1149 (fun m -> if (m.FStar_Absyn_Syntax.is_interface && (FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name m.FStar_Absyn_Syntax.name)) then begin
(let _145_1148 = (FStar_All.pipe_right m.FStar_Absyn_Syntax.exports assume_vals)
in Some (_145_1148))
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
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (let msg = (Prims.strcat "Internals for " name)
in (let env = (let _54_3273 = env
in (let _145_1154 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _54_3273.FStar_Tc_Env.solver; FStar_Tc_Env.range = _54_3273.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _54_3273.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _54_3273.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _54_3273.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _54_3273.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _54_3273.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _54_3273.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _54_3273.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _54_3273.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _54_3273.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _54_3273.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _54_3273.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _54_3273.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _54_3273.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _54_3273.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _54_3273.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _145_1154; FStar_Tc_Env.default_effects = _54_3273.FStar_Tc_Env.default_effects}))
in (let _54_3276 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (let _54_3282 = (tc_decls true env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_54_3282) with
| (ses, non_private_decls, env) -> begin
((let _54_3283 = modul
in {FStar_Absyn_Syntax.name = _54_3283.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _54_3283.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _54_3283.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _54_3283.FStar_Absyn_Syntax.is_deserialized}), non_private_decls, env)
end))))))))

let tc_more_partial_modul = (fun env modul decls -> (let _54_3291 = (tc_decls true env decls false)
in (match (_54_3291) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _54_3292 = modul
in {FStar_Absyn_Syntax.name = _54_3292.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _54_3292.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _54_3292.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _54_3292.FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun env modul npds -> (let exports = (get_exports env modul npds)
in (let modul = (let _54_3299 = modul
in {FStar_Absyn_Syntax.name = _54_3299.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _54_3299.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (let env = (FStar_Tc_Env.finish_module env modul)
in (let _54_3309 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(let _54_3303 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (let _54_3305 = if ((not (modul.FStar_Absyn_Syntax.is_interface)) || (let _145_1167 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Absyn_Syntax.name.FStar_Ident.str _145_1167))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
end else begin
()
end
in (let _54_3307 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _145_1168 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _145_1168 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

let tc_modul = (fun env modul -> (let _54_3316 = (tc_partial_modul env modul)
in (match (_54_3316) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_Tc_Env.push_sigelt en elt)
in (let _54_3323 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _145_1181 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _145_1181 m)))))

let check_module = (fun env m -> (let _54_3328 = if ((let _145_1186 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _145_1186)) <> 0) then begin
(let _145_1187 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _145_1187))
end else begin
()
end
in (let _54_3341 = if m.FStar_Absyn_Syntax.is_deserialized then begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end else begin
(let _54_3333 = (tc_modul env m)
in (match (_54_3333) with
| (m, env) -> begin
(let _54_3337 = if (FStar_ST.read FStar_Options.serialize_mods) then begin
(let c_file_name = (let _145_1192 = (let _145_1191 = (let _145_1190 = (let _145_1189 = (let _145_1188 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _145_1188 "/"))
in (Prims.strcat _145_1189 FStar_Options.cache_dir))
in (Prims.strcat _145_1190 "/"))
in (Prims.strcat _145_1191 (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)))
in (Prims.strcat _145_1192 ".cache"))
in (let _54_3335 = (FStar_Util.print_string (Prims.strcat (Prims.strcat "Serializing module " (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)) "\n"))
in (let _145_1193 = (FStar_Util.get_owriter c_file_name)
in (FStar_Absyn_SSyntax.serialize_modul _145_1193 m))))
end else begin
()
end
in (m, env))
end))
end
in (match (_54_3341) with
| (m, env) -> begin
(let _54_3342 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _145_1194 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _145_1194))
end else begin
()
end
in ((m)::[], env))
end))))




