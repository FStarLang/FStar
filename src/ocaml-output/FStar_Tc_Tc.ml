
open Prims
let syn' = (fun env k -> (let _105_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _105_11 (Some (k)))))

let log = (fun env -> ((FStar_ST.read FStar_Options.log_types) && (not ((let _105_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _105_14))))))

let rng = (fun env -> (FStar_Tc_Env.get_range env))

let instantiate_both = (fun env -> (let _52_24 = env
in {FStar_Tc_Env.solver = _52_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _52_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_24.FStar_Tc_Env.default_effects}))

let no_inst = (fun env -> (let _52_27 = env
in {FStar_Tc_Env.solver = _52_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _52_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_27.FStar_Tc_Env.default_effects}))

let mk_lex_list = (fun vs -> (FStar_List.fold_right (fun v tl -> (let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _105_30 = (let _105_29 = (let _105_28 = (let _105_27 = (let _105_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _105_25 -> FStar_Util.Inl (_105_25)) _105_26))
in (_105_27, Some (FStar_Absyn_Syntax.Implicit)))
in (_105_28)::((FStar_Absyn_Syntax.varg v))::((FStar_Absyn_Syntax.varg tl))::[])
in (FStar_Absyn_Util.lex_pair, _105_29))
in (FStar_Absyn_Syntax.mk_Exp_app _105_30 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))

let is_eq = (fun _52_1 -> (match (_52_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _52_37 -> begin
false
end))

let steps = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)

let whnf = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))

let norm_t = (fun env t -> (let _105_43 = (steps env)
in (FStar_Tc_Normalize.norm_typ _105_43 env t)))

let norm_k = (fun env k -> (let _105_48 = (steps env)
in (FStar_Tc_Normalize.norm_kind _105_48 env k)))

let norm_c = (fun env c -> (let _105_53 = (steps env)
in (FStar_Tc_Normalize.norm_comp _105_53 env c)))

let fxv_check = (fun head env kt fvs -> (let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _105_72 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _105_72))
end
| FStar_Util.Inr (t) -> begin
(let _105_73 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _105_73))
end)
in (let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (norm)) then begin
(aux true kt)
end else begin
(let fail = (fun _52_61 -> (match (()) with
| () -> begin
(let escaping = (let _105_78 = (let _105_77 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _105_77 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _105_78 (FStar_String.concat ", ")))
in (let msg = if ((FStar_Util.set_count a) > 1) then begin
(let _105_79 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _105_79))
end else begin
(let _105_80 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _105_80))
end
in (let _105_83 = (let _105_82 = (let _105_81 = (FStar_Tc_Env.get_range env)
in (msg, _105_81))
in FStar_Absyn_Syntax.Error (_105_82))
in (Prims.raise _105_83))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _52_71 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _52_78 -> begin
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

let maybe_make_subst = (fun _52_2 -> (match (_52_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl ((a, t)))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr ((x, e)))::[]
end
| _52_99 -> begin
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
(let _105_94 = (let _105_93 = (let _105_92 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _105_92))
in FStar_Util.Inl (_105_93))
in (_105_94)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _105_97 = (let _105_96 = (let _105_95 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _105_95))
in FStar_Util.Inr (_105_96))
in (_105_97)::s)
end
end
| _52_114 -> begin
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
| _52_129 -> begin
(FStar_All.failwith "Impossible")
end)
end)

let set_lcomp_result = (fun lc t -> (let _52_132 = lc
in {FStar_Absyn_Syntax.eff_name = _52_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _52_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _52_134 -> (match (()) with
| () -> begin
(let _105_106 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _105_106 t))
end))}))

let value_check_expected_typ = (fun env e tlc -> (let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _105_113 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _105_113))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (let t = lc.FStar_Absyn_Syntax.res_typ
in (let _52_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_Tc_Rel.trivial_guard)
end
| Some (t') -> begin
(let _52_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_115 = (FStar_Absyn_Print.typ_to_string t)
in (let _105_114 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _105_115 _105_114)))
end else begin
()
end
in (let _52_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_52_151) with
| (e, g) -> begin
(let _52_154 = (let _105_121 = (FStar_All.pipe_left (fun _105_120 -> Some (_105_120)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _105_121 env e lc g))
in (match (_52_154) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))
end)))
end)
in (match (_52_158) with
| (e, lc, g) -> begin
(let _52_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_122 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _105_122))
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

let check_expected_effect = (fun env copt _52_171 -> (match (_52_171) with
| (e, c) -> begin
(let expected_c_opt = (match (copt) with
| Some (_52_173) -> begin
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
(let _105_135 = (norm_c env c)
in (e, _105_135, FStar_Tc_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(let _52_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_138 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _105_137 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _105_136 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _105_138 _105_137 _105_136))))
end else begin
()
end
in (let c = (norm_c env c)
in (let expected_c' = (let _105_139 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _105_139))
in (let _52_195 = (let _105_140 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _105_140))
in (match (_52_195) with
| (e, _52_193, g) -> begin
(let _52_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_142 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _105_141 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _105_142 _105_141)))
end else begin
()
end
in (e, expected_c, g))
end)))))
end))
end))

let no_logical_guard = (fun env _52_202 -> (match (_52_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
(te, kt, f)
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _105_148 = (let _105_147 = (let _105_146 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _105_145 = (FStar_Tc_Env.get_range env)
in (_105_146, _105_145)))
in FStar_Absyn_Syntax.Error (_105_147))
in (Prims.raise _105_148))
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
(let _105_155 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _105_155))
end))

let with_implicits = (fun imps _52_220 -> (match (_52_220) with
| (e, l, g) -> begin
(e, l, (let _52_221 = g
in {FStar_Tc_Rel.guard_f = _52_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _52_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)}))
end))

let add_implicit = (fun u g -> (let _52_225 = g
in {FStar_Tc_Rel.guard_f = _52_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _52_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))

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
(let _52_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _105_208 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _105_207 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _105_208 _105_207)))
end else begin
()
end
in (let _52_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_52_249) with
| (env, _52_248) -> begin
(let _52_252 = (tc_args env args)
in (match (_52_252) with
| (args, g) -> begin
(let _105_210 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar (u, args)))
in (_105_210, g))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _52_263; FStar_Absyn_Syntax.pos = _52_261; FStar_Absyn_Syntax.fvs = _52_259; FStar_Absyn_Syntax.uvs = _52_257}) -> begin
(let _52_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_52_272) with
| (_52_269, binders, body) -> begin
(let _52_275 = (tc_args env args)
in (match (_52_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _105_214 = (let _105_213 = (let _105_212 = (let _105_211 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _105_211))
in (_105_212, k.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_213))
in (Prims.raise _105_214))
end else begin
(let _52_308 = (FStar_List.fold_left2 (fun _52_279 b a -> (match (_52_279) with
| (subst, args, guards) -> begin
(match (((Prims.fst b), (Prims.fst a))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(let _52_289 = (let _105_218 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _105_218))
in (match (_52_289) with
| (t, g) -> begin
(let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t)))::subst
in (subst, ((FStar_Absyn_Syntax.targ t))::args, (g)::guards))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(let env = (let _105_219 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _105_219))
in (let _52_301 = (tc_ghost_exp env e)
in (match (_52_301) with
| (e, _52_299, g) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::subst
in (subst, ((FStar_Absyn_Syntax.varg e))::args, (g)::guards))
end)))
end
| _52_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Ill-typed argument to kind abbreviation", (FStar_Absyn_Util.range_of_arg a)))))
end)
end)) ([], [], []) binders args)
in (match (_52_308) with
| (subst, args, guards) -> begin
(let args = (FStar_List.rev args)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown)))
in (let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), k')))
in (let _105_222 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in (k', _105_222))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(let _52_319 = (tc_kind env k)
in (match (_52_319) with
| (k, f) -> begin
(let _52_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_52_322) with
| (args, g) -> begin
(let kabr = ((Prims.fst kabr), args)
in (let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev (kabr, k)))
in (let _105_224 = (FStar_Tc_Rel.conj_guard f g)
in (kk, _105_224))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _52_332 = (tc_binders env bs)
in (match (_52_332) with
| (bs, env, g) -> begin
(let _52_335 = (tc_kind env k)
in (match (_52_335) with
| (k, f) -> begin
(let f = (FStar_Tc_Rel.close_guard bs f)
in (let _105_227 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k)))
in (let _105_226 = (FStar_Tc_Rel.conj_guard g f)
in (_105_227, _105_226))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _105_228 = (FStar_Tc_Util.new_kvar env)
in (_105_228, FStar_Tc_Rel.trivial_guard))
end))))
and tc_vbinder = (fun env x -> (let _52_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_52_342) with
| (t, g) -> begin
(let x = (let _52_343 = x
in {FStar_Absyn_Syntax.v = _52_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _52_343.FStar_Absyn_Syntax.p})
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
(let _52_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_52_362) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _52_363 = a
in {FStar_Absyn_Syntax.v = _52_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _52_363.FStar_Absyn_Syntax.p})), imp)
in (let env' = (maybe_push_binding env b)
in (let _52_370 = (aux env' bs)
in (match (_52_370) with
| (bs, env', g') -> begin
(let _105_238 = (let _105_237 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _105_237))
in ((b)::bs, env', _105_238))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(let _52_376 = (tc_vbinder env x)
in (match (_52_376) with
| (x, env', g) -> begin
(let b = (FStar_Util.Inr (x), imp)
in (let _52_381 = (aux env' bs)
in (match (_52_381) with
| (bs, env', g') -> begin
(let _105_240 = (let _105_239 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _105_239))
in ((b)::bs, env', _105_240))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args = (fun env args -> (FStar_List.fold_right (fun _52_386 _52_389 -> (match ((_52_386, _52_389)) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(let _52_396 = (tc_typ env t)
in (match (_52_396) with
| (t, _52_394, g') -> begin
(let _105_245 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inl (t), imp))::args, _105_245))
end))
end
| FStar_Util.Inr (e) -> begin
(let _52_403 = (tc_ghost_exp env e)
in (match (_52_403) with
| (e, _52_401, g') -> begin
(let _105_246 = (FStar_Tc_Rel.conj_guard g g')
in (((FStar_Util.Inr (e), imp))::args, _105_246))
end))
end)
end)) args ([], FStar_Tc_Rel.trivial_guard)))
and tc_pats = (fun env pats -> (FStar_List.fold_right (fun p _52_409 -> (match (_52_409) with
| (pats, g) -> begin
(let _52_412 = (tc_args env p)
in (match (_52_412) with
| (args, g') -> begin
(let _105_251 = (FStar_Tc_Rel.conj_guard g g')
in ((args)::pats, _105_251))
end))
end)) pats ([], FStar_Tc_Rel.trivial_guard)))
and tc_comp = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _52_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_52_419) with
| (t, g) -> begin
(let _105_254 = (FStar_Absyn_Syntax.mk_Total t)
in (_105_254, g))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (let tc = (FStar_Absyn_Syntax.mk_Typ_app (head, ((FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ))::c.FStar_Absyn_Syntax.effect_args) None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos)
in (let _52_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_52_427) with
| (tc, f) -> begin
(let _52_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_52_431) with
| (_52_429, args) -> begin
(let _52_443 = (match (args) with
| (FStar_Util.Inl (res), _52_436)::args -> begin
(res, args)
end
| _52_440 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_52_443) with
| (res, args) -> begin
(let _52_459 = (let _105_256 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _52_3 -> (match (_52_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _52_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_52_450) with
| (env, _52_449) -> begin
(let _52_455 = (tc_ghost_exp env e)
in (match (_52_455) with
| (e, _52_453, g) -> begin
(FStar_Absyn_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_Tc_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _105_256 FStar_List.unzip))
in (match (_52_459) with
| (flags, guards) -> begin
(let _105_258 = (FStar_Absyn_Syntax.mk_Comp (let _52_460 = c
in {FStar_Absyn_Syntax.effect_name = _52_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _52_460.FStar_Absyn_Syntax.flags}))
in (let _105_257 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in (_105_258, _105_257)))
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
in (let a = (let _52_472 = a
in {FStar_Absyn_Syntax.v = _52_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _52_472.FStar_Absyn_Syntax.p})
in (let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (let _52_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_52_479) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.eqT_k k)
in (let i = (let _52_484 = i
in {FStar_Absyn_Syntax.v = _52_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _52_484.FStar_Absyn_Syntax.p})
in (let _105_281 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_105_281, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let qk = (FStar_Absyn_Util.allT_k k)
in (let i = (let _52_491 = i
in {FStar_Absyn_Syntax.v = _52_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _52_491.FStar_Absyn_Syntax.p})
in (let _105_282 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in (_105_282, qk, FStar_Tc_Rel.trivial_guard)))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _52_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (let i = (let _52_501 = i
in {FStar_Absyn_Syntax.v = _52_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _52_501.FStar_Absyn_Syntax.p})
in (let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (let _52_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_52_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) (t, k, FStar_Tc_Rel.trivial_guard))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(let _52_516 = (tc_binders env bs)
in (match (_52_516) with
| (bs, env, g) -> begin
(let _52_519 = (tc_comp env cod)
in (match (_52_519) with
| (cod, f) -> begin
(let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun (bs, cod)))
in (let _52_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _52_542; FStar_Absyn_Syntax.result_typ = _52_540; FStar_Absyn_Syntax.effect_args = (FStar_Util.Inl (pre), _52_536)::(FStar_Util.Inl (post), _52_531)::(FStar_Util.Inr (pats), _52_526)::[]; FStar_Absyn_Syntax.flags = _52_522}) -> begin
(let rec extract_pats = (fun pats -> (match ((let _105_287 = (FStar_Absyn_Util.compress_exp pats)
in _105_287.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _52_557); FStar_Absyn_Syntax.tk = _52_554; FStar_Absyn_Syntax.pos = _52_552; FStar_Absyn_Syntax.fvs = _52_550; FStar_Absyn_Syntax.uvs = _52_548}, _52_572::(FStar_Util.Inr (hd), _52_569)::(FStar_Util.Inr (tl), _52_564)::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _52_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_52_578) with
| (head, args) -> begin
(let pat = (match (args) with
| (_::arg::[]) | (arg::[]) -> begin
(arg)::[]
end
| _52_585 -> begin
[]
end)
in (let _105_288 = (extract_pats tl)
in (FStar_List.append pat _105_288)))
end))
end
| _52_588 -> begin
[]
end))
in (let pats = (let _105_289 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _105_289))
in (let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _52_594 -> (match (_52_594) with
| (b, _52_593) -> begin
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
(let _105_292 = (let _105_291 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _105_291))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _105_292))
end))))
end
| _52_603 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end
in (let _105_294 = (let _105_293 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _105_293))
in (t, FStar_Absyn_Syntax.ktype, _105_294))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(let _52_613 = (tc_binders env bs)
in (match (_52_613) with
| (bs, env, g) -> begin
(let _52_617 = (tc_typ env t)
in (match (_52_617) with
| (t, k, f) -> begin
(let k = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) top.FStar_Absyn_Syntax.pos)
in (let _105_299 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam (bs, t)))
in (let _105_298 = (let _105_297 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _105_297))
in (_105_299, k, _105_298))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(let _52_626 = (tc_vbinder env x)
in (match (_52_626) with
| (x, env, f1) -> begin
(let _52_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_302 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _105_301 = (FStar_Absyn_Print.typ_to_string phi)
in (let _105_300 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _105_302 _105_301 _105_300))))
end else begin
()
end
in (let _52_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_52_634) with
| (phi, f2) -> begin
(let _105_307 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine (x, phi)))
in (let _105_306 = (let _105_305 = (FStar_Tc_Rel.close_guard (((FStar_Absyn_Syntax.v_binder x))::[]) f2)
in (FStar_Tc_Rel.conj_guard f1 _105_305))
in (_105_307, FStar_Absyn_Syntax.ktype, _105_306)))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let _52_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_310 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _105_309 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _105_308 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _105_310 _105_309 _105_308))))
end else begin
()
end
in (let _52_644 = (tc_typ (no_inst env) head)
in (match (_52_644) with
| (head, k1', f1) -> begin
(let args0 = args
in (let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (let _52_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_314 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _105_313 = (FStar_Absyn_Print.typ_to_string head)
in (let _105_312 = (FStar_Absyn_Print.kind_to_string k1')
in (let _105_311 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _105_314 _105_313 _105_312 _105_311)))))
end else begin
()
end
in (let check_app = (fun _52_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_52_652) -> begin
(let _52_656 = (tc_args env args)
in (match (_52_656) with
| (args, g) -> begin
(let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (let kres = (let _105_317 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _105_317 Prims.fst))
in (let bs = (let _105_318 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _105_318))
in (let kar = (FStar_Absyn_Syntax.mk_Kind_arrow (bs, kres) k1.FStar_Absyn_Syntax.pos)
in (let _52_662 = (let _105_319 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _105_319))
in (kres, args, g)))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(let rec check_args = (fun outargs subst g formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let _105_330 = (FStar_Absyn_Util.subst_kind subst kres)
in (_105_330, (FStar_List.rev outargs), g))
end
| (((_, None)::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) | (((_, Some (FStar_Absyn_Syntax.Equality))::_, (_, Some (FStar_Absyn_Syntax.Implicit))::_)) -> begin
(let _105_334 = (let _105_333 = (let _105_332 = (let _105_331 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _105_331))
in ("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit", _105_332))
in FStar_Absyn_Syntax.Error (_105_333))
in (Prims.raise _105_334))
end
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _52_735 = (let _105_335 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _105_335))
in (match (_52_735) with
| (t, u) -> begin
(let targ = (FStar_Util.Inl (t), Some (FStar_Absyn_Syntax.Implicit))
in (let g = (add_implicit (FStar_Util.Inl (u)) g)
in (let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_, None)::_)) | (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, [])) -> begin
(let formal = (FStar_List.hd formals)
in (let _52_764 = (let _105_336 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _105_336))
in (match (_52_764) with
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
in (let _52_785 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_338 = (FStar_Absyn_Print.arg_to_string actual)
in (let _105_337 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _105_338 _105_337)))
end else begin
()
end
in (let _52_791 = (tc_typ_check (let _52_787 = env
in {FStar_Tc_Env.solver = _52_787.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_787.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_787.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_787.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_787.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_787.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_787.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_787.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_787.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_787.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_787.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_787.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_787.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_787.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_787.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_787.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _52_787.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_787.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_787.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_52_791) with
| (t, g') -> begin
(let _52_792 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_339 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _105_339))
end else begin
()
end
in (let actual = (FStar_Util.Inl (t), imp)
in (let g' = (let _105_341 = (let _105_340 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _105_340))
in (FStar_Tc_Rel.imp_guard _105_341 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _105_342 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _105_342 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (let env' = (let _52_808 = env'
in {FStar_Tc_Env.solver = _52_808.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_808.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_808.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_808.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_808.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_808.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_808.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_808.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_808.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_808.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_808.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_808.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_808.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_808.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_808.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_808.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _52_808.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_808.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_808.FStar_Tc_Env.default_effects})
in (let _52_811 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_344 = (FStar_Absyn_Print.arg_to_string actual)
in (let _105_343 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _105_344 _105_343)))
end else begin
()
end
in (let _52_817 = (tc_ghost_exp env' v)
in (match (_52_817) with
| (v, _52_815, g') -> begin
(let actual = (FStar_Util.Inr (v), imp)
in (let g' = (let _105_346 = (let _105_345 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _105_345))
in (FStar_Tc_Rel.imp_guard _105_346 g'))
in (let subst = (maybe_extend_subst subst formal actual)
in (let _105_347 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _105_347 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _52_824), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(let tv = (FStar_Absyn_Util.b2t v)
in (check_args outargs subst g ((formal)::formals) (((FStar_Absyn_Syntax.targ tv))::actuals)))
end
| _52_834 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected a type; got an expression", v.FStar_Absyn_Syntax.pos))))
end)
end
| ((FStar_Util.Inr (_52_836), _52_839), (FStar_Util.Inl (_52_842), _52_845)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected an expression; got a type", (FStar_Absyn_Util.range_of_arg actual)))))
end)
end
| (_52_849, []) -> begin
(let _105_349 = (let _105_348 = (FStar_Absyn_Syntax.mk_Kind_arrow (formals, kres) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _105_348))
in (_105_349, (FStar_List.rev outargs), g))
end
| ([], _52_854) -> begin
(let _105_357 = (let _105_356 = (let _105_355 = (let _105_354 = (let _105_352 = (let _105_351 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _52_4 -> (match (_52_4) with
| (_52_858, Some (FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _52_863 -> begin
true
end))))
in (FStar_List.length _105_351))
in (FStar_All.pipe_right _105_352 FStar_Util.string_of_int))
in (let _105_353 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _105_354 _105_353)))
in (_105_355, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_356))
in (Prims.raise _105_357))
end))
in (check_args [] [] f1 formals args))
end
| _52_865 -> begin
(let _105_360 = (let _105_359 = (let _105_358 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in (_105_358, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_359))
in (Prims.raise _105_360))
end)
end))
in (match ((let _105_364 = (let _105_361 = (FStar_Absyn_Util.compress_typ head)
in _105_361.FStar_Absyn_Syntax.n)
in (let _105_363 = (let _105_362 = (FStar_Absyn_Util.compress_kind k1)
in _105_362.FStar_Absyn_Syntax.n)
in (_105_364, _105_363)))) with
| (FStar_Absyn_Syntax.Typ_uvar (_52_867), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(let result_k = (let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in (t, result_k, FStar_Tc_Rel.trivial_guard)))
end
| _52_878 -> begin
(let _52_882 = (check_app ())
in (match (_52_882) with
| (k, args, g) -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (head, args) (Some (k)) top.FStar_Absyn_Syntax.pos)
in (t, k, g))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(let _52_890 = (tc_kind env k1)
in (match (_52_890) with
| (k1, f1) -> begin
(let _52_893 = (tc_typ_check env t1 k1)
in (match (_52_893) with
| (t1, f2) -> begin
(let _105_368 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' (t1, k1)))
in (let _105_367 = (FStar_Tc_Rel.conj_guard f1 f2)
in (_105_368, k1, _105_367)))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_52_895, k1) -> begin
(let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(let _52_904 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _105_370 = (FStar_Absyn_Print.typ_to_string s)
in (let _105_369 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _105_370 _105_369)))
end else begin
()
end
in (let _105_373 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' (u, k1)))
in (_105_373, k1, FStar_Tc_Rel.trivial_guard)))
end
| _52_907 -> begin
(let _52_908 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _105_375 = (FStar_Absyn_Print.typ_to_string s)
in (let _105_374 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _105_375 _105_374)))
end else begin
()
end
in (s, k1, FStar_Tc_Rel.trivial_guard))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(let _52_919 = (tc_typ env t)
in (match (_52_919) with
| (t, k, f) -> begin
(let _105_376 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label ((t, b, r))))
in (_105_376, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(let _52_930 = (tc_typ env t)
in (match (_52_930) with
| (t, k, f) -> begin
(let _105_377 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((t, l, r, p))))
in (_105_377, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(let _52_939 = (tc_typ env t)
in (match (_52_939) with
| (t, k, f) -> begin
(let _105_378 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, l))))
in (_105_378, k, f))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(let _52_947 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_52_947) with
| (quant, f) -> begin
(let _52_950 = (tc_pats env pats)
in (match (_52_950) with
| (pats, g) -> begin
(let g = (let _52_951 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _52_951.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_951.FStar_Tc_Rel.implicits})
in (let _105_381 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((quant, pats))))
in (let _105_380 = (FStar_Tc_Util.force_tk quant)
in (let _105_379 = (FStar_Tc_Rel.conj_guard f g)
in (_105_381, _105_380, _105_379)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let k = (FStar_Tc_Util.new_kvar env)
in (let t = (FStar_Tc_Util.new_tvar env k)
in (t, k, FStar_Tc_Rel.trivial_guard)))
end
| _52_958 -> begin
(let _105_383 = (let _105_382 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _105_382))
in (FStar_All.failwith _105_383))
end))))))
and tc_typ_check = (fun env t k -> (let _52_965 = (tc_typ env t)
in (match (_52_965) with
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
| FStar_Absyn_Syntax.Exp_uvar (_52_974, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (FStar_Tc_Env.lookup_bvar env x)
in (let e = (FStar_Absyn_Syntax.mk_Exp_bvar (let _52_981 = x
in {FStar_Absyn_Syntax.v = _52_981.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _52_981.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _52_987 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_52_987) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _105_390 = (let _105_389 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _105_389))
in FStar_Util.Inr (_105_390))
end
in (let _105_391 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _105_391)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (let e = (FStar_Absyn_Syntax.mk_Exp_fvar ((let _52_994 = v
in {FStar_Absyn_Syntax.v = _52_994.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _52_994.FStar_Absyn_Syntax.p}), dc) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (let _52_1000 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_52_1000) with
| (e, t, implicits) -> begin
(let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _105_393 = (let _105_392 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _105_392))
in FStar_Util.Inr (_105_393))
end
in (let is_data_ctor = (fun _52_5 -> (match (_52_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _52_1010 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _105_399 = (let _105_398 = (let _105_397 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _105_396 = (FStar_Tc_Env.get_range env)
in (_105_397, _105_396)))
in FStar_Absyn_Syntax.Error (_105_398))
in (Prims.raise _105_399))
end else begin
(let _105_400 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _105_400))
end))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fail = (fun msg t -> (let _105_405 = (let _105_404 = (let _105_403 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_105_403, top.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_404))
in (Prims.raise _105_405)))
in (let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(let _52_1031 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _52_1030 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _52_1036 = (tc_binders env bs)
in (match (_52_1036) with
| (bs, envbody, g) -> begin
(None, bs, [], None, envbody, g)
end)))
end
| Some (t) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (let rec as_function_typ = (fun norm t -> (match ((let _105_414 = (FStar_Absyn_Util.compress_typ t)
in _105_414.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _52_1065 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _52_1064 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _52_1070 = (tc_binders env bs)
in (match (_52_1070) with
| (bs, envbody, g) -> begin
(let _52_1074 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_52_1074) with
| (envbody, _52_1073) -> begin
(Some ((t, true)), bs, [], None, envbody, g)
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let rec tc_binders = (fun _52_1084 bs_annot c bs -> (match (_52_1084) with
| (out, env, g, subst) -> begin
(match ((bs_annot, bs)) with
| ([], []) -> begin
(let _105_423 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _105_423))
end
| (hdannot::tl_annot, hd::tl) -> begin
(match ((hdannot, hd)) with
| ((FStar_Util.Inl (_52_1099), _52_1102), (FStar_Util.Inr (_52_1105), _52_1108)) -> begin
(let env = (maybe_push_binding env hdannot)
in (tc_binders ((hdannot)::out, env, g, subst) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _52_1115), (FStar_Util.Inl (b), imp)) -> begin
(let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1133 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(ka, FStar_Tc_Rel.trivial_guard)
end
| _52_1125 -> begin
(let _52_1128 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_52_1128) with
| (k, g1) -> begin
(let g2 = (FStar_Tc_Rel.keq env None ka k)
in (let g = (let _105_424 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _105_424))
in (k, g)))
end))
end)
in (match (_52_1133) with
| (k, g) -> begin
(let b = (FStar_Util.Inl ((let _52_1134 = b
in {FStar_Absyn_Syntax.v = _52_1134.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _52_1134.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _52_1142), (FStar_Util.Inr (y), imp)) -> begin
(let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1164 = (match ((let _105_425 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _105_425.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(tx, g)
end
| _52_1152 -> begin
(let _52_1153 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_426 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _105_426))
end else begin
()
end
in (let _52_1159 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_52_1159) with
| (t, _52_1157, g1) -> begin
(let g2 = (FStar_Tc_Rel.teq env tx t)
in (let g = (let _105_427 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _105_427))
in (t, g)))
end)))
end)
in (match (_52_1164) with
| (t, g) -> begin
(let b = (FStar_Util.Inr ((let _52_1165 = y
in {FStar_Absyn_Syntax.v = _52_1165.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _52_1165.FStar_Absyn_Syntax.p})), imp)
in (let env = (maybe_push_binding env b)
in (let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders ((b)::out, env, g, subst) tl_annot c tl))))
end)))
end
| _52_1171 -> begin
(let _105_430 = (let _105_429 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _105_428 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _105_429 _105_428)))
in (fail _105_430 t))
end)
end
| ([], _52_1174) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _52_1183; FStar_Absyn_Syntax.pos = _52_1181; FStar_Absyn_Syntax.fvs = _52_1179; FStar_Absyn_Syntax.uvs = _52_1177} -> begin
(tc_binders (out, env, g, subst) bs_annot c' bs)
end
| t -> begin
(let _105_432 = (let _105_431 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _105_431))
in (fail _105_432 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_52_1191, []) -> begin
(let c = (let _105_433 = (FStar_Absyn_Syntax.mk_Typ_fun (bs_annot, c) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _105_433 c.FStar_Absyn_Syntax.pos))
in (let _105_434 = (FStar_Absyn_Util.subst_comp subst c)
in ((FStar_List.rev out), env, g, _105_434)))
end)
end))
in (let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
(env, [])
end
| letrecs -> begin
(let _52_1200 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_439 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _105_439))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let env = (let _52_1203 = env
in {FStar_Tc_Env.solver = _52_1203.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_1203.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_1203.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_1203.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_1203.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_1203.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_1203.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_1203.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_1203.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_1203.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_1203.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_1203.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_1203.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _52_1203.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_1203.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_1203.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_1203.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_1203.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_1203.FStar_Tc_Env.default_effects})
in (let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_52_1210), _52_1213) -> begin
[]
end
| (FStar_Util.Inr (x), _52_1218) -> begin
(match ((let _105_445 = (let _105_444 = (let _105_443 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _105_443))
in (FStar_Absyn_Util.unrefine _105_444))
in _105_445.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_52_1221) -> begin
[]
end
| _52_1224 -> begin
(let _105_446 = (FStar_Absyn_Util.bvar_to_exp x)
in (_105_446)::[])
end)
end)))))
in (let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (let as_lex_list = (fun dec -> (let _52_1231 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_52_1231) with
| (head, _52_1230) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _52_1234) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _52_1238 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (let prev_dec = (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _52_6 -> (match (_52_6) with
| FStar_Absyn_Syntax.DECREASES (_52_1242) -> begin
true
end
| _52_1245 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let _52_1249 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _105_455 = (let _105_454 = (let _105_453 = (let _105_451 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _105_450 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _105_451 _105_450)))
in (let _105_452 = (FStar_Tc_Env.get_range env)
in (_105_453, _105_452)))
in FStar_Absyn_Syntax.Error (_105_454))
in (Prims.raise _105_455))
end else begin
()
end
in (let dec = (as_lex_list dec)
in (let subst = (FStar_List.map2 (fun b a -> (match ((b, a)) with
| ((FStar_Util.Inl (formal), _52_1257), (FStar_Util.Inl (actual), _52_1262)) -> begin
(let _105_459 = (let _105_458 = (FStar_Absyn_Util.btvar_to_typ actual)
in (formal.FStar_Absyn_Syntax.v, _105_458))
in FStar_Util.Inl (_105_459))
end
| ((FStar_Util.Inr (formal), _52_1268), (FStar_Util.Inr (actual), _52_1273)) -> begin
(let _105_461 = (let _105_460 = (FStar_Absyn_Util.bvar_to_exp actual)
in (formal.FStar_Absyn_Syntax.v, _105_460))
in FStar_Util.Inr (_105_461))
end
| _52_1277 -> begin
(FStar_All.failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _52_1280 -> begin
(let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| i::[] -> begin
i
end
| _52_1285 -> begin
(mk_lex_list actual_args)
end))
end))
in (let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _52_1289 -> (match (_52_1289) with
| (l, t0) -> begin
(let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _105_463 = (FStar_Absyn_Util.compress_typ t)
in _105_463.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _52_7 -> (match (_52_7) with
| FStar_Absyn_Syntax.DECREASES (_52_1305) -> begin
true
end
| _52_1308 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(let dec = (as_lex_list dec)
in (let dec = (let subst = (let _105_467 = (let _105_466 = (let _105_465 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _105_465))
in FStar_Util.Inr (_105_466))
in (_105_467)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (FStar_Absyn_Syntax.mk_Typ_app (precedes, ((FStar_Absyn_Syntax.varg dec))::((FStar_Absyn_Syntax.varg prev_dec))::[]) None r)))
end
| _52_1316 -> begin
(let formal_args = (FStar_All.pipe_right (FStar_List.append bs (((FStar_Absyn_Syntax.v_binder y))::[])) filter_types_and_functions)
in (let lhs = (match (formal_args) with
| i::[] -> begin
i
end
| _52_1321 -> begin
(mk_lex_list formal_args)
end)
in (FStar_Absyn_Syntax.mk_Typ_app (precedes, ((FStar_Absyn_Syntax.varg lhs))::((FStar_Absyn_Syntax.varg prev_dec))::[]) None r)))
end)
in (let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine (y, precedes) None r)
in (let bs = (FStar_List.append bs (((FStar_Util.Inr ((let _52_1325 = x
in {FStar_Absyn_Syntax.v = _52_1325.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _52_1325.FStar_Absyn_Syntax.p})), imp))::[]))
in (let t' = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None r)
in (let _52_1329 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_470 = (FStar_Absyn_Print.lbname_to_string l)
in (let _105_469 = (FStar_Absyn_Print.typ_to_string t)
in (let _105_468 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _105_470 _105_469 _105_468))))
end else begin
()
end
in (let _52_1336 = (let _105_472 = (let _105_471 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _105_471 Prims.fst))
in (tc_typ _105_472 t'))
in (match (_52_1336) with
| (t', _52_1333, _52_1335) -> begin
(l, t')
end)))))))))
end
| _52_1338 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _52_1340 -> begin
(FStar_All.failwith "Impossible")
end))
end))))
in (let _105_477 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _52_1345 -> (match (_52_1345) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _105_476 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _52_8 -> (match (_52_8) with
| (FStar_Util.Inl (x), t) -> begin
((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::[]
end
| _52_1352 -> begin
[]
end))))
in (_105_477, _105_476)))))))))))
end))
in (let _52_1357 = (tc_binders ([], env, FStar_Tc_Rel.trivial_guard, []) bs' c bs)
in (match (_52_1357) with
| (bs, envbody, g, c) -> begin
(let _52_1360 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
(envbody, [])
end
in (match (_52_1360) with
| (envbody, letrecs) -> begin
(let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, g))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _52_1364) -> begin
(let _52_1374 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_52_1374) with
| (_52_1368, bs, bs', copt, env, g) -> begin
(Some ((t, false)), bs, bs', copt, env, g)
end))
end
| _52_1376 -> begin
if (not (norm)) then begin
(let _105_478 = (whnf env t)
in (as_function_typ true _105_478))
end else begin
(let _52_1385 = (expected_function_typ env None)
in (match (_52_1385) with
| (_52_1378, bs, _52_1381, c_opt, envbody, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (let use_eq = env.FStar_Tc_Env.use_eq
in (let _52_1389 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_52_1389) with
| (env, topt) -> begin
(let _52_1396 = (expected_function_typ env topt)
in (match (_52_1396) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(let _52_1402 = (tc_exp (let _52_1397 = envbody
in {FStar_Tc_Env.solver = _52_1397.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_1397.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_1397.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_1397.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_1397.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_1397.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_1397.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_1397.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_1397.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_1397.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_1397.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_1397.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_1397.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_1397.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _52_1397.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _52_1397.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_1397.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_1397.FStar_Tc_Env.default_effects}) body)
in (match (_52_1402) with
| (body, cbody, guard_body) -> begin
(let _52_1403 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _105_481 = (FStar_Absyn_Print.exp_to_string body)
in (let _105_480 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _105_479 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _105_481 _105_480 _105_479))))
end else begin
()
end
in (let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (let _52_1406 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _105_482 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _105_482))
end else begin
()
end
in (let _52_1413 = (let _105_484 = (let _105_483 = (cbody.FStar_Absyn_Syntax.comp ())
in (body, _105_483))
in (check_expected_effect (let _52_1408 = envbody
in {FStar_Tc_Env.solver = _52_1408.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_1408.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_1408.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_1408.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_1408.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_1408.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_1408.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_1408.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_1408.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_1408.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_1408.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_1408.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_1408.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_1408.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_1408.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_1408.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _52_1408.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_1408.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_1408.FStar_Tc_Env.default_effects}) c_opt _105_484))
in (match (_52_1413) with
| (body, cbody, guard) -> begin
(let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(let _52_1415 = (let _105_485 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _105_485))
in (let _52_1417 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _52_1417.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _52_1417.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cbody) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (let e = (let _105_487 = (let _105_486 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in (_105_486, tfun_computed, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _105_487 None top.FStar_Absyn_Syntax.pos))
in (let _52_1440 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_52_1429) -> begin
(let _105_490 = (let _105_489 = (let _105_488 = (FStar_Absyn_Syntax.mk_Exp_abs (bs, body) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (_105_488, t, Some (FStar_Absyn_Const.effect_Tot_lid)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _105_489 None top.FStar_Absyn_Syntax.pos))
in (_105_490, t, guard))
end
| _52_1432 -> begin
(let _52_1435 = if use_teq then begin
(let _105_491 = (FStar_Tc_Rel.teq env t tfun_computed)
in (e, _105_491))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_52_1435) with
| (e, guard') -> begin
(let _105_493 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, t, Some (FStar_Absyn_Const.effect_Tot_lid)) None top.FStar_Absyn_Syntax.pos)
in (let _105_492 = (FStar_Tc_Rel.conj_guard guard guard')
in (_105_493, t, _105_492)))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_52_1440) with
| (e, tfun, guard) -> begin
(let _52_1441 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_496 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _105_495 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _105_494 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _105_496 _105_495 _105_494))))
end else begin
()
end
in (let c = if env.FStar_Tc_Env.top_level then begin
(FStar_Absyn_Syntax.mk_Total tfun)
end else begin
(FStar_Tc_Util.return_value env tfun e)
end
in (let _52_1446 = (let _105_498 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _105_498 guard))
in (match (_52_1446) with
| (c, g) -> begin
(e, c, g)
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _52_1448 -> begin
(let _105_500 = (let _105_499 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _105_499))
in (FStar_All.failwith _105_500))
end))))
and tc_exp = (fun env e -> (let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (let _52_1452 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_505 = (let _105_503 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _105_503))
in (let _105_504 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _105_505 _105_504)))
end else begin
()
end
in (let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_52_1458) -> begin
(let _105_529 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _105_529))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _52_1478) -> begin
(let _52_1483 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_52_1483) with
| (t1, f) -> begin
(let _52_1487 = (let _105_530 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _105_530 e1))
in (match (_52_1487) with
| (e1, c, g) -> begin
(let _52_1491 = (let _105_534 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _52_1488 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _105_534 e1 c f))
in (match (_52_1491) with
| (c, f) -> begin
(let _52_1495 = (let _105_538 = (let _105_537 = (w c)
in (FStar_All.pipe_left _105_537 (FStar_Absyn_Syntax.mk_Exp_ascribed (e1, t1, Some (c.FStar_Absyn_Syntax.eff_name)))))
in (comp_check_expected_typ env _105_538 c))
in (match (_52_1495) with
| (e, c, f2) -> begin
(let _105_540 = (let _105_539 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _105_539))
in (e, c, _105_540))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(let pats_t = (let _105_546 = (let _105_545 = (let _105_541 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _105_541))
in (let _105_544 = (let _105_543 = (let _105_542 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _105_542))
in (_105_543)::[])
in (_105_545, _105_544)))
in (FStar_Absyn_Syntax.mk_Typ_app _105_546 None FStar_Absyn_Syntax.dummyRange))
in (let _52_1505 = (let _105_547 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _105_547 e))
in (match (_52_1505) with
| (e, t, g) -> begin
(let g = (let _52_1506 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _52_1506.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_1506.FStar_Tc_Rel.implicits})
in (let c = (let _105_548 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _105_548 FStar_Tc_Util.lcomp_of_comp))
in (e, c, g)))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _105_549 = (FStar_Absyn_Util.compress_exp e)
in _105_549.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_52_1516, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _52_1521; FStar_Absyn_Syntax.lbeff = _52_1519; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _52_1532 = (let _105_550 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _105_550 e1))
in (match (_52_1532) with
| (e1, c1, g1) -> begin
(let _52_1536 = (tc_exp env e2)
in (match (_52_1536) with
| (e2, c2, g2) -> begin
(let c = (FStar_Tc_Util.bind env (Some (e1)) c1 (None, c2))
in (let _105_558 = (let _105_556 = (let _105_555 = (let _105_554 = (let _105_553 = (w c)
in (FStar_All.pipe_left _105_553 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, FStar_Tc_Recheck.t_unit, e1)))::[]), e2))))
in (_105_554, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_105_555))
in (FStar_Absyn_Syntax.mk_Exp_meta _105_556))
in (let _105_557 = (FStar_Tc_Rel.conj_guard g1 g2)
in (_105_558, c, _105_557))))
end))
end))
end
| _52_1539 -> begin
(let _52_1543 = (tc_exp env e)
in (match (_52_1543) with
| (e, c, g) -> begin
(let _105_559 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Sequence))))
in (_105_559, c, g))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(let _52_1552 = (tc_exp env e)
in (match (_52_1552) with
| (e, c, g) -> begin
(let _105_560 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, i))))
in (_105_560, c, g))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(let env0 = env
in (let env = (let _105_562 = (let _105_561 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _105_561 Prims.fst))
in (FStar_All.pipe_right _105_562 instantiate_both))
in (let _52_1559 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_564 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _105_563 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _105_564 _105_563)))
end else begin
()
end
in (let _52_1564 = (tc_exp (no_inst env) head)
in (match (_52_1564) with
| (head, chead, g_head) -> begin
(let aux = (fun _52_1566 -> (match (()) with
| () -> begin
(let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _52_1570) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = 2)) -> begin
(let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| (FStar_Util.Inr (e1), _52_1582)::(FStar_Util.Inr (e2), _52_1577)::[] -> begin
(let _52_1588 = (tc_exp env e1)
in (match (_52_1588) with
| (e1, c1, g1) -> begin
(let _52_1592 = (tc_exp env e2)
in (match (_52_1592) with
| (e2, c2, g2) -> begin
(let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (let c2 = if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _105_570 = (let _105_567 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _105_567))
in (let _105_569 = (let _105_568 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _105_568 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _105_570 c2 _105_569)))
end else begin
(let _105_574 = (let _105_571 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _105_571))
in (let _105_573 = (let _105_572 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _105_572 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _105_574 _105_573 c2)))
end
in (let c = (let _105_577 = (let _105_576 = (FStar_All.pipe_left (fun _105_575 -> Some (_105_575)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, FStar_Absyn_Util.t_bool))))
in (_105_576, c2))
in (FStar_Tc_Util.bind env None c1 _105_577))
in (let e = (FStar_Absyn_Syntax.mk_Exp_app (head, ((FStar_Absyn_Syntax.varg e1))::((FStar_Absyn_Syntax.varg e2))::[]) (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos)
in (let _105_579 = (let _105_578 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _105_578))
in (e, c, _105_579)))))))
end))
end))
end
| _52_1599 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Expected two boolean arguments", head.FStar_Absyn_Syntax.pos))))
end))
end
| _52_1601 -> begin
(let thead = chead.FStar_Absyn_Syntax.res_typ
in (let _52_1603 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_581 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _105_580 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _105_581 _105_580)))
end else begin
()
end
in (let rec check_function_app = (fun norm tf -> (match ((let _105_586 = (FStar_Absyn_Util.unrefine tf)
in _105_586.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_Tc_Rel.trivial_guard)
end
| (FStar_Util.Inl (t), _52_1636)::_52_1632 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Explicit type applications on a term with unknown type; add an annotation?", t.FStar_Absyn_Syntax.pos))))
end
| (FStar_Util.Inr (e), imp)::tl -> begin
(let _52_1648 = (tc_exp env e)
in (match (_52_1648) with
| (e, c, g_e) -> begin
(let _52_1652 = (tc_args env tl)
in (match (_52_1652) with
| (args, comps, g_rest) -> begin
(let _105_591 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((FStar_Util.Inr (e), imp))::args, (c)::comps, _105_591))
end))
end))
end))
in (let _52_1656 = (tc_args env args)
in (match (_52_1656) with
| (args, comps, g_args) -> begin
(let bs = (let _105_592 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _105_592))
in (let cres = (let _105_593 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _105_593 top.FStar_Absyn_Syntax.pos))
in (let _52_1659 = (let _105_595 = (let _105_594 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, cres) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _105_594))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _105_595))
in (let comp = (let _105_598 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c (None, out))) ((chead)::comps) _105_598))
in (let _105_600 = (FStar_Absyn_Syntax.mk_Exp_app (head, args) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _105_599 = (FStar_Tc_Rel.conj_guard g_head g_args)
in (_105_600, comp, _105_599)))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let vars = (FStar_Tc_Env.binders env)
in (let rec tc_args = (fun _52_1676 bs cres args -> (match (_52_1676) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit))::rest, (_52_1690, None)::_52_1688) -> begin
(let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1696 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _52_1700 = (let _105_636 = (let _105_635 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _105_635))
in (FStar_Tc_Rel.new_tvar _105_636 vars k))
in (match (_52_1700) with
| (targ, u) -> begin
(let _52_1701 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_638 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _105_637 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _105_638 _105_637)))
end else begin
()
end
in (let subst = (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, targ)))::subst
in (let arg = (FStar_Util.Inl (targ), (FStar_Absyn_Syntax.as_implicit true))
in (let _105_647 = (let _105_646 = (let _105_645 = (let _105_644 = (let _105_643 = (FStar_Tc_Util.as_uvar_t u)
in (_105_643, u.FStar_Absyn_Syntax.pos))
in FStar_Util.Inl (_105_644))
in (add_implicit _105_645 g))
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _105_646, fvs))
in (tc_args _105_647 rest cres args)))))
end))))
end
| ((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit))::rest, (_52_1715, None)::_52_1713) -> begin
(let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1721 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (let _52_1725 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_52_1725) with
| (varg, u) -> begin
(let subst = (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, varg)))::subst
in (let arg = (FStar_Util.Inr (varg), (FStar_Absyn_Syntax.as_implicit true))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, (add_implicit (FStar_Util.Inr (u)) g), fvs) rest cres args)))
end))))
end
| ((FStar_Util.Inl (a), aqual)::rest, (FStar_Util.Inl (t), aq)::rest') -> begin
(let _52_1741 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_653 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _105_652 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _105_653 _105_652)))
end else begin
()
end
in (let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _52_1744 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (let _52_1750 = (tc_typ_check (let _52_1746 = env
in {FStar_Tc_Env.solver = _52_1746.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_1746.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_1746.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_1746.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_1746.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_1746.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_1746.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_1746.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_1746.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_1746.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_1746.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_1746.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_1746.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_1746.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_1746.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_1746.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _52_1746.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_1746.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_1746.FStar_Tc_Env.default_effects}) t k)
in (match (_52_1750) with
| (t, g') -> begin
(let f = (let _105_654 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _105_654))
in (let g' = (let _52_1752 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _52_1752.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _52_1752.FStar_Tc_Rel.implicits})
in (let arg = (FStar_Util.Inl (t), aq)
in (let subst = (let _105_655 = (FStar_List.hd bs)
in (maybe_extend_subst subst _105_655 arg))
in (let _105_661 = (let _105_660 = (FStar_Tc_Rel.conj_guard g g')
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _105_660, fvs))
in (tc_args _105_661 rest cres rest'))))))
end)))))
end
| ((FStar_Util.Inr (x), aqual)::rest, (FStar_Util.Inr (e), aq)::rest') -> begin
(let _52_1770 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_663 = (FStar_Absyn_Print.subst_to_string subst)
in (let _105_662 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _105_663 _105_662)))
end else begin
()
end
in (let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _52_1773 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_664 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _105_664))
end else begin
()
end
in (let _52_1775 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (let env = (FStar_Tc_Env.set_expected_typ env targ)
in (let env = (let _52_1778 = env
in {FStar_Tc_Env.solver = _52_1778.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_1778.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_1778.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_1778.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_1778.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_1778.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_1778.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_1778.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_1778.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_1778.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_1778.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_1778.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_1778.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_1778.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_1778.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_1778.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _52_1778.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_1778.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_1778.FStar_Tc_Env.default_effects})
in (let _52_1781 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _105_666 = (FStar_Absyn_Print.exp_to_string e)
in (let _105_665 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _105_666 _105_665)))
end else begin
()
end
in (let _52_1783 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_669 = (FStar_Absyn_Print.tag_of_exp e)
in (let _105_668 = (FStar_Absyn_Print.exp_to_string e)
in (let _105_667 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _105_669 _105_668 _105_667))))
end else begin
()
end
in (let _52_1788 = (tc_exp env e)
in (match (_52_1788) with
| (e, c, g_e) -> begin
(let g = (FStar_Tc_Rel.conj_guard g g_e)
in (let _52_1790 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_671 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _105_670 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _105_671 _105_670)))
end else begin
()
end
in (let arg = (FStar_Util.Inr (e), aq)
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(let subst = (let _105_672 = (FStar_List.hd bs)
in (maybe_extend_subst subst _105_672 arg))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(let subst = (let _105_677 = (FStar_List.hd bs)
in (maybe_extend_subst subst _105_677 arg))
in (let _52_1797 = (((Some (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))), c))::comps, g)
in (match (_52_1797) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _105_682 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _105_682)) then begin
(let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (let arg' = (let _105_683 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _105_683))
in (let binding = FStar_Tc_Env.Binding_var ((newx.FStar_Absyn_Syntax.v, newx.FStar_Absyn_Syntax.sort))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((Some (binding), c))::comps, g, fvs) rest cres rest'))))
end else begin
(let _105_696 = (let _105_695 = (let _105_689 = (let _105_688 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _105_688))
in (_105_689)::arg_rets)
in (let _105_694 = (let _105_692 = (let _105_691 = (FStar_All.pipe_left (fun _105_690 -> Some (_105_690)) (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, targ))))
in (_105_691, c))
in (_105_692)::comps)
in (let _105_693 = (FStar_Util.set_add x fvs)
in (subst, (arg)::outargs, _105_695, _105_694, g, _105_693))))
in (tc_args _105_696 rest cres rest'))
end
end
end)))
end))))))))))
end
| ((FStar_Util.Inr (_52_1804), _52_1807)::_52_1802, (FStar_Util.Inl (_52_1813), _52_1816)::_52_1811) -> begin
(let _105_700 = (let _105_699 = (let _105_698 = (let _105_697 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _105_697))
in ("Expected an expression; got a type", _105_698))
in FStar_Absyn_Syntax.Error (_105_699))
in (Prims.raise _105_700))
end
| ((FStar_Util.Inl (_52_1823), _52_1826)::_52_1821, (FStar_Util.Inr (_52_1832), _52_1835)::_52_1830) -> begin
(let _105_704 = (let _105_703 = (let _105_702 = (let _105_701 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _105_701))
in ("Expected a type; got an expression", _105_702))
in FStar_Absyn_Syntax.Error (_105_703))
in (Prims.raise _105_704))
end
| (_52_1840, []) -> begin
(let _52_1843 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (let _52_1861 = (match (bs) with
| [] -> begin
(let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (let g = (FStar_Tc_Rel.conj_guard g_head g)
in (let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _52_1851 -> (match (_52_1851) with
| (_52_1849, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (let cres = if refine_with_equality then begin
(let _105_706 = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev arg_rets)) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _105_706 cres))
end else begin
(let _52_1853 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_709 = (FStar_Absyn_Print.exp_to_string head)
in (let _105_708 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _105_707 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _105_709 _105_708 _105_707))))
end else begin
()
end
in cres)
end
in (let _105_710 = (FStar_Tc_Util.refresh_comp_label env false cres)
in (_105_710, g))))))
end
| _52_1857 -> begin
(let g = (let _105_711 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _105_711 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _105_717 = (let _105_716 = (let _105_715 = (let _105_714 = (let _105_713 = (let _105_712 = (cres.FStar_Absyn_Syntax.comp ())
in (bs, _105_712))
in (FStar_Absyn_Syntax.mk_Typ_fun _105_713 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _105_714))
in (FStar_Absyn_Syntax.mk_Total _105_715))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _105_716))
in (_105_717, g)))
end)
in (match (_52_1861) with
| (cres, g) -> begin
(let _52_1862 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_718 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _105_718))
end else begin
()
end
in (let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) ((Prims.fst c), out))) cres comps)
in (let comp = (FStar_Tc_Util.bind env None chead (None, comp))
in (let app = (FStar_Absyn_Syntax.mk_Exp_app_flat (head, (FStar_List.rev outargs)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _52_1871 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_52_1871) with
| (comp, g) -> begin
(let _52_1872 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_724 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _105_723 = (let _105_722 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _105_722))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _105_724 _105_723)))
end else begin
()
end
in (app, comp, g))
end))))))
end)))
end
| ([], arg::_52_1876) -> begin
(let rec aux = (fun norm tres -> (let tres = (let _105_729 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _105_729 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(let _52_1888 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_730 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _105_730))
end else begin
()
end
in (let _105_735 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args (subst, outargs, arg_rets, ((None, cres))::comps, g, fvs) bs _105_735 args)))
end
| _52_1891 when (not (norm)) -> begin
(let _105_736 = (whnf env tres)
in (aux true _105_736))
end
| _52_1893 -> begin
(let _105_741 = (let _105_740 = (let _105_739 = (let _105_738 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _105_737 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _105_738 _105_737)))
in (_105_739, (FStar_Absyn_Syntax.argpos arg)))
in FStar_Absyn_Syntax.Error (_105_740))
in (Prims.raise _105_741))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _105_742 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args ([], [], [], [], FStar_Tc_Rel.trivial_guard, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs) bs _105_742 args))))
end
| _52_1895 -> begin
if (not (norm)) then begin
(let _105_743 = (whnf env tf)
in (check_function_app true _105_743))
end else begin
(let _105_746 = (let _105_745 = (let _105_744 = (FStar_Tc_Errors.expected_function_typ env tf)
in (_105_744, head.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_745))
in (Prims.raise _105_746))
end
end))
in (let _105_747 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _105_747)))))
end))
end))
in (let _52_1899 = (aux ())
in (match (_52_1899) with
| (e, c, g) -> begin
(let _52_1900 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _105_748 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _105_748))
end else begin
()
end
in (let c = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (let _52_1907 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_753 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _105_752 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _105_751 = (let _105_750 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _105_750 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _105_753 _105_752 _105_751))))
end else begin
()
end
in (let _52_1912 = (comp_check_expected_typ env0 e c)
in (match (_52_1912) with
| (e, c, g') -> begin
(let _105_754 = (FStar_Tc_Rel.conj_guard g g')
in (e, c, _105_754))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(let _52_1919 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_52_1919) with
| (env1, topt) -> begin
(let env1 = (instantiate_both env1)
in (let _52_1924 = (tc_exp env1 e1)
in (match (_52_1924) with
| (e1, c1, g1) -> begin
(let _52_1931 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _105_755 = (FStar_Tc_Env.set_expected_typ env res_t)
in (_105_755, res_t)))
end)
in (match (_52_1931) with
| (env_branches, res_t) -> begin
(let guard_x = (let _105_757 = (FStar_All.pipe_left (fun _105_756 -> Some (_105_756)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _105_757))
in (let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (let _52_1948 = (let _52_1945 = (FStar_List.fold_right (fun _52_1939 _52_1942 -> (match ((_52_1939, _52_1942)) with
| ((_52_1935, f, c, g), (caccum, gaccum)) -> begin
(let _105_760 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _105_760))
end)) t_eqns ([], FStar_Tc_Rel.trivial_guard))
in (match (_52_1945) with
| (cases, g) -> begin
(let _105_761 = (FStar_Tc_Util.bind_cases env res_t cases)
in (_105_761, g))
end))
in (match (_52_1948) with
| (c_branches, g_branches) -> begin
(let _52_1949 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_765 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _105_764 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _105_763 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _105_762 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _105_765 _105_764 _105_763 _105_762)))))
end else begin
()
end
in (let cres = (let _105_768 = (let _105_767 = (FStar_All.pipe_left (fun _105_766 -> Some (_105_766)) (FStar_Tc_Env.Binding_var ((guard_x, c1.FStar_Absyn_Syntax.res_typ))))
in (_105_767, c_branches))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _105_768))
in (let e = (let _105_775 = (w cres)
in (let _105_774 = (let _105_773 = (let _105_772 = (FStar_List.map (fun _52_1959 -> (match (_52_1959) with
| (f, _52_1954, _52_1956, _52_1958) -> begin
f
end)) t_eqns)
in (e1, _105_772))
in (FStar_Absyn_Syntax.mk_Exp_match _105_773))
in (FStar_All.pipe_left _105_775 _105_774)))
in (let _105_777 = (FStar_Absyn_Syntax.mk_Exp_ascribed (e, cres.FStar_Absyn_Syntax.res_typ, Some (cres.FStar_Absyn_Syntax.eff_name)) None e.FStar_Absyn_Syntax.pos)
in (let _105_776 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in (_105_777, cres, _105_776))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _52_1964; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let env = (instantiate_both env)
in (let env0 = env
in (let topt = (FStar_Tc_Env.expected_typ env)
in (let top_level = (match (x) with
| FStar_Util.Inr (_52_1977) -> begin
true
end
| _52_1980 -> begin
false
end)
in (let _52_1985 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_52_1985) with
| (env1, _52_1984) -> begin
(let _52_1998 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(FStar_Tc_Rel.trivial_guard, env1)
end
| _52_1988 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _105_778 = (FStar_Tc_Env.set_expected_typ env1 t)
in (FStar_Tc_Rel.trivial_guard, _105_778))
end else begin
(let _52_1991 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_52_1991) with
| (t, f) -> begin
(let _52_1992 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _105_780 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _105_779 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _105_780 _105_779)))
end else begin
()
end
in (let t = (norm_t env1 t)
in (let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in (f, env1))))
end))
end
end)
in (match (_52_1998) with
| (f, env1) -> begin
(let _52_2004 = (tc_exp (let _52_1999 = env1
in {FStar_Tc_Env.solver = _52_1999.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_1999.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_1999.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_1999.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_1999.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_1999.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_1999.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_1999.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_1999.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_1999.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_1999.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_1999.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_1999.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_1999.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _52_1999.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_1999.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_1999.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_1999.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_1999.FStar_Tc_Env.default_effects}) e1)
in (match (_52_2004) with
| (e1, c1, g1) -> begin
(let _52_2008 = (let _105_784 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _52_2005 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _105_784 e1 c1 f))
in (match (_52_2008) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_52_2010) -> begin
(let _52_2021 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(let _52_2014 = (let _105_785 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _105_785 c1))
in (match (_52_2014) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(let _52_2015 = if (FStar_ST.read FStar_Options.warn_top_level_effects) then begin
(let _105_786 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _105_786 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _105_787 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e2, FStar_Absyn_Syntax.Masked_effect))))
in (_105_787, c1)))
end
end))
end else begin
(let _52_2017 = (let _105_788 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.discharge_guard env _105_788))
in (let _105_789 = (c1.FStar_Absyn_Syntax.comp ())
in (e2, _105_789)))
end
in (match (_52_2021) with
| (e2, c1) -> begin
(let _52_2026 = if env.FStar_Tc_Env.generalize then begin
(let _105_790 = (FStar_Tc_Util.generalize false env1 (((x, e1, c1))::[]))
in (FStar_All.pipe_left FStar_List.hd _105_790))
end else begin
(x, e1, c1)
end
in (match (_52_2026) with
| (_52_2023, e1, c1) -> begin
(let cres = (let _105_791 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _105_791))
in (let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _105_792 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _105_792 (None, cres)))
end
in (let _52_2029 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _105_796 = (let _105_795 = (w cres)
in (FStar_All.pipe_left _105_795 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, (FStar_Absyn_Util.comp_effect_name c1), (FStar_Absyn_Util.comp_result c1), e1)))::[]), e2))))
in (_105_796, cres, FStar_Tc_Rel.trivial_guard)))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (let _52_2037 = (let _105_797 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _105_797 e2))
in (match (_52_2037) with
| (e2, c2, g2) -> begin
(let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 (Some (b), c2))
in (let e = (let _105_800 = (w cres)
in (FStar_All.pipe_left _105_800 (FStar_Absyn_Syntax.mk_Exp_let ((false, ((FStar_Absyn_Syntax.mk_lb (x, c1.FStar_Absyn_Syntax.eff_name, c1.FStar_Absyn_Syntax.res_typ, e1)))::[]), e2))))
in (let g2 = (let _105_806 = (let _105_805 = (let _105_804 = (let _105_803 = (let _105_802 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _105_802 e1))
in (FStar_All.pipe_left (fun _105_801 -> FStar_Tc_Rel.NonTrivial (_105_801)) _105_803))
in (FStar_Tc_Rel.guard_of_guard_formula _105_804))
in (FStar_Tc_Rel.imp_guard _105_805 g2))
in (FStar_All.pipe_left (FStar_Tc_Rel.close_guard (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ)))::[])) _105_806))
in (let guard = (let _105_807 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _105_807))
in (match (topt) with
| None -> begin
(let tres = cres.FStar_Absyn_Syntax.res_typ
in (let fvs = (FStar_Absyn_Util.freevars_typ tres)
in if (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs) then begin
(let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _52_2046 = (let _105_808 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _105_808))
in (e, cres, guard)))
end else begin
(e, cres, guard)
end))
end
| _52_2049 -> begin
(e, cres, guard)
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _52_2052), _52_2055) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(let env = (instantiate_both env)
in (let _52_2067 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_52_2067) with
| (env0, topt) -> begin
(let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _52_9 -> (match (_52_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_52_2076); FStar_Absyn_Syntax.lbtyp = _52_2074; FStar_Absyn_Syntax.lbeff = _52_2072; FStar_Absyn_Syntax.lbdef = _52_2070} -> begin
true
end
| _52_2080 -> begin
false
end))))
in (let _52_2107 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _52_2084 _52_2090 -> (match ((_52_2084, _52_2090)) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _52_2087; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _52_2095 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_52_2095) with
| (_52_2092, t, check_t) -> begin
(let e = (FStar_Absyn_Util.unascribe e)
in (let t = if (not (check_t)) then begin
t
end else begin
if ((not (is_inner_let)) && (not (env.FStar_Tc_Env.generalize))) then begin
(let _52_2097 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _105_812 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Type %s is marked as no-generalize\n" _105_812))
end else begin
()
end
in t)
end else begin
(let _105_813 = (tc_typ_check_trivial (let _52_2099 = env0
in {FStar_Tc_Env.solver = _52_2099.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_2099.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_2099.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_2099.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_2099.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_2099.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_2099.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_2099.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_2099.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_2099.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_2099.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_2099.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_2099.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_2099.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_2099.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _52_2099.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_2099.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_2099.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_2099.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _105_813 (norm_t env)))
end
end
in (let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(let _52_2102 = env
in {FStar_Tc_Env.solver = _52_2102.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_2102.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_2102.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_2102.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_2102.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_2102.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_2102.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_2102.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_2102.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_2102.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_2102.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_2102.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_2102.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = ((x, t))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_2102.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_2102.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_2102.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_2102.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_2102.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_2102.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((x, t, e))::xts, env))))
end))
end)) ([], env)))
in (match (_52_2107) with
| (lbs, env') -> begin
(let _52_2122 = (let _105_819 = (let _105_818 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _105_818 (FStar_List.map (fun _52_2111 -> (match (_52_2111) with
| (x, t, e) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (let _52_2113 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_817 = (FStar_Absyn_Print.lbname_to_string x)
in (let _105_816 = (FStar_Absyn_Print.exp_to_string e)
in (let _105_815 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _105_817 _105_816 _105_815))))
end else begin
()
end
in (let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (let _52_2119 = (tc_total_exp env' e)
in (match (_52_2119) with
| (e, t, g) -> begin
((x, t, e), g)
end)))))
end)))))
in (FStar_All.pipe_right _105_819 FStar_List.unzip))
in (match (_52_2122) with
| (lbs, gs) -> begin
(let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (let _52_2141 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _105_821 = (FStar_List.map (fun _52_2127 -> (match (_52_2127) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, t, e))
end)) lbs)
in (_105_821, g_lbs))
end else begin
(let _52_2128 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let ecs = (let _105_824 = (FStar_All.pipe_right lbs (FStar_List.map (fun _52_2133 -> (match (_52_2133) with
| (x, t, e) -> begin
(let _105_823 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb (x, t, e)))
in (x, e, _105_823))
end))))
in (FStar_Tc_Util.generalize true env _105_824))
in (let _105_826 = (FStar_List.map (fun _52_2138 -> (match (_52_2138) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb (x, FStar_Absyn_Const.effect_Tot_lid, (FStar_Absyn_Util.comp_result c), e))
end)) ecs)
in (_105_826, FStar_Tc_Rel.trivial_guard))))
end
in (match (_52_2141) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(let cres = (let _105_827 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _105_827))
in (let _52_2143 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (let _52_2145 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _105_831 = (let _105_830 = (w cres)
in (FStar_All.pipe_left _105_830 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (_105_831, cres, FStar_Tc_Rel.trivial_guard)))))
end else begin
(let _52_2161 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _52_2149 _52_2156 -> (match ((_52_2149, _52_2156)) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _52_2153; FStar_Absyn_Syntax.lbdef = _52_2151}) -> begin
(let b = (binding_of_lb x t)
in (let env = (FStar_Tc_Env.push_local_binding env b)
in ((b)::bindings, env)))
end)) ([], env)))
in (match (_52_2161) with
| (bindings, env) -> begin
(let _52_2165 = (tc_exp env e1)
in (match (_52_2165) with
| (e1, cres, g1) -> begin
(let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (let cres = (let _52_2169 = cres
in {FStar_Absyn_Syntax.eff_name = _52_2169.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _52_2169.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _52_2169.FStar_Absyn_Syntax.comp})
in (let e = (let _105_836 = (w cres)
in (FStar_All.pipe_left _105_836 (FStar_Absyn_Syntax.mk_Exp_let ((true, lbs), e1))))
in (match (topt) with
| Some (_52_2174) -> begin
(e, cres, guard)
end
| None -> begin
(let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _52_10 -> (match (_52_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_52_2186); FStar_Absyn_Syntax.lbtyp = _52_2184; FStar_Absyn_Syntax.lbeff = _52_2182; FStar_Absyn_Syntax.lbdef = _52_2180} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _52_2194; FStar_Absyn_Syntax.lbeff = _52_2192; FStar_Absyn_Syntax.lbdef = _52_2190} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _52_2203; FStar_Absyn_Syntax.lbeff = _52_2201; FStar_Absyn_Syntax.lbdef = _52_2199}) -> begin
(let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (let _52_2209 = (let _105_838 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _105_838))
in (e, cres, guard)))
end
| _52_2212 -> begin
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
and tc_eqn = (fun scrutinee_x pat_t env _52_2219 -> (match (_52_2219) with
| (pattern, when_clause, branch) -> begin
(let tc_pat = (fun allow_implicits pat_t p0 -> (let _52_2227 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_52_2227) with
| (bindings, exps, p) -> begin
(let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (let _52_2236 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _52_11 -> (match (_52_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _105_851 = (FStar_Absyn_Print.strBvd x)
in (let _105_850 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _105_851 _105_850)))
end
| _52_2235 -> begin
()
end))))
end else begin
()
end
in (let _52_2241 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_52_2241) with
| (env1, _52_2240) -> begin
(let env1 = (let _52_2242 = env1
in {FStar_Tc_Env.solver = _52_2242.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_2242.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_2242.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_2242.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_2242.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_2242.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_2242.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_2242.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _52_2242.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_2242.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_2242.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_2242.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_2242.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_2242.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_2242.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_2242.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_2242.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_2242.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_2242.FStar_Tc_Env.default_effects})
in (let expected_pat_t = (FStar_Tc_Rel.unrefine env pat_t)
in (let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (let _52_2247 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_854 = (FStar_Absyn_Print.exp_to_string e)
in (let _105_853 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _105_854 _105_853)))
end else begin
()
end
in (let _52_2252 = (tc_exp env1 e)
in (match (_52_2252) with
| (e, lc, g) -> begin
(let _52_2253 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_856 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _105_855 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _105_856 _105_855)))
end else begin
()
end
in (let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (let g = (FStar_Tc_Rel.conj_guard g g')
in (let _52_2257 = (let _105_857 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _105_857))
in (let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (let _52_2260 = if (let _105_860 = (let _105_859 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _105_858 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _105_859 _105_858)))
in (FStar_All.pipe_left Prims.op_Negation _105_860)) then begin
(let _105_865 = (let _105_864 = (let _105_863 = (let _105_862 = (FStar_Absyn_Print.exp_to_string e')
in (let _105_861 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _105_862 _105_861)))
in (_105_863, p.FStar_Absyn_Syntax.p))
in FStar_Absyn_Syntax.Error (_105_864))
in (Prims.raise _105_865))
end else begin
()
end
in (let _52_2262 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_866 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _105_866))
end else begin
()
end
in e)))))))
end))))))
in (let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (let _52_2273 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _52_12 -> (match (_52_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _105_869 = (FStar_Absyn_Print.strBvd x)
in (let _105_868 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _105_869 _105_868)))
end
| _52_2272 -> begin
()
end))))
end else begin
()
end
in (p, bindings, pat_env, exps, FStar_Tc_Rel.trivial_guard))))))
end))))
end)))
in (let _52_2280 = (tc_pat true pat_t pattern)
in (match (_52_2280) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(let _52_2290 = (match (when_clause) with
| None -> begin
(None, FStar_Tc_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("When clauses are not yet supported in --verify mode; they soon will be", e.FStar_Absyn_Syntax.pos))))
end else begin
(let _52_2287 = (let _105_870 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _105_870 e))
in (match (_52_2287) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_52_2290) with
| (when_clause, g_when) -> begin
(let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _105_872 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _105_871 -> Some (_105_871)) _105_872))
end)
in (let _52_2298 = (tc_exp pat_env branch)
in (match (_52_2298) with
| (branch, c, g_branch) -> begin
(let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (let _52_2303 = (let _105_873 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((scrutinee_x, pat_t))))
in (FStar_All.pipe_right _105_873 FStar_Tc_Env.clear_expected_typ))
in (match (_52_2303) with
| (scrutinee_env, _52_2302) -> begin
(let c = (let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _52_2317 -> begin
(let clause = (let _105_877 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _105_876 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _105_877 _105_876 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _105_879 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _105_878 -> Some (_105_878)) _105_879))
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
(let _105_882 = (let _105_881 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _105_880 -> FStar_Tc_Rel.NonTrivial (_105_880)) _105_881))
in (FStar_Tc_Util.weaken_precondition env c _105_882))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (let discriminate = (fun scrutinee f -> (let disc = (let _105_888 = (let _105_887 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _105_887))
in (FStar_All.pipe_left _105_888 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (let disc = (let _105_891 = (let _105_890 = (let _105_889 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_105_889)::[])
in (disc, _105_890))
in (FStar_Absyn_Syntax.mk_Exp_app _105_891 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (let rec mk_guard = (fun scrutinee pat_exp -> (let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_52_2375) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (FStar_Absyn_Util.teq, ((FStar_Absyn_Syntax.varg scrutinee))::((FStar_Absyn_Syntax.varg pat_exp))::[]) None scrutinee.FStar_Absyn_Syntax.pos)
end
| FStar_Absyn_Syntax.Exp_fvar (f, _52_2379) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _52_2392); FStar_Absyn_Syntax.tk = _52_2389; FStar_Absyn_Syntax.pos = _52_2387; FStar_Absyn_Syntax.fvs = _52_2385; FStar_Absyn_Syntax.uvs = _52_2383}, args) -> begin
(let head = (discriminate scrutinee f)
in (let sub_term_guards = (let _105_901 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_52_2403) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in (let sub_term = (let _105_899 = (let _105_898 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (_105_898, ((FStar_Absyn_Syntax.varg scrutinee))::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _105_899 None f.FStar_Absyn_Syntax.p))
in (let _105_900 = (mk_guard sub_term ei)
in (_105_900)::[])))
end))))
in (FStar_All.pipe_right _105_901 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _52_2411 -> begin
(let _105_904 = (let _105_903 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _105_902 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _105_903 _105_902)))
in (FStar_All.failwith _105_904))
end)))
in (let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(let t = (mk_guard s pat)
in (let _52_2420 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_52_2420) with
| (t, _52_2419) -> begin
t
end)))
end)
in (let path_guard = (let _105_913 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _105_912 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _105_912)))))
in (FStar_All.pipe_right _105_913 FStar_Absyn_Util.mk_disj_l))
in (let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (let guard = (let _105_914 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _105_914))
in (let _52_2428 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _105_915 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _105_915))
end else begin
()
end
in (let _105_917 = (let _105_916 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _105_916))
in ((pattern, when_clause, branch), path_guard, c, _105_917))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial = (fun env k -> (let _52_2434 = (tc_kind env k)
in (match (_52_2434) with
| (k, g) -> begin
(let _52_2435 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial = (fun env t -> (let _52_2442 = (tc_typ env t)
in (match (_52_2442) with
| (t, k, g) -> begin
(let _52_2443 = (FStar_Tc_Util.discharge_guard env g)
in (t, k))
end)))
and tc_typ_check_trivial = (fun env t k -> (let _52_2450 = (tc_typ_check env t k)
in (match (_52_2450) with
| (t, f) -> begin
(let _52_2451 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp = (fun env e -> (let _52_2458 = (tc_exp env e)
in (match (_52_2458) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (let c = (let _105_927 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _105_927 (norm_c env)))
in (match ((let _105_929 = (let _105_928 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _105_928))
in (FStar_Tc_Rel.sub_comp env c _105_929))) with
| Some (g') -> begin
(let _105_930 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _105_930))
end
| _52_2464 -> begin
(let _105_933 = (let _105_932 = (let _105_931 = (FStar_Tc_Errors.expected_pure_expression e c)
in (_105_931, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_932))
in (Prims.raise _105_933))
end)))
end
end)))
and tc_ghost_exp = (fun env e -> (let _52_2470 = (tc_exp env e)
in (match (_52_2470) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
(e, c.FStar_Absyn_Syntax.res_typ, g)
end else begin
(let c = (let _105_936 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _105_936 (norm_c env)))
in (let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (let _52_2474 = env
in {FStar_Tc_Env.solver = _52_2474.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_2474.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_2474.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_2474.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_2474.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_2474.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_2474.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_2474.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_2474.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_2474.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_2474.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_2474.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_2474.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_2474.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_2474.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_2474.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _52_2474.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_2474.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_2474.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _105_937 = (FStar_Tc_Rel.conj_guard g g')
in (e, (FStar_Absyn_Util.comp_result c), _105_937))
end
| _52_2479 -> begin
(let _105_940 = (let _105_939 = (let _105_938 = (FStar_Tc_Errors.expected_ghost_expression e c)
in (_105_938, e.FStar_Absyn_Syntax.pos))
in FStar_Absyn_Syntax.Error (_105_939))
in (Prims.raise _105_940))
end))))
end
end)))

let tc_tparams = (fun env tps -> (let _52_2485 = (tc_binders env tps)
in (match (_52_2485) with
| (tps, env, g) -> begin
(let _52_2486 = (FStar_Tc_Util.force_trivial env g)
in (tps, env))
end)))

let a_kwp_a = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _52_2505)::(FStar_Util.Inl (wp), _52_2500)::(FStar_Util.Inl (_52_2492), _52_2495)::[], _52_2509) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _52_2513 -> begin
(let _105_953 = (let _105_952 = (let _105_951 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in (_105_951, (FStar_Ident.range_of_lid m)))
in FStar_Absyn_Syntax.Error (_105_952))
in (Prims.raise _105_953))
end))

let rec tc_eff_decl = (fun env m -> (let _52_2519 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_52_2519) with
| (binders, env, g) -> begin
(let _52_2520 = (FStar_Tc_Util.discharge_guard env g)
in (let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (let _52_2525 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_52_2525) with
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
in (let _105_975 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _105_975 (norm_t env))))
in (let bind_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder a_kwp_b))::((FStar_Absyn_Syntax.null_t_binder a_kwlp_b))::[], kwp_b)))
in (let _105_977 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _105_977 (norm_t env))))
in (let bind_wlp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder a_kwlp_b))::[], kwlp_b)))
in (let _105_979 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _105_979 (norm_t env))))
in (let if_then_else = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _105_981 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _105_981 (norm_t env))))
in (let ite_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _105_983 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _105_983 (norm_t env))))
in (let ite_wlp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwlp_a))::[], kwlp_a)))
in (let _105_985 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _105_985 (norm_t env))))
in (let wp_binop = (let expected_k = (let _105_993 = (let _105_992 = (let _105_991 = (let _105_990 = (let _105_989 = (let _105_988 = (let _105_987 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _105_987))
in (_105_988)::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[])
in ((FStar_Absyn_Syntax.null_t_binder kwp_a))::_105_989)
in ((FStar_Absyn_Syntax.t_binder a))::_105_990)
in (_105_991, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _105_992))
in (FStar_All.pipe_left w _105_993))
in (let _105_994 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _105_994 (norm_t env))))
in (let wp_as_type = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], FStar_Absyn_Syntax.ktype)))
in (let _105_996 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _105_996 (norm_t env))))
in (let close_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder b))::((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder a_kwp_b))::[], kwp_b)))
in (let _105_998 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _105_998 (norm_t env))))
in (let close_wp_t = (let expected_k = (let _105_1006 = (let _105_1005 = (let _105_1004 = (let _105_1003 = (let _105_1002 = (let _105_1001 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype))::[], kwp_a)))
in (FStar_Absyn_Syntax.null_t_binder _105_1001))
in (_105_1002)::[])
in ((FStar_Absyn_Syntax.t_binder a))::_105_1003)
in (_105_1004, kwp_a))
in (FStar_Absyn_Syntax.mk_Kind_arrow _105_1005))
in (FStar_All.pipe_left w _105_1006))
in (let _105_1007 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _105_1007 (norm_t env))))
in (let _52_2559 = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], kwp_a)))
in (let _105_1012 = (let _105_1009 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _105_1009 (norm_t env)))
in (let _105_1011 = (let _105_1010 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _105_1010 (norm_t env)))
in (_105_1012, _105_1011))))
in (match (_52_2559) with
| (assert_p, assume_p) -> begin
(let null_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::[], kwp_a)))
in (let _105_1014 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _105_1014 (norm_t env))))
in (let trivial_wp = (let expected_k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a))::[], FStar_Absyn_Syntax.ktype)))
in (let _105_1016 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _105_1016 (norm_t env))))
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
(let _52_2578 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _52_2580 = (let _105_1020 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _105_1020 Prims.ignore))
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
(let _52_2595 = (let _105_1021 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _105_1021))
in (match (_52_2595) with
| (a, kwp_a_src) -> begin
(let _52_2598 = (let _105_1022 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _105_1022))
in (match (_52_2598) with
| (b, kwp_b_tgt) -> begin
(let kwp_a_tgt = (let _105_1026 = (let _105_1025 = (let _105_1024 = (let _105_1023 = (FStar_Absyn_Util.btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _105_1023))
in FStar_Util.Inl (_105_1024))
in (_105_1025)::[])
in (FStar_Absyn_Util.subst_kind _105_1026 kwp_b_tgt))
in (let expected_k = (FStar_All.pipe_right r (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.t_binder a))::((FStar_Absyn_Syntax.null_t_binder kwp_a_src))::[], kwp_a_tgt)))
in (let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (let sub = (let _52_2602 = sub
in {FStar_Absyn_Syntax.source = _52_2602.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _52_2602.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (let se = FStar_Absyn_Syntax.Sig_sub_effect ((sub, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _52_2619 = (tc_tparams env tps)
in (match (_52_2619) with
| (tps, env) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _52_2622 -> begin
(tc_kind_trivial env k)
end)
in (let _52_2624 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _105_1029 = (FStar_Absyn_Print.sli lid)
in (let _105_1028 = (let _105_1027 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _105_1027))
in (FStar_Util.print2 "Checked %s at kind %s\n" _105_1029 _105_1028)))
end else begin
()
end
in (let k = (norm_k env k)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _mutuals, _data, tags, r))
in (let _52_2642 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_52_2637); FStar_Absyn_Syntax.tk = _52_2635; FStar_Absyn_Syntax.pos = _52_2633; FStar_Absyn_Syntax.fvs = _52_2631; FStar_Absyn_Syntax.uvs = _52_2629} -> begin
(let _105_1030 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _105_1030))
end
| _52_2641 -> begin
()
end)
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env)))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(let env0 = env
in (let env = (FStar_Tc_Env.set_range env r)
in (let _52_2655 = (tc_tparams env tps)
in (match (_52_2655) with
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
in (let _52_2670 = (tc_tparams env tps)
in (match (_52_2670) with
| (tps, env) -> begin
(let _52_2673 = (tc_comp env c)
in (match (_52_2673) with
| (c, g) -> begin
(let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _52_13 -> (match (_52_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _105_1033 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _105_1032 -> Some (_105_1032)))
in FStar_Absyn_Syntax.DefaultEffect (_105_1033)))
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
in (let _52_2693 = (tc_tparams env tps)
in (match (_52_2693) with
| (tps, env') -> begin
(let _52_2699 = (let _105_1037 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _105_1037 (fun _52_2696 -> (match (_52_2696) with
| (t, k) -> begin
(let _105_1036 = (norm_t env' t)
in (let _105_1035 = (norm_k env' k)
in (_105_1036, _105_1035)))
end))))
in (match (_52_2699) with
| (t, k1) -> begin
(let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _52_2702 -> begin
(let k2 = (let _105_1038 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _105_1038 (norm_k env)))
in (let _52_2704 = (let _105_1039 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _105_1039))
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
in (let _52_2724 = (tc_binders env tps)
in (match (_52_2724) with
| (tps, env, g) -> begin
(let tycon = (tname, tps, k)
in (let _52_2726 = (FStar_Tc_Util.discharge_guard env g)
in (let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (let t = (norm_t env t)
in (let _52_2738 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(formals, (FStar_Absyn_Util.comp_result cod))
end
| _52_2735 -> begin
([], t)
end)
in (match (_52_2738) with
| (formals, result_t) -> begin
(let cardinality_and_positivity_check = (fun formal -> (let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _52_2746 -> (match (_52_2746) with
| (a, _52_2745) -> begin
(match (a) with
| FStar_Util.Inl (_52_2748) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _105_1047 = (FStar_Absyn_Util.compress_typ t)
in _105_1047.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _105_1051 = (let _105_1050 = (let _105_1049 = (let _105_1048 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _105_1048 tname))
in (_105_1049, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_105_1050))
in (Prims.raise _105_1051))
end)
end
| _52_2761 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(let _52_2764 = if (FStar_Options.warn_cardinality ()) then begin
(let _105_1052 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _105_1052))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _105_1055 = (let _105_1054 = (let _105_1053 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (_105_1053, r))
in FStar_Absyn_Syntax.Error (_105_1054))
in (Prims.raise _105_1055))
end else begin
()
end
end
in (let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_52_2768) -> begin
(let _52_2773 = (FStar_Absyn_Util.kind_formals k)
in (match (_52_2773) with
| (formals, _52_2772) -> begin
(check_positivity formals)
end))
end
| _52_2775 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(let _52_2782 = (let _105_1056 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _105_1056 FStar_Util.must))
in (match (_52_2782) with
| (formals, _52_2781) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (let _52_2783 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (let _52_2837 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _105_1060 = (let _105_1059 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _105_1059 Prims.fst))
in (FStar_List.forall2 (fun _52_2790 _52_2794 -> (match ((_52_2790, _52_2794)) with
| ((a, _52_2789), (b, _52_2793)) -> begin
(match ((a, b)) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _52_2802; FStar_Absyn_Syntax.pos = _52_2800; FStar_Absyn_Syntax.fvs = _52_2798; FStar_Absyn_Syntax.uvs = _52_2796}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _52_2817; FStar_Absyn_Syntax.pos = _52_2815; FStar_Absyn_Syntax.fvs = _52_2813; FStar_Absyn_Syntax.uvs = _52_2811}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _52_2826 -> begin
false
end)
end)) _105_1060 tps))))) then begin
(let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _52_2829 -> begin
(let _52_2833 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_52_2833) with
| (_52_2831, expected_args) -> begin
(let _105_1061 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _105_1061 expected_args))
end))
end)
in (let _105_1065 = (let _105_1064 = (let _105_1063 = (let _105_1062 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _105_1062 result_t expected_t))
in (_105_1063, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_105_1064))
in (Prims.raise _105_1065)))
end else begin
()
end
end
| _52_2836 -> begin
(let _105_1070 = (let _105_1069 = (let _105_1068 = (let _105_1067 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _105_1066 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _105_1067 result_t _105_1066)))
in (_105_1068, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_105_1069))
in (Prims.raise _105_1070))
end)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((lid, t, tycon, quals, mutuals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _52_2841 = if (log env) then begin
(let _105_1072 = (let _105_1071 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _105_1071))
in (FStar_All.pipe_left FStar_Util.print_string _105_1072))
end else begin
()
end
in (se, env)))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let t = (let _105_1073 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _105_1073 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (let _52_2851 = (FStar_Tc_Util.check_uvars r t)
in (let se = FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (let _52_2855 = if (log env) then begin
(let _105_1075 = (let _105_1074 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _105_1074))
in (FStar_All.pipe_left FStar_Util.print_string _105_1075))
end else begin
()
end
in (se, env)))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let phi = (let _105_1076 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _105_1076 (norm_t env)))
in (let _52_2865 = (FStar_Tc_Util.check_uvars r phi)
in (let se = FStar_Absyn_Syntax.Sig_assume ((lid, phi, quals, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _52_2918 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _52_2878 lb -> (match (_52_2878) with
| (gen, lbs) -> begin
(let _52_2915 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_52_2887); FStar_Absyn_Syntax.lbtyp = _52_2885; FStar_Absyn_Syntax.lbeff = _52_2883; FStar_Absyn_Syntax.lbdef = _52_2881} -> begin
(FStar_All.failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _52_2892; FStar_Absyn_Syntax.lbdef = e} -> begin
(let _52_2912 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
(gen, lb)
end
| Some (t', _52_2900) -> begin
(let _52_2903 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _105_1079 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _105_1079 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(false, (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e)))
end
| _52_2907 -> begin
(let _52_2908 = if (not (deserialized)) then begin
(let _105_1081 = (let _105_1080 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _105_1080))
in (FStar_All.pipe_left FStar_Util.print_string _105_1081))
end else begin
()
end
in (false, (FStar_Absyn_Syntax.mk_lb (FStar_Util.Inr (l), FStar_Absyn_Const.effect_ALL_lid, t', e))))
end))
end)
in (match (_52_2912) with
| (gen, lb) -> begin
(gen, lb)
end))
end)
in (match (_52_2915) with
| (gen, lb) -> begin
(gen, (lb)::lbs)
end))
end)) (true, [])))
in (match (_52_2918) with
| (generalize, lbs') -> begin
(let lbs' = (FStar_List.rev lbs')
in (let e = (let _105_1086 = (let _105_1085 = (let _105_1084 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _105_1084 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((Prims.fst lbs), lbs'), _105_1085))
in (FStar_Absyn_Syntax.mk_Exp_let _105_1086 None r))
in (let _52_2953 = (match ((tc_exp (let _52_2921 = env
in {FStar_Tc_Env.solver = _52_2921.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_2921.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_2921.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_2921.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_2921.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_2921.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_2921.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_2921.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_2921.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_2921.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_2921.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_2921.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _52_2921.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_2921.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_2921.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_2921.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _52_2921.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _52_2921.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _52_2921.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _52_2930; FStar_Absyn_Syntax.pos = _52_2928; FStar_Absyn_Syntax.fvs = _52_2926; FStar_Absyn_Syntax.uvs = _52_2924}, _52_2937, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_52_2941, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _52_2947 -> begin
quals
end)
in (FStar_Absyn_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _52_2950 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_52_2953) with
| (se, lbs) -> begin
(let _52_2959 = if (log env) then begin
(let _105_1092 = (let _105_1091 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let should_log = (match ((let _105_1088 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _105_1088))) with
| None -> begin
true
end
| _52_2957 -> begin
false
end)
in if should_log then begin
(let _105_1090 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _105_1089 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _105_1090 _105_1089)))
end else begin
""
end))))
in (FStar_All.pipe_right _105_1091 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _105_1092))
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
in (let _52_2971 = (tc_exp env e)
in (match (_52_2971) with
| (e, c, g1) -> begin
(let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (let _52_2977 = (let _105_1096 = (let _105_1093 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_105_1093))
in (let _105_1095 = (let _105_1094 = (c.FStar_Absyn_Syntax.comp ())
in (e, _105_1094))
in (check_expected_effect env _105_1096 _105_1095)))
in (match (_52_2977) with
| (e, _52_2975, g) -> begin
(let _52_2978 = (let _105_1097 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _105_1097))
in (let se = FStar_Absyn_Syntax.Sig_main ((e, r))
in (let env = (FStar_Tc_Env.push_sigelt env se)
in (se, env))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(let env = (FStar_Tc_Env.set_range env r)
in (let _52_2997 = (FStar_All.pipe_right ses (FStar_List.partition (fun _52_14 -> (match (_52_14) with
| FStar_Absyn_Syntax.Sig_tycon (_52_2991) -> begin
true
end
| _52_2994 -> begin
false
end))))
in (match (_52_2997) with
| (tycons, rest) -> begin
(let _52_3006 = (FStar_All.pipe_right rest (FStar_List.partition (fun _52_15 -> (match (_52_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_52_3000) -> begin
true
end
| _52_3003 -> begin
false
end))))
in (match (_52_3006) with
| (abbrevs, rest) -> begin
(let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _52_16 -> (match (_52_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _105_1101 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _105_1101 Prims.fst))
end
| _52_3018 -> begin
k
end)
in (FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, [], [], [], r)), t))
end
| _52_3021 -> begin
(FStar_All.failwith "impossible")
end))))
in (let _52_3025 = (FStar_List.split recs)
in (match (_52_3025) with
| (recs, abbrev_defs) -> begin
(let msg = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _105_1102 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _105_1102))
end else begin
""
end
in (let _52_3027 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (let _52_3034 = (tc_decls false env tycons deserialized)
in (match (_52_3034) with
| (tycons, _52_3031, _52_3033) -> begin
(let _52_3040 = (tc_decls false env recs deserialized)
in (match (_52_3040) with
| (recs, _52_3037, _52_3039) -> begin
(let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle (((FStar_List.append tycons recs), quals, lids, r))))
in (let _52_3047 = (tc_decls false env1 rest deserialized)
in (match (_52_3047) with
| (rest, _52_3044, _52_3046) -> begin
(let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(let tt = (let _105_1105 = (FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _105_1105))
in (let _52_3063 = (tc_typ_trivial env1 tt)
in (match (_52_3063) with
| (tt, _52_3062) -> begin
(let _52_3072 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(bs, t)
end
| _52_3069 -> begin
([], tt)
end)
in (match (_52_3072) with
| (tps, t) -> begin
(let _105_1107 = (let _105_1106 = (FStar_Absyn_Util.compress_kind k)
in (lid, tps, _105_1106, t, [], r))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_105_1107))
end))
end)))
end
| _52_3074 -> begin
(let _105_1109 = (let _105_1108 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _105_1108))
in (FStar_All.failwith _105_1109))
end)) recs abbrev_defs)
in (let _52_3076 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
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
in (let _52_3092 = (let _105_1120 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _105_1120))
in res))))))
in (let _52_3110 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _52_3097 se -> (match (_52_3097) with
| (ses, all_non_private, env) -> begin
(let _52_3099 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _105_1124 = (let _105_1123 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _105_1123))
in (FStar_Util.print_string _105_1124))
end else begin
()
end
in (let _52_3103 = if (FStar_ST.read FStar_Options.timing) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_52_3103) with
| (se, env) -> begin
(let _52_3104 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in (let non_private_decls = if for_export then begin
(non_private env se)
end else begin
[]
end
in ((se)::ses, (non_private_decls)::all_non_private, env)))
end)))
end)) ([], [], env)))
in (match (_52_3110) with
| (ses, all_non_private, env) -> begin
(let _105_1125 = (FStar_All.pipe_right (FStar_List.rev all_non_private) FStar_List.flatten)
in ((FStar_List.rev ses), _105_1125, env))
end))))
and non_private = (fun env se -> (let is_private = (fun quals -> (FStar_List.contains FStar_Absyn_Syntax.Private quals))
in (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _52_3118, _52_3120) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_tycon (_52_3124, _52_3126, _52_3128, _52_3130, _52_3132, quals, r) -> begin
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
| FStar_Absyn_Syntax.Sig_assume (_52_3146, _52_3148, quals, _52_3151) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_val_decl (_52_3155, _52_3157, quals, _52_3160) -> begin
if (is_private quals) then begin
[]
end else begin
(se)::[]
end
end
| FStar_Absyn_Syntax.Sig_main (_52_3164) -> begin
[]
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) -> begin
(se)::[]
end
| FStar_Absyn_Syntax.Sig_datacon (_52_3182) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, _52_3188) -> begin
(let check_priv = (fun lbs -> (let is_priv = (fun _52_17 -> (match (_52_17) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _52_3199; FStar_Absyn_Syntax.lbeff = _52_3197; FStar_Absyn_Syntax.lbdef = _52_3195} -> begin
(match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| Some (_52_3204, qs) -> begin
(FStar_List.contains FStar_Absyn_Syntax.Private qs)
end
| _52_3209 -> begin
false
end)
end
| _52_3211 -> begin
false
end))
in (let some_priv = (FStar_All.pipe_right lbs (FStar_Util.for_some is_priv))
in if some_priv then begin
if (FStar_All.pipe_right lbs (FStar_Util.for_some (fun x -> (let _105_1135 = (is_priv x)
in (FStar_All.pipe_right _105_1135 Prims.op_Negation))))) then begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Some but not all functions in this mutually recursive nest are marked private", r))))
end else begin
true
end
end else begin
false
end)))
in (let _52_3218 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.partition (fun lb -> ((FStar_Absyn_Util.is_pure_or_ghost_function lb.FStar_Absyn_Syntax.lbtyp) && (let _105_1137 = (FStar_Absyn_Util.is_lemma lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_left Prims.op_Negation _105_1137))))))
in (match (_52_3218) with
| (pure_funs, rest) -> begin
(match ((pure_funs, rest)) with
| (_52_3222::_52_3220, _52_3227::_52_3225) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Pure functions cannot be mutually recursive with impure functions", r))))
end
| (_52_3233::_52_3231, []) -> begin
if (check_priv pure_funs) then begin
[]
end else begin
(se)::[]
end
end
| ([], _52_3241::_52_3239) -> begin
if (check_priv rest) then begin
[]
end else begin
(FStar_All.pipe_right rest (FStar_List.collect (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_52_3246) -> begin
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

let get_exports = (fun env modul non_private_decls -> (let assume_vals = (fun decls -> (FStar_All.pipe_right decls (FStar_List.map (fun _52_18 -> (match (_52_18) with
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
FStar_Absyn_Syntax.Sig_val_decl ((lid, t, (FStar_Absyn_Syntax.Assumption)::quals, r))
end
| s -> begin
s
end)))))
in if modul.FStar_Absyn_Syntax.is_interface then begin
non_private_decls
end else begin
(let exports = (let _105_1150 = (FStar_Tc_Env.modules env)
in (FStar_Util.find_map _105_1150 (fun m -> if (m.FStar_Absyn_Syntax.is_interface && (FStar_Absyn_Syntax.lid_equals modul.FStar_Absyn_Syntax.name m.FStar_Absyn_Syntax.name)) then begin
(let _105_1149 = (FStar_All.pipe_right m.FStar_Absyn_Syntax.exports assume_vals)
in Some (_105_1149))
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
in (let env = (let _52_3275 = env
in (let _105_1155 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _52_3275.FStar_Tc_Env.solver; FStar_Tc_Env.range = _52_3275.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _52_3275.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _52_3275.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _52_3275.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _52_3275.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _52_3275.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _52_3275.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _52_3275.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _52_3275.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _52_3275.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _52_3275.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _52_3275.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _52_3275.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _52_3275.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _52_3275.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _52_3275.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _105_1155; FStar_Tc_Env.default_effects = _52_3275.FStar_Tc_Env.default_effects}))
in (let _52_3278 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (let _52_3284 = (tc_decls true env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_52_3284) with
| (ses, non_private_decls, env) -> begin
((let _52_3285 = modul
in {FStar_Absyn_Syntax.name = _52_3285.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _52_3285.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _52_3285.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _52_3285.FStar_Absyn_Syntax.is_deserialized}), non_private_decls, env)
end))))))))

let tc_more_partial_modul = (fun env modul decls -> (let _52_3293 = (tc_decls true env decls false)
in (match (_52_3293) with
| (ses, non_private_decls, env) -> begin
(let modul = (let _52_3294 = modul
in {FStar_Absyn_Syntax.name = _52_3294.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _52_3294.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _52_3294.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _52_3294.FStar_Absyn_Syntax.is_deserialized})
in (modul, non_private_decls, env))
end)))

let finish_partial_modul = (fun env modul npds -> (let exports = (get_exports env modul npds)
in (let modul = (let _52_3301 = modul
in {FStar_Absyn_Syntax.name = _52_3301.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _52_3301.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (let env = (FStar_Tc_Env.finish_module env modul)
in (let _52_3311 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(let _52_3305 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (let _52_3307 = if ((not (modul.FStar_Absyn_Syntax.is_interface)) || (let _105_1168 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.contains modul.FStar_Absyn_Syntax.name.FStar_Ident.str _105_1168))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
end else begin
()
end
in (let _52_3309 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _105_1169 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _105_1169 Prims.ignore)))))
end else begin
()
end
in (modul, env))))))

let tc_modul = (fun env modul -> (let _52_3318 = (tc_partial_modul env modul)
in (match (_52_3318) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))

let add_modul_to_tcenv = (fun en m -> (let do_sigelt = (fun en elt -> (let env = (FStar_Tc_Env.push_sigelt en elt)
in (let _52_3325 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _105_1182 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _105_1182 m)))))

let check_module = (fun env m -> (let _52_3330 = if ((let _105_1187 = (FStar_ST.read FStar_Options.debug)
in (FStar_List.length _105_1187)) <> 0) then begin
(let _105_1188 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _105_1188))
end else begin
()
end
in (let _52_3343 = if m.FStar_Absyn_Syntax.is_deserialized then begin
(let env' = (add_modul_to_tcenv env m)
in (m, env'))
end else begin
(let _52_3335 = (tc_modul env m)
in (match (_52_3335) with
| (m, env) -> begin
(let _52_3339 = if (FStar_ST.read FStar_Options.serialize_mods) then begin
(let c_file_name = (let _105_1193 = (let _105_1192 = (let _105_1191 = (let _105_1190 = (let _105_1189 = (FStar_Options.get_fstar_home ())
in (Prims.strcat _105_1189 "/"))
in (Prims.strcat _105_1190 FStar_Options.cache_dir))
in (Prims.strcat _105_1191 "/"))
in (Prims.strcat _105_1192 (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)))
in (Prims.strcat _105_1193 ".cache"))
in (let _52_3337 = (FStar_Util.print_string (Prims.strcat (Prims.strcat "Serializing module " (FStar_Ident.text_of_lid m.FStar_Absyn_Syntax.name)) "\n"))
in (let _105_1194 = (FStar_Util.get_owriter c_file_name)
in (FStar_Absyn_SSyntax.serialize_modul _105_1194 m))))
end else begin
()
end
in (m, env))
end))
end
in (match (_52_3343) with
| (m, env) -> begin
(let _52_3344 = if (FStar_Options.should_dump m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _105_1195 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _105_1195))
end else begin
()
end
in ((m)::[], env))
end))))




