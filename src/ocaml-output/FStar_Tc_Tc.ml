
open Prims

let syn' = (fun env k -> (let _150_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _150_11 (Some (k)))))


let log : FStar_Tc_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _150_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _150_14))))))


let rng : FStar_Tc_Env.env  ->  FStar_Range.range = (fun env -> (FStar_Tc_Env.get_range env))


let instantiate_both : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (

let _49_6 = env
in {FStar_Tc_Env.solver = _49_6.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_6.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_6.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_6.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_6.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_6.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_6.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_6.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_6.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _49_6.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_6.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_6.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_6.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_6.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_6.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_6.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_6.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_6.FStar_Tc_Env.default_effects}))


let no_inst : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (

let _49_9 = env
in {FStar_Tc_Env.solver = _49_9.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_9.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_9.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_9.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_9.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_9.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_9.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_9.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_9.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _49_9.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_9.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_9.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_9.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_9.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_9.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_9.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_9.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_9.FStar_Tc_Env.default_effects}))


let mk_lex_list : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _150_34 = (let _150_33 = (let _150_32 = (let _150_27 = (let _150_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _150_25 -> FStar_Util.Inl (_150_25)) _150_26))
in ((_150_27), (Some (FStar_Absyn_Syntax.Implicit (false)))))
in (let _150_31 = (let _150_30 = (FStar_Absyn_Syntax.varg v)
in (let _150_29 = (let _150_28 = (FStar_Absyn_Syntax.varg tl)
in (_150_28)::[])
in (_150_30)::_150_29))
in (_150_32)::_150_31))
in ((FStar_Absyn_Util.lex_pair), (_150_33)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))


let is_eq : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun uu___177 -> (match (uu___177) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _49_19 -> begin
false
end))


let steps : FStar_Tc_Env.env  ->  FStar_Tc_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)


let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))


let norm_t : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _150_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _150_47 env t)))


let norm_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let _150_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _150_52 env k)))


let norm_c : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun env c -> (let _150_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _150_57 env c)))


let fxv_check : FStar_Absyn_Syntax.exp  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either  ->  FStar_Absyn_Syntax.bvvar FStar_Util.set  ->  Prims.unit = (fun head env kt fvs -> (

let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(

let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _150_70 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _150_70))
end
| FStar_Util.Inr (t) -> begin
(let _150_71 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _150_71))
end)
in (

let a = (FStar_Util.set_intersect fvs fvs'.FStar_Absyn_Syntax.fxvs)
in if (FStar_Util.set_is_empty a) then begin
()
end else begin
if (not (norm)) then begin
(aux true kt)
end else begin
(

let fail = (fun _49_43 -> (match (()) with
| () -> begin
(

let escaping = (let _150_76 = (let _150_75 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _150_75 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _150_76 (FStar_String.concat ", ")))
in (

let msg = if ((FStar_Util.set_count a) > (Prims.parse_int "1")) then begin
(let _150_77 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _150_77))
end else begin
(let _150_78 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _150_78))
end
in (let _150_81 = (let _150_80 = (let _150_79 = (FStar_Tc_Env.get_range env)
in ((msg), (_150_79)))
in FStar_Errors.Error (_150_80))
in (Prims.raise _150_81))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(

let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _49_53 -> begin
(fail ())
end))
end
| FStar_Util.Inr (t) -> begin
(

let s = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (match ((FStar_Tc_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _49_60 -> begin
(fail ())
end))
end))
end
end))
end)
in (aux false kt)))


let maybe_push_binding : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binder  ->  FStar_Tc_Env.env = (fun env b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
env
end else begin
(match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(

let b = FStar_Tc_Env.Binding_typ (((a.FStar_Absyn_Syntax.v), (a.FStar_Absyn_Syntax.sort)))
in (FStar_Tc_Env.push_local_binding env b))
end
| FStar_Util.Inr (x) -> begin
(

let b = FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))
in (FStar_Tc_Env.push_local_binding env b))
end)
end)


let maybe_make_subst = (fun uu___178 -> (match (uu___178) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl (((a), (t))))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr (((x), (e))))::[]
end
| _49_81 -> begin
[]
end))


let maybe_alpha_subst = (fun s b1 b2 -> if (FStar_Absyn_Syntax.is_null_binder b1) then begin
s
end else begin
(match ((((Prims.fst b1)), ((Prims.fst b2)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (FStar_Absyn_Util.bvar_eq a b) then begin
s
end else begin
(let _150_92 = (let _150_91 = (let _150_90 = (FStar_Absyn_Util.btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_150_90)))
in FStar_Util.Inl (_150_91))
in (_150_92)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _150_95 = (let _150_94 = (let _150_93 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_150_93)))
in FStar_Util.Inr (_150_94))
in (_150_95)::s)
end
end
| _49_96 -> begin
(failwith "impossible")
end)
end)


let maybe_extend_subst = (fun s b v -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
s
end else begin
(match ((((Prims.fst b)), ((Prims.fst v)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::s
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (e))))::s
end
| _49_111 -> begin
(failwith "Impossible")
end)
end)


let set_lcomp_result : FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.lcomp = (fun lc t -> (

let _49_114 = lc
in {FStar_Absyn_Syntax.eff_name = _49_114.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _49_114.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _49_116 -> (match (()) with
| () -> begin
(let _150_104 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _150_104 t))
end))}))


let value_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, FStar_Absyn_Syntax.lcomp) FStar_Util.either  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e tlc -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _150_111 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _150_111))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Absyn_Syntax.res_typ
in (

let _49_140 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
((e), (lc), (FStar_Tc_Rel.trivial_guard))
end
| Some (t') -> begin
(

let _49_129 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_113 = (FStar_Absyn_Print.typ_to_string t)
in (let _150_112 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _150_113 _150_112)))
end else begin
()
end
in (

let _49_133 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_49_133) with
| (e, g) -> begin
(

let _49_136 = (let _150_119 = (FStar_All.pipe_left (fun _150_118 -> Some (_150_118)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _150_119 env e lc g))
in (match (_49_136) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))
end)))
end)
in (match (_49_140) with
| (e, lc, g) -> begin
(

let _49_141 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_120 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _150_120))
end else begin
()
end
in ((e), (lc), (g)))
end)))))


let comp_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.lcomp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e lc -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
((e), (lc), (FStar_Tc_Rel.trivial_guard))
end
| Some (t) -> begin
(FStar_Tc_Util.weaken_result_typ env e lc t)
end))


let check_expected_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp Prims.option  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp)  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env copt _49_153 -> (match (_49_153) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_49_155) -> begin
copt
end
| None -> begin
(

let c1 = (FStar_Tc_Normalize.weak_norm_comp env c)
in (

let md = (FStar_Tc_Env.get_effect_decl env c1.FStar_Absyn_Syntax.effect_name)
in (match ((FStar_Tc_Env.default_effect env md.FStar_Absyn_Syntax.mname)) with
| None -> begin
None
end
| Some (l) -> begin
(

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

let def = (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = l; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = flags})
in Some (def)))
end)))
end)
in (match (expected_c_opt) with
| None -> begin
(let _150_133 = (norm_c env c)
in ((e), (_150_133), (FStar_Tc_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _49_169 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_136 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _150_135 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _150_134 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _150_136 _150_135 _150_134))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let expected_c' = (let _150_137 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _150_137))
in (

let _49_177 = (let _150_138 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _150_138))
in (match (_49_177) with
| (e, _49_175, g) -> begin
(

let _49_178 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_140 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _150_139 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _150_140 _150_139)))
end else begin
()
end
in ((e), (expected_c), (g)))
end)))))
end))
end))


let no_logical_guard = (fun env _49_184 -> (match (_49_184) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
((te), (kt), (f))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _150_146 = (let _150_145 = (let _150_144 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _150_143 = (FStar_Tc_Env.get_range env)
in ((_150_144), (_150_143))))
in FStar_Errors.Error (_150_145))
in (Prims.raise _150_146))
end)
end))


let binding_of_lb : (FStar_Absyn_Syntax.bvvdef, FStar_Ident.lident) FStar_Util.either  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.binding = (fun x t -> (match (x) with
| FStar_Util.Inl (bvd) -> begin
FStar_Tc_Env.Binding_var (((bvd), (t)))
end
| FStar_Util.Inr (lid) -> begin
FStar_Tc_Env.Binding_lid (((lid), (t)))
end))


let print_expected_ty : FStar_Tc_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _150_153 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _150_153))
end))


let with_implicits = (fun imps _49_202 -> (match (_49_202) with
| (e, l, g) -> begin
((e), (l), ((

let _49_203 = g
in {FStar_Tc_Rel.guard_f = _49_203.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _49_203.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)})))
end))


let add_implicit : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * FStar_Range.range), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * FStar_Range.range)) FStar_Util.either  ->  FStar_Tc_Rel.guard_t  ->  FStar_Tc_Rel.guard_t = (fun u g -> (

let _49_207 = g
in {FStar_Tc_Rel.guard_f = _49_207.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _49_207.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))


let rec tc_kind : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd * FStar_Tc_Rel.guard_t) = (fun env k -> (

let k = (FStar_Absyn_Util.compress_kind k)
in (

let w = (fun f -> (f k.FStar_Absyn_Syntax.pos))
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_lam (_)) | (FStar_Absyn_Syntax.Kind_delayed (_)) -> begin
(failwith "impossible")
end
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
((k), (FStar_Tc_Rel.trivial_guard))
end
| FStar_Absyn_Syntax.Kind_uvar (u, args) -> begin
(

let _49_226 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _150_206 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _150_205 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _150_206 _150_205)))
end else begin
()
end
in (

let _49_231 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_49_231) with
| (env, _49_230) -> begin
(

let _49_234 = (tc_args env args)
in (match (_49_234) with
| (args, g) -> begin
(let _150_208 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar ((u), (args))))
in ((_150_208), (g)))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _49_245; FStar_Absyn_Syntax.pos = _49_243; FStar_Absyn_Syntax.fvs = _49_241; FStar_Absyn_Syntax.uvs = _49_239}) -> begin
(

let _49_254 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_49_254) with
| (_49_251, binders, body) -> begin
(

let _49_257 = (tc_args env args)
in (match (_49_257) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _150_212 = (let _150_211 = (let _150_210 = (let _150_209 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _150_209))
in ((_150_210), (k.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_211))
in (Prims.raise _150_212))
end else begin
(

let _49_290 = (FStar_List.fold_left2 (fun _49_261 b a -> (match (_49_261) with
| (subst, args, guards) -> begin
(match ((((Prims.fst b)), ((Prims.fst a)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(

let _49_271 = (let _150_216 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _150_216))
in (match (_49_271) with
| (t, g) -> begin
(

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (let _150_218 = (let _150_217 = (FStar_Absyn_Syntax.targ t)
in (_150_217)::args)
in ((subst), (_150_218), ((g)::guards))))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(

let env = (let _150_219 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _150_219))
in (

let _49_283 = (tc_ghost_exp env e)
in (match (_49_283) with
| (e, _49_281, g) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (e))))::subst
in (let _150_221 = (let _150_220 = (FStar_Absyn_Syntax.varg e)
in (_150_220)::args)
in ((subst), (_150_221), ((g)::guards))))
end)))
end
| _49_286 -> begin
(Prims.raise (FStar_Errors.Error ((("Ill-typed argument to kind abbreviation"), ((FStar_Absyn_Util.range_of_arg a))))))
end)
end)) (([]), ([]), ([])) binders args)
in (match (_49_290) with
| (subst, args, guards) -> begin
(

let args = (FStar_List.rev args)
in (

let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
in (

let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (

let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (k'))))
in (let _150_224 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in ((k'), (_150_224)))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(

let _49_301 = (tc_kind env k)
in (match (_49_301) with
| (k, f) -> begin
(

let _49_304 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_49_304) with
| (args, g) -> begin
(

let kabr = (((Prims.fst kabr)), (args))
in (

let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((kabr), (k))))
in (let _150_226 = (FStar_Tc_Rel.conj_guard f g)
in ((kk), (_150_226)))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _49_314 = (tc_binders env bs)
in (match (_49_314) with
| (bs, env, g) -> begin
(

let _49_317 = (tc_kind env k)
in (match (_49_317) with
| (k, f) -> begin
(

let f = (FStar_Tc_Rel.close_guard bs f)
in (let _150_229 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k))))
in (let _150_228 = (FStar_Tc_Rel.conj_guard g f)
in ((_150_229), (_150_228)))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _150_230 = (FStar_Tc_Util.new_kvar env)
in ((_150_230), (FStar_Tc_Rel.trivial_guard)))
end))))
and tc_vbinder : FStar_Tc_Env.env  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env x -> (

let _49_324 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_49_324) with
| (t, g) -> begin
(

let x = (

let _49_325 = x
in {FStar_Absyn_Syntax.v = _49_325.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _49_325.FStar_Absyn_Syntax.p})
in (

let env' = (let _150_233 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _150_233))
in ((x), (env'), (g))))
end)))
and tc_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_Tc_Rel.trivial_guard))
end
| ((b, imp))::bs -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(

let _49_344 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_49_344) with
| (k, g) -> begin
(

let b = ((FStar_Util.Inl ((

let _49_345 = a
in {FStar_Absyn_Syntax.v = _49_345.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _49_345.FStar_Absyn_Syntax.p}))), (imp))
in (

let env' = (maybe_push_binding env b)
in (

let _49_352 = (aux env' bs)
in (match (_49_352) with
| (bs, env', g') -> begin
(let _150_241 = (let _150_240 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _150_240))
in (((b)::bs), (env'), (_150_241)))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _49_358 = (tc_vbinder env x)
in (match (_49_358) with
| (x, env', g) -> begin
(

let b = ((FStar_Util.Inr (x)), (imp))
in (

let _49_363 = (aux env' bs)
in (match (_49_363) with
| (bs, env', g') -> begin
(let _150_243 = (let _150_242 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _150_242))
in (((b)::bs), (env'), (_150_243)))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.args * FStar_Tc_Rel.guard_t) = (fun env args -> (FStar_List.fold_right (fun _49_368 _49_371 -> (match (((_49_368), (_49_371))) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(

let _49_378 = (tc_typ env t)
in (match (_49_378) with
| (t, _49_376, g') -> begin
(let _150_248 = (FStar_Tc_Rel.conj_guard g g')
in (((((FStar_Util.Inl (t)), (imp)))::args), (_150_248)))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _49_385 = (tc_ghost_exp env e)
in (match (_49_385) with
| (e, _49_383, g') -> begin
(let _150_249 = (FStar_Tc_Rel.conj_guard g g')
in (((((FStar_Util.Inr (e)), (imp)))::args), (_150_249)))
end))
end)
end)) args (([]), (FStar_Tc_Rel.trivial_guard))))
and tc_pats : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list Prims.list  ->  (FStar_Absyn_Syntax.args Prims.list * FStar_Tc_Rel.guard_t) = (fun env pats -> (FStar_List.fold_right (fun p _49_391 -> (match (_49_391) with
| (pats, g) -> begin
(

let _49_394 = (tc_args env p)
in (match (_49_394) with
| (args, g') -> begin
(let _150_254 = (FStar_Tc_Rel.conj_guard g g')
in (((args)::pats), (_150_254)))
end))
end)) pats (([]), (FStar_Tc_Rel.trivial_guard))))
and tc_comp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _49_401 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_49_401) with
| (t, g) -> begin
(let _150_257 = (FStar_Absyn_Syntax.mk_Total t)
in ((_150_257), (g)))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(

let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (

let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (

let tc = (let _150_260 = (let _150_259 = (let _150_258 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_150_258)::c.FStar_Absyn_Syntax.effect_args)
in ((head), (_150_259)))
in (FStar_Absyn_Syntax.mk_Typ_app _150_260 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (

let _49_409 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_49_409) with
| (tc, f) -> begin
(

let _49_413 = (FStar_Absyn_Util.head_and_args tc)
in (match (_49_413) with
| (_49_411, args) -> begin
(

let _49_425 = (match (args) with
| ((FStar_Util.Inl (res), _49_418))::args -> begin
((res), (args))
end
| _49_422 -> begin
(failwith "Impossible")
end)
in (match (_49_425) with
| (res, args) -> begin
(

let _49_441 = (let _150_262 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun uu___179 -> (match (uu___179) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(

let _49_432 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_49_432) with
| (env, _49_431) -> begin
(

let _49_437 = (tc_ghost_exp env e)
in (match (_49_437) with
| (e, _49_435, g) -> begin
((FStar_Absyn_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_Tc_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _150_262 FStar_List.unzip))
in (match (_49_441) with
| (flags, guards) -> begin
(let _150_264 = (FStar_Absyn_Syntax.mk_Comp (

let _49_442 = c
in {FStar_Absyn_Syntax.effect_name = _49_442.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _49_442.FStar_Absyn_Syntax.flags}))
in (let _150_263 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in ((_150_264), (_150_263))))
end))
end))
end))
end)))))
end))
and tc_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd * FStar_Tc_Rel.guard_t) = (fun env t -> (

let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (

let w = (fun k -> (FStar_Absyn_Syntax.syn t.FStar_Absyn_Syntax.pos (Some (k))))
in (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let top = t
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(

let k = (FStar_Tc_Env.lookup_btvar env a)
in (

let a = (

let _49_454 = a
in {FStar_Absyn_Syntax.v = _49_454.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _49_454.FStar_Absyn_Syntax.p})
in (

let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (

let _49_461 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_49_461) with
| (t, k, implicits) -> begin
(FStar_All.pipe_left (with_implicits implicits) ((t), (k), (FStar_Tc_Rel.trivial_guard)))
end)))))
end
| FStar_Absyn_Syntax.Typ_const (i) when (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.eqT_lid) -> begin
(

let k = (FStar_Tc_Util.new_kvar env)
in (

let qk = (FStar_Absyn_Util.eqT_k k)
in (

let i = (

let _49_466 = i
in {FStar_Absyn_Syntax.v = _49_466.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _49_466.FStar_Absyn_Syntax.p})
in (let _150_287 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in ((_150_287), (qk), (FStar_Tc_Rel.trivial_guard))))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(

let k = (FStar_Tc_Util.new_kvar env)
in (

let qk = (FStar_Absyn_Util.allT_k k)
in (

let i = (

let _49_473 = i
in {FStar_Absyn_Syntax.v = _49_473.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _49_473.FStar_Absyn_Syntax.p})
in (let _150_288 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in ((_150_288), (qk), (FStar_Tc_Rel.trivial_guard))))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(

let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _49_481 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (

let i = (

let _49_483 = i
in {FStar_Absyn_Syntax.v = _49_483.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _49_483.FStar_Absyn_Syntax.p})
in (

let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (

let _49_490 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_49_490) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) ((t), (k), (FStar_Tc_Rel.trivial_guard)))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(

let _49_498 = (tc_binders env bs)
in (match (_49_498) with
| (bs, env, g) -> begin
(

let _49_501 = (tc_comp env cod)
in (match (_49_501) with
| (cod, f) -> begin
(

let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (cod))))
in (

let _49_586 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _49_524; FStar_Absyn_Syntax.result_typ = _49_522; FStar_Absyn_Syntax.effect_args = ((FStar_Util.Inl (pre), _49_518))::((FStar_Util.Inl (post), _49_513))::((FStar_Util.Inr (pats), _49_508))::[]; FStar_Absyn_Syntax.flags = _49_504}) -> begin
(

let rec extract_pats = (fun pats -> (match ((let _150_293 = (FStar_Absyn_Util.compress_exp pats)
in _150_293.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _49_539); FStar_Absyn_Syntax.tk = _49_536; FStar_Absyn_Syntax.pos = _49_534; FStar_Absyn_Syntax.fvs = _49_532; FStar_Absyn_Syntax.uvs = _49_530}, (_49_554)::((FStar_Util.Inr (hd), _49_551))::((FStar_Util.Inr (tl), _49_546))::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(

let _49_560 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_49_560) with
| (head, args) -> begin
(

let pat = (match (args) with
| ((_)::(arg)::[]) | ((arg)::[]) -> begin
(arg)::[]
end
| _49_567 -> begin
[]
end)
in (let _150_294 = (extract_pats tl)
in (FStar_List.append pat _150_294)))
end))
end
| _49_570 -> begin
[]
end))
in (

let pats = (let _150_295 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _150_295))
in (

let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _49_576 -> (match (_49_576) with
| (b, _49_575) -> begin
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
(let _150_298 = (let _150_297 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _150_297))
in (FStar_Errors.warn t.FStar_Absyn_Syntax.pos _150_298))
end))))
end
| _49_585 -> begin
(failwith "Impossible")
end)
end else begin
()
end
in (let _150_300 = (let _150_299 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _150_299))
in ((t), (FStar_Absyn_Syntax.ktype), (_150_300)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(

let _49_595 = (tc_binders env bs)
in (match (_49_595) with
| (bs, env, g) -> begin
(

let _49_599 = (tc_typ env t)
in (match (_49_599) with
| (t, k, f) -> begin
(

let k = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k)) top.FStar_Absyn_Syntax.pos)
in (let _150_305 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t))))
in (let _150_304 = (let _150_303 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _150_303))
in ((_150_305), (k), (_150_304)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(

let _49_608 = (tc_vbinder env x)
in (match (_49_608) with
| (x, env, f1) -> begin
(

let _49_612 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_308 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _150_307 = (FStar_Absyn_Print.typ_to_string phi)
in (let _150_306 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _150_308 _150_307 _150_306))))
end else begin
()
end
in (

let _49_616 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_49_616) with
| (phi, f2) -> begin
(let _150_315 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine ((x), (phi))))
in (let _150_314 = (let _150_313 = (let _150_312 = (let _150_311 = (FStar_Absyn_Syntax.v_binder x)
in (_150_311)::[])
in (FStar_Tc_Rel.close_guard _150_312 f2))
in (FStar_Tc_Rel.conj_guard f1 _150_313))
in ((_150_315), (FStar_Absyn_Syntax.ktype), (_150_314))))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let _49_621 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_318 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _150_317 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _150_316 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _150_318 _150_317 _150_316))))
end else begin
()
end
in (

let _49_626 = (tc_typ (no_inst env) head)
in (match (_49_626) with
| (head, k1', f1) -> begin
(

let args0 = args
in (

let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (

let _49_629 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_322 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _150_321 = (FStar_Absyn_Print.typ_to_string head)
in (let _150_320 = (FStar_Absyn_Print.kind_to_string k1')
in (let _150_319 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _150_322 _150_321 _150_320 _150_319)))))
end else begin
()
end
in (

let check_app = (fun _49_632 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_49_634) -> begin
(

let _49_638 = (tc_args env args)
in (match (_49_638) with
| (args, g) -> begin
(

let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (

let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (

let kres = (let _150_325 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _150_325 Prims.fst))
in (

let bs = (let _150_326 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _150_326))
in (

let kar = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (kres)) k1.FStar_Absyn_Syntax.pos)
in (

let _49_644 = (let _150_327 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _150_327))
in ((kres), (args), (g))))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(

let rec check_args = (fun outargs subst g formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(let _150_338 = (FStar_Absyn_Util.subst_kind subst kres)
in ((_150_338), ((FStar_List.rev outargs)), (g)))
end
| ((((_, None))::_, ((_, Some (FStar_Absyn_Syntax.Implicit (_))))::_)) | ((((_, Some (FStar_Absyn_Syntax.Equality)))::_, ((_, Some (FStar_Absyn_Syntax.Implicit (_))))::_)) -> begin
(let _150_342 = (let _150_341 = (let _150_340 = (let _150_339 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _150_339))
in (("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit"), (_150_340)))
in FStar_Errors.Error (_150_341))
in (Prims.raise _150_342))
end
| ((((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_))))::rest, ((_, None))::_)) | ((((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_))))::rest, [])) -> begin
(

let formal = (FStar_List.hd formals)
in (

let _49_725 = (let _150_343 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _150_343))
in (match (_49_725) with
| (t, u) -> begin
(

let targ = (let _150_345 = (FStar_All.pipe_left (fun _150_344 -> Some (_150_344)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_150_345)))
in (

let g = (add_implicit (FStar_Util.Inl (u)) g)
in (

let subst = (maybe_extend_subst subst formal targ)
in (check_args ((targ)::outargs) subst g rest args))))
end)))
end
| ((((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_))))::rest, ((_, None))::_)) | ((((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_))))::rest, [])) -> begin
(

let formal = (FStar_List.hd formals)
in (

let _49_758 = (let _150_346 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _150_346))
in (match (_49_758) with
| (e, u) -> begin
(

let varg = (let _150_348 = (FStar_All.pipe_left (fun _150_347 -> Some (_150_347)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (e)), (_150_348)))
in (

let g = (add_implicit (FStar_Util.Inr (u)) g)
in (

let subst = (maybe_extend_subst subst formal varg)
in (check_args ((varg)::outargs) subst g rest args))))
end)))
end
| ((formal)::formals, (actual)::actuals) -> begin
(match (((formal), (actual))) with
| ((FStar_Util.Inl (a), aqual), (FStar_Util.Inl (t), imp)) -> begin
(

let formal_k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _49_779 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_350 = (FStar_Absyn_Print.arg_to_string actual)
in (let _150_349 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _150_350 _150_349)))
end else begin
()
end
in (

let _49_785 = (tc_typ_check (

let _49_781 = env
in {FStar_Tc_Env.solver = _49_781.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_781.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_781.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_781.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_781.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_781.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_781.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_781.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_781.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_781.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_781.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_781.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_781.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_781.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_781.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_781.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _49_781.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_781.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_781.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_49_785) with
| (t, g') -> begin
(

let _49_786 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_351 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _150_351))
end else begin
()
end
in (

let actual = ((FStar_Util.Inl (t)), (imp))
in (

let g' = (let _150_353 = (let _150_352 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _150_352))
in (FStar_Tc_Rel.imp_guard _150_353 g'))
in (

let subst = (maybe_extend_subst subst formal actual)
in (let _150_354 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _150_354 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(

let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (

let env' = (

let _49_802 = env'
in {FStar_Tc_Env.solver = _49_802.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_802.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_802.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_802.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_802.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_802.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_802.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_802.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_802.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_802.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_802.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_802.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_802.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_802.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_802.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_802.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _49_802.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_802.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_802.FStar_Tc_Env.default_effects})
in (

let _49_805 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_356 = (FStar_Absyn_Print.arg_to_string actual)
in (let _150_355 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _150_356 _150_355)))
end else begin
()
end
in (

let _49_811 = (tc_ghost_exp env' v)
in (match (_49_811) with
| (v, _49_809, g') -> begin
(

let actual = ((FStar_Util.Inr (v)), (imp))
in (

let g' = (let _150_358 = (let _150_357 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _150_357))
in (FStar_Tc_Rel.imp_guard _150_358 g'))
in (

let subst = (maybe_extend_subst subst formal actual)
in (let _150_359 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _150_359 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _49_818), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(

let tv = (FStar_Absyn_Util.b2t v)
in (let _150_361 = (let _150_360 = (FStar_Absyn_Syntax.targ tv)
in (_150_360)::actuals)
in (check_args outargs subst g ((formal)::formals) _150_361)))
end
| _49_828 -> begin
(Prims.raise (FStar_Errors.Error ((("Expected a type; got an expression"), (v.FStar_Absyn_Syntax.pos)))))
end)
end
| ((FStar_Util.Inr (_49_830), _49_833), (FStar_Util.Inl (_49_836), _49_839)) -> begin
(Prims.raise (FStar_Errors.Error ((("Expected an expression; got a type"), ((FStar_Absyn_Util.range_of_arg actual))))))
end)
end
| (_49_843, []) -> begin
(let _150_363 = (let _150_362 = (FStar_Absyn_Syntax.mk_Kind_arrow ((formals), (kres)) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _150_362))
in ((_150_363), ((FStar_List.rev outargs)), (g)))
end
| ([], _49_848) -> begin
(let _150_371 = (let _150_370 = (let _150_369 = (let _150_368 = (let _150_366 = (let _150_365 = (FStar_All.pipe_right outargs (FStar_List.filter (fun uu___180 -> (match (uu___180) with
| (_49_852, Some (FStar_Absyn_Syntax.Implicit (_49_854))) -> begin
false
end
| _49_859 -> begin
true
end))))
in (FStar_List.length _150_365))
in (FStar_All.pipe_right _150_366 FStar_Util.string_of_int))
in (let _150_367 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _150_368 _150_367)))
in ((_150_369), (top.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_370))
in (Prims.raise _150_371))
end))
in (check_args [] [] f1 formals args))
end
| _49_861 -> begin
(let _150_374 = (let _150_373 = (let _150_372 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in ((_150_372), (top.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_373))
in (Prims.raise _150_374))
end)
end))
in (match ((let _150_378 = (let _150_375 = (FStar_Absyn_Util.compress_typ head)
in _150_375.FStar_Absyn_Syntax.n)
in (let _150_377 = (let _150_376 = (FStar_Absyn_Util.compress_kind k1)
in _150_376.FStar_Absyn_Syntax.n)
in ((_150_378), (_150_377))))) with
| (FStar_Absyn_Syntax.Typ_uvar (_49_863), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(

let result_k = (

let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (

let t = (FStar_Absyn_Syntax.mk_Typ_app ((head), (args)) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in ((t), (result_k), (FStar_Tc_Rel.trivial_guard))))
end
| _49_874 -> begin
(

let _49_878 = (check_app ())
in (match (_49_878) with
| (k, args, g) -> begin
(

let t = (FStar_Absyn_Syntax.mk_Typ_app ((head), (args)) (Some (k)) top.FStar_Absyn_Syntax.pos)
in ((t), (k), (g)))
end))
end)))))
end)))
end
| FStar_Absyn_Syntax.Typ_ascribed (t1, k1) -> begin
(

let _49_886 = (tc_kind env k1)
in (match (_49_886) with
| (k1, f1) -> begin
(

let _49_889 = (tc_typ_check env t1 k1)
in (match (_49_889) with
| (t1, f2) -> begin
(let _150_382 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' ((t1), (k1))))
in (let _150_381 = (FStar_Tc_Rel.conj_guard f1 f2)
in ((_150_382), (k1), (_150_381))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_49_891, k1) -> begin
(

let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(

let _49_900 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _150_384 = (FStar_Absyn_Print.typ_to_string s)
in (let _150_383 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _150_384 _150_383)))
end else begin
()
end
in (let _150_387 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' ((u), (k1))))
in ((_150_387), (k1), (FStar_Tc_Rel.trivial_guard))))
end
| _49_903 -> begin
(

let _49_904 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _150_389 = (FStar_Absyn_Print.typ_to_string s)
in (let _150_388 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _150_389 _150_388)))
end else begin
()
end
in ((s), (k1), (FStar_Tc_Rel.trivial_guard)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(

let _49_915 = (tc_typ env t)
in (match (_49_915) with
| (t, k, f) -> begin
(let _150_390 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (((t), (b), (r)))))
in ((_150_390), (k), (f)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(

let _49_926 = (tc_typ env t)
in (match (_49_926) with
| (t, k, f) -> begin
(let _150_391 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (p)))))
in ((_150_391), (k), (f)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(

let _49_935 = (tc_typ env t)
in (match (_49_935) with
| (t, k, f) -> begin
(let _150_392 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (l)))))
in ((_150_392), (k), (f)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(

let _49_943 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_49_943) with
| (quant, f) -> begin
(

let _49_946 = (tc_pats env pats)
in (match (_49_946) with
| (pats, g) -> begin
(

let g = (

let _49_947 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _49_947.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _49_947.FStar_Tc_Rel.implicits})
in (let _150_395 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((quant), (pats)))))
in (let _150_394 = (FStar_Tc_Util.force_tk quant)
in (let _150_393 = (FStar_Tc_Rel.conj_guard f g)
in ((_150_395), (_150_394), (_150_393))))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_unknown -> begin
(

let k = (FStar_Tc_Util.new_kvar env)
in (

let t = (FStar_Tc_Util.new_tvar env k)
in ((t), (k), (FStar_Tc_Rel.trivial_guard))))
end
| _49_954 -> begin
(let _150_397 = (let _150_396 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _150_396))
in (failwith _150_397))
end))))))
and tc_typ_check : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env t k -> (

let _49_961 = (tc_typ env t)
in (match (_49_961) with
| (t, k', f) -> begin
(

let env = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (

let f' = if env.FStar_Tc_Env.use_eq then begin
(FStar_Tc_Rel.keq env (Some (t)) k' k)
end else begin
(FStar_Tc_Rel.subkind env k' k)
end
in (

let f = (FStar_Tc_Rel.conj_guard f f')
in ((t), (f)))))
end)))
and tc_value : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (

let env = (FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
in (

let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (_49_970, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let t = (FStar_Tc_Env.lookup_bvar env x)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar (

let _49_977 = x
in {FStar_Absyn_Syntax.v = _49_977.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _49_977.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (

let _49_983 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_49_983) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _150_404 = (let _150_403 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _150_403))
in FStar_Util.Inr (_150_404))
end
in (let _150_405 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _150_405)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(

let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_fvar (((

let _49_990 = v
in {FStar_Absyn_Syntax.v = _49_990.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _49_990.FStar_Absyn_Syntax.p})), (dc)) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (

let _49_996 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_49_996) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _150_407 = (let _150_406 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _150_406))
in FStar_Util.Inr (_150_407))
end
in (

let is_data_ctor = (fun uu___181 -> (match (uu___181) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _49_1006 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _150_413 = (let _150_412 = (let _150_411 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _150_410 = (FStar_Tc_Env.get_range env)
in ((_150_411), (_150_410))))
in FStar_Errors.Error (_150_412))
in (Prims.raise _150_413))
end else begin
(let _150_414 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _150_414))
end))
end))))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(

let t = (FStar_Tc_Recheck.typing_const e.FStar_Absyn_Syntax.pos c)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_constant c (Some (t)) e.FStar_Absyn_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)))))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let fail = (fun msg t -> (let _150_419 = (let _150_418 = (let _150_417 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_150_417), (top.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_418))
in (Prims.raise _150_419)))
in (

let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(

let _49_1027 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _49_1026 -> begin
(failwith "Impossible")
end)
in (

let _49_1032 = (tc_binders env bs)
in (match (_49_1032) with
| (bs, envbody, g) -> begin
((None), (bs), ([]), (None), (envbody), (g))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Absyn_Util.compress_typ t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _150_428 = (FStar_Absyn_Util.compress_typ t)
in _150_428.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(

let _49_1061 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _49_1060 -> begin
(failwith "Impossible")
end)
in (

let _49_1066 = (tc_binders env bs)
in (match (_49_1066) with
| (bs, envbody, g) -> begin
(

let _49_1070 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_49_1070) with
| (envbody, _49_1069) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (g))
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(

let rec tc_binders = (fun _49_1080 bs_annot c bs -> (match (_49_1080) with
| (out, env, g, subst) -> begin
(match (((bs_annot), (bs))) with
| ([], []) -> begin
(let _150_437 = (FStar_Absyn_Util.subst_comp subst c)
in (((FStar_List.rev out)), (env), (g), (_150_437)))
end
| ((hdannot)::tl_annot, (hd)::tl) -> begin
(match (((hdannot), (hd))) with
| ((FStar_Util.Inl (_49_1095), _49_1098), (FStar_Util.Inr (_49_1101), _49_1104)) -> begin
(

let env = (maybe_push_binding env hdannot)
in (tc_binders (((hdannot)::out), (env), (g), (subst)) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _49_1111), (FStar_Util.Inl (b), imp)) -> begin
(

let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _49_1129 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
((ka), (FStar_Tc_Rel.trivial_guard))
end
| _49_1121 -> begin
(

let _49_1124 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_49_1124) with
| (k, g1) -> begin
(

let g2 = (FStar_Tc_Rel.keq env None ka k)
in (

let g = (let _150_438 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _150_438))
in ((k), (g))))
end))
end)
in (match (_49_1129) with
| (k, g) -> begin
(

let b = ((FStar_Util.Inl ((

let _49_1130 = b
in {FStar_Absyn_Syntax.v = _49_1130.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _49_1130.FStar_Absyn_Syntax.p}))), (imp))
in (

let env = (maybe_push_binding env b)
in (

let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders (((b)::out), (env), (g), (subst)) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _49_1138), (FStar_Util.Inr (y), imp)) -> begin
(

let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _49_1160 = (match ((let _150_439 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _150_439.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
((tx), (g))
end
| _49_1148 -> begin
(

let _49_1149 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_440 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _150_440))
end else begin
()
end
in (

let _49_1155 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_49_1155) with
| (t, _49_1153, g1) -> begin
(

let g2 = (FStar_Tc_Rel.teq env tx t)
in (

let g = (let _150_441 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _150_441))
in ((t), (g))))
end)))
end)
in (match (_49_1160) with
| (t, g) -> begin
(

let b = ((FStar_Util.Inr ((

let _49_1161 = y
in {FStar_Absyn_Syntax.v = _49_1161.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _49_1161.FStar_Absyn_Syntax.p}))), (imp))
in (

let env = (maybe_push_binding env b)
in (

let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders (((b)::out), (env), (g), (subst)) tl_annot c tl))))
end)))
end
| _49_1167 -> begin
(let _150_444 = (let _150_443 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _150_442 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _150_443 _150_442)))
in (fail _150_444 t))
end)
end
| ([], _49_1170) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _49_1179; FStar_Absyn_Syntax.pos = _49_1177; FStar_Absyn_Syntax.fvs = _49_1175; FStar_Absyn_Syntax.uvs = _49_1173} -> begin
(tc_binders ((out), (env), (g), (subst)) bs_annot c' bs)
end
| t -> begin
(let _150_446 = (let _150_445 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _150_445))
in (fail _150_446 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_49_1187, []) -> begin
(

let c = (let _150_447 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs_annot), (c)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _150_447 c.FStar_Absyn_Syntax.pos))
in (let _150_448 = (FStar_Absyn_Util.subst_comp subst c)
in (((FStar_List.rev out)), (env), (g), (_150_448))))
end)
end))
in (

let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
((env), ([]))
end
| letrecs -> begin
(

let _49_1196 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_453 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _150_453))
end else begin
()
end
in (

let r = (FStar_Tc_Env.get_range env)
in (

let env = (

let _49_1199 = env
in {FStar_Tc_Env.solver = _49_1199.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_1199.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_1199.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_1199.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_1199.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_1199.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_1199.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_1199.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_1199.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_1199.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_1199.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_1199.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_1199.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _49_1199.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_1199.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_1199.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_1199.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_1199.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_1199.FStar_Tc_Env.default_effects})
in (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_49_1206), _49_1209) -> begin
[]
end
| (FStar_Util.Inr (x), _49_1214) -> begin
(match ((let _150_459 = (let _150_458 = (let _150_457 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _150_457))
in (FStar_Absyn_Util.unrefine _150_458))
in _150_459.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_49_1217) -> begin
[]
end
| _49_1220 -> begin
(let _150_460 = (FStar_Absyn_Util.bvar_to_exp x)
in (_150_460)::[])
end)
end)))))
in (

let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (

let as_lex_list = (fun dec -> (

let _49_1227 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_49_1227) with
| (head, _49_1226) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _49_1230) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _49_1234 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let prev_dec = (

let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun uu___182 -> (match (uu___182) with
| FStar_Absyn_Syntax.DECREASES (_49_1238) -> begin
true
end
| _49_1241 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(

let _49_1245 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _150_469 = (let _150_468 = (let _150_467 = (let _150_465 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _150_464 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _150_465 _150_464)))
in (let _150_466 = (FStar_Tc_Env.get_range env)
in ((_150_467), (_150_466))))
in FStar_Errors.Error (_150_468))
in (Prims.raise _150_469))
end else begin
()
end
in (

let dec = (as_lex_list dec)
in (

let subst = (FStar_List.map2 (fun b a -> (match (((b), (a))) with
| ((FStar_Util.Inl (formal), _49_1253), (FStar_Util.Inl (actual), _49_1258)) -> begin
(let _150_473 = (let _150_472 = (FStar_Absyn_Util.btvar_to_typ actual)
in ((formal.FStar_Absyn_Syntax.v), (_150_472)))
in FStar_Util.Inl (_150_473))
end
| ((FStar_Util.Inr (formal), _49_1264), (FStar_Util.Inr (actual), _49_1269)) -> begin
(let _150_475 = (let _150_474 = (FStar_Absyn_Util.bvar_to_exp actual)
in ((formal.FStar_Absyn_Syntax.v), (_150_474)))
in FStar_Util.Inr (_150_475))
end
| _49_1273 -> begin
(failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _49_1276 -> begin
(

let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| (i)::[] -> begin
i
end
| _49_1281 -> begin
(mk_lex_list actual_args)
end))
end))
in (

let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _49_1285 -> (match (_49_1285) with
| (l, t0) -> begin
(

let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _150_477 = (FStar_Absyn_Util.compress_typ t)
in _150_477.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(

let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (

let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (

let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun uu___183 -> (match (uu___183) with
| FStar_Absyn_Syntax.DECREASES (_49_1301) -> begin
true
end
| _49_1304 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(

let dec = (as_lex_list dec)
in (

let dec = (

let subst = (let _150_481 = (let _150_480 = (let _150_479 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_150_479)))
in FStar_Util.Inr (_150_480))
in (_150_481)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _150_486 = (let _150_485 = (let _150_484 = (FStar_Absyn_Syntax.varg dec)
in (let _150_483 = (let _150_482 = (FStar_Absyn_Syntax.varg prev_dec)
in (_150_482)::[])
in (_150_484)::_150_483))
in ((precedes), (_150_485)))
in (FStar_Absyn_Syntax.mk_Typ_app _150_486 None r))))
end
| _49_1312 -> begin
(

let formal_args = (let _150_489 = (let _150_488 = (let _150_487 = (FStar_Absyn_Syntax.v_binder y)
in (_150_487)::[])
in (FStar_List.append bs _150_488))
in (FStar_All.pipe_right _150_489 filter_types_and_functions))
in (

let lhs = (match (formal_args) with
| (i)::[] -> begin
i
end
| _49_1317 -> begin
(mk_lex_list formal_args)
end)
in (let _150_494 = (let _150_493 = (let _150_492 = (FStar_Absyn_Syntax.varg lhs)
in (let _150_491 = (let _150_490 = (FStar_Absyn_Syntax.varg prev_dec)
in (_150_490)::[])
in (_150_492)::_150_491))
in ((precedes), (_150_493)))
in (FStar_Absyn_Syntax.mk_Typ_app _150_494 None r))))
end)
in (

let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine ((y), (precedes)) None r)
in (

let bs = (FStar_List.append bs ((((FStar_Util.Inr ((

let _49_1321 = x
in {FStar_Absyn_Syntax.v = _49_1321.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _49_1321.FStar_Absyn_Syntax.p}))), (imp)))::[]))
in (

let t' = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None r)
in (

let _49_1325 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_497 = (FStar_Absyn_Print.lbname_to_string l)
in (let _150_496 = (FStar_Absyn_Print.typ_to_string t)
in (let _150_495 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _150_497 _150_496 _150_495))))
end else begin
()
end
in (

let _49_1332 = (let _150_499 = (let _150_498 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_498 Prims.fst))
in (tc_typ _150_499 t'))
in (match (_49_1332) with
| (t', _49_1329, _49_1331) -> begin
((l), (t'))
end)))))))))
end
| _49_1334 -> begin
(failwith "Impossible")
end)
end
| _49_1336 -> begin
(failwith "Impossible")
end))
end))))
in (let _150_505 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _49_1341 -> (match (_49_1341) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _150_504 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun uu___184 -> (match (uu___184) with
| (FStar_Util.Inl (x), t) -> begin
(let _150_503 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_150_503)::[])
end
| _49_1348 -> begin
[]
end))))
in ((_150_505), (_150_504))))))))))))
end))
in (

let _49_1353 = (tc_binders (([]), (env), (FStar_Tc_Rel.trivial_guard), ([])) bs' c bs)
in (match (_49_1353) with
| (bs, envbody, g, c) -> begin
(

let _49_1356 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
((envbody), ([]))
end
in (match (_49_1356) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (g)))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _49_1360) -> begin
(

let _49_1370 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_49_1370) with
| (_49_1364, bs, bs', copt, env, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (g))
end))
end
| _49_1372 -> begin
if (not (norm)) then begin
(let _150_506 = (whnf env t)
in (as_function_typ true _150_506))
end else begin
(

let _49_1381 = (expected_function_typ env None)
in (match (_49_1381) with
| (_49_1374, bs, _49_1377, c_opt, envbody, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_Tc_Env.use_eq
in (

let _49_1385 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_49_1385) with
| (env, topt) -> begin
(

let _49_1392 = (expected_function_typ env topt)
in (match (_49_1392) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(

let _49_1398 = (tc_exp (

let _49_1393 = envbody
in {FStar_Tc_Env.solver = _49_1393.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_1393.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_1393.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_1393.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_1393.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_1393.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_1393.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_1393.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_1393.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_1393.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_1393.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_1393.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_1393.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_1393.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _49_1393.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _49_1393.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_1393.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_1393.FStar_Tc_Env.default_effects}) body)
in (match (_49_1398) with
| (body, cbody, guard_body) -> begin
(

let _49_1399 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _150_509 = (FStar_Absyn_Print.exp_to_string body)
in (let _150_508 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _150_507 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _150_509 _150_508 _150_507))))
end else begin
()
end
in (

let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (

let _49_1402 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_510 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _150_510))
end else begin
()
end
in (

let _49_1409 = (let _150_512 = (let _150_511 = (cbody.FStar_Absyn_Syntax.comp ())
in ((body), (_150_511)))
in (check_expected_effect (

let _49_1404 = envbody
in {FStar_Tc_Env.solver = _49_1404.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_1404.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_1404.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_1404.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_1404.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_1404.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_1404.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_1404.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_1404.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_1404.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_1404.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_1404.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_1404.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_1404.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_1404.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_1404.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _49_1404.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_1404.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_1404.FStar_Tc_Env.default_effects}) c_opt _150_512))
in (match (_49_1409) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(

let _49_1411 = (let _150_513 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _150_513))
in (

let _49_1413 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _49_1413.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _49_1413.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(

let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (cbody)) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (

let e = (let _150_515 = (let _150_514 = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in ((_150_514), (tfun_computed), (Some (FStar_Absyn_Const.effect_Tot_lid))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _150_515 None top.FStar_Absyn_Syntax.pos))
in (

let _49_1436 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_49_1425) -> begin
(let _150_518 = (let _150_517 = (let _150_516 = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) (Some (t)) e.FStar_Absyn_Syntax.pos)
in ((_150_516), (t), (Some (FStar_Absyn_Const.effect_Tot_lid))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _150_517 None top.FStar_Absyn_Syntax.pos))
in ((_150_518), (t), (guard)))
end
| _49_1428 -> begin
(

let _49_1431 = if use_teq then begin
(let _150_519 = (FStar_Tc_Rel.teq env t tfun_computed)
in ((e), (_150_519)))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_49_1431) with
| (e, guard') -> begin
(let _150_521 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (t), (Some (FStar_Absyn_Const.effect_Tot_lid))) None top.FStar_Absyn_Syntax.pos)
in (let _150_520 = (FStar_Tc_Rel.conj_guard guard guard')
in ((_150_521), (t), (_150_520))))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_49_1436) with
| (e, tfun, guard) -> begin
(

let _49_1437 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_524 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _150_523 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _150_522 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _150_524 _150_523 _150_522))))
end else begin
()
end
in (

let c = if env.FStar_Tc_Env.top_level then begin
(FStar_Absyn_Syntax.mk_Total tfun)
end else begin
(FStar_Tc_Util.return_value env tfun e)
end
in (

let _49_1442 = (let _150_526 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _150_526 guard))
in (match (_49_1442) with
| (c, g) -> begin
((e), (c), (g))
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _49_1444 -> begin
(let _150_528 = (let _150_527 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _150_527))
in (failwith _150_528))
end))))
and tc_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (

let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (

let _49_1448 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_533 = (let _150_531 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _150_531))
in (let _150_532 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _150_533 _150_532)))
end else begin
()
end
in (

let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (

let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_49_1454) -> begin
(let _150_557 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _150_557))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _49_1474) -> begin
(

let _49_1479 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_49_1479) with
| (t1, f) -> begin
(

let _49_1483 = (let _150_558 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _150_558 e1))
in (match (_49_1483) with
| (e1, c, g) -> begin
(

let _49_1487 = (let _150_562 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _49_1484 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _150_562 e1 c f))
in (match (_49_1487) with
| (c, f) -> begin
(

let _49_1491 = (let _150_566 = (let _150_565 = (w c)
in (FStar_All.pipe_left _150_565 (FStar_Absyn_Syntax.mk_Exp_ascribed ((e1), (t1), (Some (c.FStar_Absyn_Syntax.eff_name))))))
in (comp_check_expected_typ env _150_566 c))
in (match (_49_1491) with
| (e, c, f2) -> begin
(let _150_568 = (let _150_567 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _150_567))
in ((e), (c), (_150_568)))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(

let pats_t = (let _150_574 = (let _150_573 = (let _150_569 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _150_569))
in (let _150_572 = (let _150_571 = (let _150_570 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _150_570))
in (_150_571)::[])
in ((_150_573), (_150_572))))
in (FStar_Absyn_Syntax.mk_Typ_app _150_574 None FStar_Absyn_Syntax.dummyRange))
in (

let _49_1501 = (let _150_575 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _150_575 e))
in (match (_49_1501) with
| (e, t, g) -> begin
(

let g = (

let _49_1502 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _49_1502.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _49_1502.FStar_Tc_Rel.implicits})
in (

let c = (let _150_576 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _150_576 FStar_Tc_Util.lcomp_of_comp))
in ((e), (c), (g))))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _150_577 = (FStar_Absyn_Util.compress_exp e)
in _150_577.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_49_1512, ({FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _49_1517; FStar_Absyn_Syntax.lbeff = _49_1515; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _49_1528 = (let _150_578 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _150_578 e1))
in (match (_49_1528) with
| (e1, c1, g1) -> begin
(

let _49_1532 = (tc_exp env e2)
in (match (_49_1532) with
| (e2, c2, g2) -> begin
(

let c = (FStar_Tc_Util.bind env (Some (e1)) c1 ((None), (c2)))
in (let _150_591 = (let _150_589 = (let _150_588 = (let _150_587 = (let _150_586 = (w c)
in (let _150_585 = (let _150_584 = (let _150_583 = (let _150_582 = (let _150_581 = (FStar_Absyn_Syntax.mk_lb ((x), (c1.FStar_Absyn_Syntax.eff_name), (FStar_Tc_Recheck.t_unit), (e1)))
in (_150_581)::[])
in ((false), (_150_582)))
in ((_150_583), (e2)))
in (FStar_Absyn_Syntax.mk_Exp_let _150_584))
in (FStar_All.pipe_left _150_586 _150_585)))
in ((_150_587), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_150_588))
in (FStar_Absyn_Syntax.mk_Exp_meta _150_589))
in (let _150_590 = (FStar_Tc_Rel.conj_guard g1 g2)
in ((_150_591), (c), (_150_590)))))
end))
end))
end
| _49_1535 -> begin
(

let _49_1539 = (tc_exp env e)
in (match (_49_1539) with
| (e, c, g) -> begin
(let _150_592 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Sequence)))))
in ((_150_592), (c), (g)))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(

let _49_1548 = (tc_exp env e)
in (match (_49_1548) with
| (e, c, g) -> begin
(let _150_593 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (i)))))
in ((_150_593), (c), (g)))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _150_595 = (let _150_594 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _150_594 Prims.fst))
in (FStar_All.pipe_right _150_595 instantiate_both))
in (

let _49_1555 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_597 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _150_596 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _150_597 _150_596)))
end else begin
()
end
in (

let _49_1560 = (tc_exp (no_inst env) head)
in (match (_49_1560) with
| (head, chead, g_head) -> begin
(

let aux = (fun _49_1562 -> (match (()) with
| () -> begin
(

let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _49_1566) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = (Prims.parse_int "2"))) -> begin
(

let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| ((FStar_Util.Inr (e1), _49_1578))::((FStar_Util.Inr (e2), _49_1573))::[] -> begin
(

let _49_1584 = (tc_exp env e1)
in (match (_49_1584) with
| (e1, c1, g1) -> begin
(

let _49_1588 = (tc_exp env e2)
in (match (_49_1588) with
| (e2, c2, g2) -> begin
(

let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (

let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (

let c2 = if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _150_603 = (let _150_600 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _150_600))
in (let _150_602 = (let _150_601 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _150_601 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _150_603 c2 _150_602)))
end else begin
(let _150_607 = (let _150_604 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _150_604))
in (let _150_606 = (let _150_605 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _150_605 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _150_607 _150_606 c2)))
end
in (

let c = (let _150_610 = (let _150_609 = (FStar_All.pipe_left (fun _150_608 -> Some (_150_608)) (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (FStar_Absyn_Util.t_bool)))))
in ((_150_609), (c2)))
in (FStar_Tc_Util.bind env None c1 _150_610))
in (

let e = (let _150_615 = (let _150_614 = (let _150_613 = (FStar_Absyn_Syntax.varg e1)
in (let _150_612 = (let _150_611 = (FStar_Absyn_Syntax.varg e2)
in (_150_611)::[])
in (_150_613)::_150_612))
in ((head), (_150_614)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_615 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _150_617 = (let _150_616 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _150_616))
in ((e), (c), (_150_617))))))))
end))
end))
end
| _49_1595 -> begin
(Prims.raise (FStar_Errors.Error ((("Expected two boolean arguments"), (head.FStar_Absyn_Syntax.pos)))))
end))
end
| _49_1597 -> begin
(

let thead = chead.FStar_Absyn_Syntax.res_typ
in (

let _49_1599 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_619 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _150_618 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _150_619 _150_618)))
end else begin
()
end
in (

let rec check_function_app = (fun norm tf -> (match ((let _150_624 = (FStar_Absyn_Util.unrefine tf)
in _150_624.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_Tc_Rel.trivial_guard))
end
| ((FStar_Util.Inl (t), _49_1632))::_49_1628 -> begin
(Prims.raise (FStar_Errors.Error ((("Explicit type applications on a term with unknown type; add an annotation?"), (t.FStar_Absyn_Syntax.pos)))))
end
| ((FStar_Util.Inr (e), imp))::tl -> begin
(

let _49_1644 = (tc_exp env e)
in (match (_49_1644) with
| (e, c, g_e) -> begin
(

let _49_1648 = (tc_args env tl)
in (match (_49_1648) with
| (args, comps, g_rest) -> begin
(let _150_629 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((((FStar_Util.Inr (e)), (imp)))::args), ((c)::comps), (_150_629)))
end))
end))
end))
in (

let _49_1652 = (tc_args env args)
in (match (_49_1652) with
| (args, comps, g_args) -> begin
(

let bs = (let _150_630 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _150_630))
in (

let cres = (let _150_631 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _150_631 top.FStar_Absyn_Syntax.pos))
in (

let _49_1655 = (let _150_633 = (let _150_632 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (cres)) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _150_632))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _150_633))
in (

let comp = (let _150_636 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c ((None), (out)))) ((chead)::comps) _150_636))
in (let _150_638 = (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _150_637 = (FStar_Tc_Rel.conj_guard g_head g_args)
in ((_150_638), (comp), (_150_637))))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let vars = (FStar_Tc_Env.binders env)
in (

let rec tc_args = (fun _49_1672 bs cres args -> (match (_49_1672) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match (((bs), (args))) with
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_49_1680))))::rest, ((_49_1688, None))::_49_1686) -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _49_1694 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (

let _49_1698 = (let _150_648 = (let _150_647 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _150_647))
in (FStar_Tc_Rel.new_tvar _150_648 vars k))
in (match (_49_1698) with
| (targ, u) -> begin
(

let _49_1699 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_650 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _150_649 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _150_650 _150_649)))
end else begin
()
end
in (

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (targ))))::subst
in (

let arg = (let _150_651 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inl (targ)), (_150_651)))
in (let _150_656 = (let _150_655 = (let _150_654 = (let _150_653 = (let _150_652 = (FStar_Tc_Util.as_uvar_t u)
in ((_150_652), (u.FStar_Absyn_Syntax.pos)))
in FStar_Util.Inl (_150_653))
in (add_implicit _150_654 g))
in ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (_150_655), (fvs)))
in (tc_args _150_656 rest cres args)))))
end))))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_49_1707))))::rest, ((_49_1715, None))::_49_1713) -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _49_1721 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (

let _49_1725 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_49_1725) with
| (varg, u) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (varg))))::subst
in (

let arg = (let _150_657 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inr (varg)), (_150_657)))
in (tc_args ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), ((add_implicit (FStar_Util.Inr (u)) g)), (fvs)) rest cres args)))
end))))
end
| (((FStar_Util.Inl (a), aqual))::rest, ((FStar_Util.Inl (t), aq))::rest') -> begin
(

let _49_1741 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_659 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _150_658 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _150_659 _150_658)))
end else begin
()
end
in (

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _49_1744 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (

let _49_1750 = (tc_typ_check (

let _49_1746 = env
in {FStar_Tc_Env.solver = _49_1746.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_1746.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_1746.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_1746.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_1746.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_1746.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_1746.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_1746.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_1746.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_1746.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_1746.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_1746.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_1746.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_1746.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_1746.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_1746.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _49_1746.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_1746.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_1746.FStar_Tc_Env.default_effects}) t k)
in (match (_49_1750) with
| (t, g') -> begin
(

let f = (let _150_660 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _150_660))
in (

let g' = (

let _49_1752 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _49_1752.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _49_1752.FStar_Tc_Rel.implicits})
in (

let arg = ((FStar_Util.Inl (t)), (aq))
in (

let subst = (let _150_661 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_661 arg))
in (let _150_663 = (let _150_662 = (FStar_Tc_Rel.conj_guard g g')
in ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (_150_662), (fvs)))
in (tc_args _150_663 rest cres rest'))))))
end)))))
end
| (((FStar_Util.Inr (x), aqual))::rest, ((FStar_Util.Inr (e), aq))::rest') -> begin
(

let _49_1770 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_665 = (FStar_Absyn_Print.subst_to_string subst)
in (let _150_664 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _150_665 _150_664)))
end else begin
()
end
in (

let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _49_1773 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_666 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _150_666))
end else begin
()
end
in (

let _49_1775 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (

let env = (FStar_Tc_Env.set_expected_typ env targ)
in (

let env = (

let _49_1778 = env
in {FStar_Tc_Env.solver = _49_1778.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_1778.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_1778.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_1778.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_1778.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_1778.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_1778.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_1778.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_1778.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_1778.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_1778.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_1778.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_1778.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_1778.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_1778.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_1778.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _49_1778.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_1778.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_1778.FStar_Tc_Env.default_effects})
in (

let _49_1781 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _150_668 = (FStar_Absyn_Print.exp_to_string e)
in (let _150_667 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _150_668 _150_667)))
end else begin
()
end
in (

let _49_1783 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_671 = (FStar_Absyn_Print.tag_of_exp e)
in (let _150_670 = (FStar_Absyn_Print.exp_to_string e)
in (let _150_669 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _150_671 _150_670 _150_669))))
end else begin
()
end
in (

let _49_1788 = (tc_exp env e)
in (match (_49_1788) with
| (e, c, g_e) -> begin
(

let g = (FStar_Tc_Rel.conj_guard g g_e)
in (

let _49_1790 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_673 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _150_672 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _150_673 _150_672)))
end else begin
()
end
in (

let arg = ((FStar_Util.Inr (e)), (aq))
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _150_674 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_674 arg))
in (tc_args ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (g), (fvs)) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(

let subst = (let _150_675 = (FStar_List.hd bs)
in (maybe_extend_subst subst _150_675 arg))
in (

let _49_1797 = (((((Some (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (targ))))), (c)))::comps), (g))
in (match (_49_1797) with
| (comps, guard) -> begin
(tc_args ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (guard), (fvs)) rest cres rest')
end)))
end else begin
if (let _150_676 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _150_676)) then begin
(

let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (

let arg' = (let _150_677 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _150_677))
in (

let binding = FStar_Tc_Env.Binding_var (((newx.FStar_Absyn_Syntax.v), (newx.FStar_Absyn_Syntax.sort)))
in (tc_args ((subst), ((arg)::outargs), ((arg')::arg_rets), ((((Some (binding)), (c)))::comps), (g), (fvs)) rest cres rest'))))
end else begin
(let _150_686 = (let _150_685 = (let _150_679 = (let _150_678 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _150_678))
in (_150_679)::arg_rets)
in (let _150_684 = (let _150_682 = (let _150_681 = (FStar_All.pipe_left (fun _150_680 -> Some (_150_680)) (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (targ)))))
in ((_150_681), (c)))
in (_150_682)::comps)
in (let _150_683 = (FStar_Util.set_add x fvs)
in ((subst), ((arg)::outargs), (_150_685), (_150_684), (g), (_150_683)))))
in (tc_args _150_686 rest cres rest'))
end
end
end)))
end))))))))))
end
| (((FStar_Util.Inr (_49_1804), _49_1807))::_49_1802, ((FStar_Util.Inl (_49_1813), _49_1816))::_49_1811) -> begin
(let _150_690 = (let _150_689 = (let _150_688 = (let _150_687 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _150_687))
in (("Expected an expression; got a type"), (_150_688)))
in FStar_Errors.Error (_150_689))
in (Prims.raise _150_690))
end
| (((FStar_Util.Inl (_49_1823), _49_1826))::_49_1821, ((FStar_Util.Inr (_49_1832), _49_1835))::_49_1830) -> begin
(let _150_694 = (let _150_693 = (let _150_692 = (let _150_691 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _150_691))
in (("Expected a type; got an expression"), (_150_692)))
in FStar_Errors.Error (_150_693))
in (Prims.raise _150_694))
end
| (_49_1840, []) -> begin
(

let _49_1843 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (

let _49_1861 = (match (bs) with
| [] -> begin
(

let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (

let g = (FStar_Tc_Rel.conj_guard g_head g)
in (

let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _49_1851 -> (match (_49_1851) with
| (_49_1849, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _150_696 = (FStar_Absyn_Syntax.mk_Exp_app_flat ((head), ((FStar_List.rev arg_rets))) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _150_696 cres))
end else begin
(

let _49_1853 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_699 = (FStar_Absyn_Print.exp_to_string head)
in (let _150_698 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _150_697 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _150_699 _150_698 _150_697))))
end else begin
()
end
in cres)
end
in (let _150_700 = (FStar_Tc_Util.refresh_comp_label env false cres)
in ((_150_700), (g)))))))
end
| _49_1857 -> begin
(

let g = (let _150_701 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _150_701 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _150_707 = (let _150_706 = (let _150_705 = (let _150_704 = (let _150_703 = (let _150_702 = (cres.FStar_Absyn_Syntax.comp ())
in ((bs), (_150_702)))
in (FStar_Absyn_Syntax.mk_Typ_fun _150_703 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _150_704))
in (FStar_Absyn_Syntax.mk_Total _150_705))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _150_706))
in ((_150_707), (g))))
end)
in (match (_49_1861) with
| (cres, g) -> begin
(

let _49_1862 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_708 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _150_708))
end else begin
()
end
in (

let comp = (FStar_List.fold_left (fun out c -> (FStar_Tc_Util.bind env None (Prims.snd c) (((Prims.fst c)), (out)))) cres comps)
in (

let comp = (FStar_Tc_Util.bind env None chead ((None), (comp)))
in (

let app = (FStar_Absyn_Syntax.mk_Exp_app_flat ((head), ((FStar_List.rev outargs))) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (

let _49_1871 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_49_1871) with
| (comp, g) -> begin
(

let _49_1872 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_714 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _150_713 = (let _150_712 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _150_712))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _150_714 _150_713)))
end else begin
()
end
in ((app), (comp), (g)))
end))))))
end)))
end
| ([], (arg)::_49_1876) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _150_719 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _150_719 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(

let _49_1888 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_720 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _150_720))
end else begin
()
end
in (let _150_721 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args ((subst), (outargs), (arg_rets), ((((None), (cres)))::comps), (g), (fvs)) bs _150_721 args)))
end
| _49_1891 when (not (norm)) -> begin
(let _150_722 = (whnf env tres)
in (aux true _150_722))
end
| _49_1893 -> begin
(let _150_728 = (let _150_727 = (let _150_726 = (let _150_724 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _150_723 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _150_724 _150_723)))
in (let _150_725 = (FStar_Absyn_Syntax.argpos arg)
in ((_150_726), (_150_725))))
in FStar_Errors.Error (_150_727))
in (Prims.raise _150_728))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _150_729 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args (([]), ([]), ([]), ([]), (FStar_Tc_Rel.trivial_guard), (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)) bs _150_729 args))))
end
| _49_1895 -> begin
if (not (norm)) then begin
(let _150_730 = (whnf env tf)
in (check_function_app true _150_730))
end else begin
(let _150_733 = (let _150_732 = (let _150_731 = (FStar_Tc_Errors.expected_function_typ env tf)
in ((_150_731), (head.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_732))
in (Prims.raise _150_733))
end
end))
in (let _150_734 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _150_734)))))
end))
end))
in (

let _49_1899 = (aux ())
in (match (_49_1899) with
| (e, c, g) -> begin
(

let _49_1900 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _150_735 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _150_735))
end else begin
()
end
in (

let c = if (((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) && (not ((FStar_Absyn_Util.is_lcomp_partial_return c)))) && (FStar_Absyn_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_Tc_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _49_1907 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_740 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _150_739 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _150_738 = (let _150_737 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _150_737 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _150_740 _150_739 _150_738))))
end else begin
()
end
in (

let _49_1912 = (comp_check_expected_typ env0 e c)
in (match (_49_1912) with
| (e, c, g') -> begin
(let _150_741 = (FStar_Tc_Rel.conj_guard g g')
in ((e), (c), (_150_741)))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(

let _49_1919 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_49_1919) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _49_1924 = (tc_exp env1 e1)
in (match (_49_1924) with
| (e1, c1, g1) -> begin
(

let _49_1931 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _150_742 = (FStar_Tc_Env.set_expected_typ env res_t)
in ((_150_742), (res_t))))
end)
in (match (_49_1931) with
| (env_branches, res_t) -> begin
(

let guard_x = (let _150_744 = (FStar_All.pipe_left (fun _150_743 -> Some (_150_743)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _150_744))
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (

let _49_1948 = (

let _49_1945 = (FStar_List.fold_right (fun _49_1939 _49_1942 -> (match (((_49_1939), (_49_1942))) with
| ((_49_1935, f, c, g), (caccum, gaccum)) -> begin
(let _150_747 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_150_747)))
end)) t_eqns (([]), (FStar_Tc_Rel.trivial_guard)))
in (match (_49_1945) with
| (cases, g) -> begin
(let _150_748 = (FStar_Tc_Util.bind_cases env res_t cases)
in ((_150_748), (g)))
end))
in (match (_49_1948) with
| (c_branches, g_branches) -> begin
(

let _49_1949 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_752 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _150_751 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _150_750 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _150_749 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _150_752 _150_751 _150_750 _150_749)))))
end else begin
()
end
in (

let cres = (let _150_755 = (let _150_754 = (FStar_All.pipe_left (fun _150_753 -> Some (_150_753)) (FStar_Tc_Env.Binding_var (((guard_x), (c1.FStar_Absyn_Syntax.res_typ)))))
in ((_150_754), (c_branches)))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _150_755))
in (

let e = (let _150_762 = (w cres)
in (let _150_761 = (let _150_760 = (let _150_759 = (FStar_List.map (fun _49_1959 -> (match (_49_1959) with
| (f, _49_1954, _49_1956, _49_1958) -> begin
f
end)) t_eqns)
in ((e1), (_150_759)))
in (FStar_Absyn_Syntax.mk_Exp_match _150_760))
in (FStar_All.pipe_left _150_762 _150_761)))
in (let _150_764 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (cres.FStar_Absyn_Syntax.res_typ), (Some (cres.FStar_Absyn_Syntax.eff_name))) None e.FStar_Absyn_Syntax.pos)
in (let _150_763 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in ((_150_764), (cres), (_150_763)))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _49_1964; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let env = (instantiate_both env)
in (

let env0 = env
in (

let topt = (FStar_Tc_Env.expected_typ env)
in (

let top_level = (match (x) with
| FStar_Util.Inr (_49_1977) -> begin
true
end
| _49_1980 -> begin
false
end)
in (

let _49_1985 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_49_1985) with
| (env1, _49_1984) -> begin
(

let _49_1998 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
((FStar_Tc_Rel.trivial_guard), (env1))
end
| _49_1988 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _150_765 = (FStar_Tc_Env.set_expected_typ env1 t)
in ((FStar_Tc_Rel.trivial_guard), (_150_765)))
end else begin
(

let _49_1991 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_49_1991) with
| (t, f) -> begin
(

let _49_1992 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _150_767 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _150_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _150_767 _150_766)))
end else begin
()
end
in (

let t = (norm_t env1 t)
in (

let env1 = (FStar_Tc_Env.set_expected_typ env1 t)
in ((f), (env1)))))
end))
end
end)
in (match (_49_1998) with
| (f, env1) -> begin
(

let _49_2004 = (tc_exp (

let _49_1999 = env1
in {FStar_Tc_Env.solver = _49_1999.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_1999.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_1999.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_1999.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_1999.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_1999.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_1999.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_1999.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_1999.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_1999.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_1999.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_1999.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_1999.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_1999.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _49_1999.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_1999.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_1999.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_1999.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_1999.FStar_Tc_Env.default_effects}) e1)
in (match (_49_2004) with
| (e1, c1, g1) -> begin
(

let _49_2008 = (let _150_771 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _49_2005 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _150_771 e1 c1 f))
in (match (_49_2008) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_49_2010) -> begin
(

let _49_2024 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(

let _49_2014 = (let _150_772 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _150_772 c1))
in (match (_49_2014) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _49_2015 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _150_773 = (FStar_Tc_Env.get_range env)
in (FStar_Errors.warn _150_773 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _150_774 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e2), (FStar_Absyn_Syntax.Masked_effect)))))
in ((_150_774), (c1))))
end
end))
end else begin
(

let g = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (

let _49_2018 = (FStar_Tc_Util.discharge_guard env g)
in (

let _49_2020 = (FStar_Tc_Util.check_unresolved_implicits g)
in (let _150_775 = (c1.FStar_Absyn_Syntax.comp ())
in ((e2), (_150_775))))))
end
in (match (_49_2024) with
| (e2, c1) -> begin
(

let _49_2029 = if env.FStar_Tc_Env.generalize then begin
(let _150_776 = (FStar_Tc_Util.generalize false env1 ((((x), (e1), (c1)))::[]))
in (FStar_All.pipe_left FStar_List.hd _150_776))
end else begin
((x), (e1), (c1))
end
in (match (_49_2029) with
| (_49_2026, e1, c1) -> begin
(

let cres = (let _150_777 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _150_777))
in (

let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _150_778 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _150_778 ((None), (cres))))
end
in (

let _49_2032 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _150_787 = (let _150_786 = (w cres)
in (let _150_785 = (let _150_784 = (let _150_783 = (let _150_782 = (let _150_781 = (FStar_Absyn_Syntax.mk_lb ((x), ((FStar_Absyn_Util.comp_effect_name c1)), ((FStar_Absyn_Util.comp_result c1)), (e1)))
in (_150_781)::[])
in ((false), (_150_782)))
in ((_150_783), (e2)))
in (FStar_Absyn_Syntax.mk_Exp_let _150_784))
in (FStar_All.pipe_left _150_786 _150_785)))
in ((_150_787), (cres), (FStar_Tc_Rel.trivial_guard))))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(

let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (

let _49_2040 = (let _150_788 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _150_788 e2))
in (match (_49_2040) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 ((Some (b)), (c2)))
in (

let e = (let _150_796 = (w cres)
in (let _150_795 = (let _150_794 = (let _150_793 = (let _150_792 = (let _150_791 = (FStar_Absyn_Syntax.mk_lb ((x), (c1.FStar_Absyn_Syntax.eff_name), (c1.FStar_Absyn_Syntax.res_typ), (e1)))
in (_150_791)::[])
in ((false), (_150_792)))
in ((_150_793), (e2)))
in (FStar_Absyn_Syntax.mk_Exp_let _150_794))
in (FStar_All.pipe_left _150_796 _150_795)))
in (

let g2 = (let _150_805 = (let _150_798 = (let _150_797 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_150_797)::[])
in (FStar_Tc_Rel.close_guard _150_798))
in (let _150_804 = (let _150_803 = (let _150_802 = (let _150_801 = (let _150_800 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _150_800 e1))
in (FStar_All.pipe_left (fun _150_799 -> FStar_Tc_Rel.NonTrivial (_150_799)) _150_801))
in (FStar_Tc_Rel.guard_of_guard_formula _150_802))
in (FStar_Tc_Rel.imp_guard _150_803 g2))
in (FStar_All.pipe_left _150_805 _150_804)))
in (

let guard = (let _150_806 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _150_806))
in (match (topt) with
| None -> begin
(

let tres = cres.FStar_Absyn_Syntax.res_typ
in (

let fvs = (FStar_Absyn_Util.freevars_typ tres)
in if (FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s bvd t) fvs.FStar_Absyn_Syntax.fxvs) then begin
(

let t = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (

let _49_2049 = (let _150_807 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _150_807))
in ((e), (cres), (guard))))
end else begin
((e), (cres), (guard))
end))
end
| _49_2052 -> begin
((e), (cres), (guard))
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _49_2055), _49_2058) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(

let env = (instantiate_both env)
in (

let _49_2070 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_49_2070) with
| (env0, topt) -> begin
(

let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun uu___185 -> (match (uu___185) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_49_2079); FStar_Absyn_Syntax.lbtyp = _49_2077; FStar_Absyn_Syntax.lbeff = _49_2075; FStar_Absyn_Syntax.lbdef = _49_2073} -> begin
true
end
| _49_2083 -> begin
false
end))))
in (

let _49_2108 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _49_2087 _49_2093 -> (match (((_49_2087), (_49_2093))) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _49_2090; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let _49_2098 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_49_2098) with
| (_49_2095, t, check_t) -> begin
(

let e = (FStar_Absyn_Util.unascribe e)
in (

let t = if (not (check_t)) then begin
t
end else begin
(let _150_811 = (tc_typ_check_trivial (

let _49_2100 = env0
in {FStar_Tc_Env.solver = _49_2100.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_2100.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_2100.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_2100.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_2100.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_2100.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_2100.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_2100.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_2100.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_2100.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_2100.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_2100.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_2100.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_2100.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_2100.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _49_2100.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_2100.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_2100.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_2100.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _150_811 (norm_t env)))
end
in (

let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(

let _49_2103 = env
in {FStar_Tc_Env.solver = _49_2103.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_2103.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_2103.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_2103.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_2103.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_2103.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_2103.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_2103.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_2103.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_2103.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_2103.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_2103.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_2103.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = (((x), (t)))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_2103.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_2103.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_2103.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_2103.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_2103.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_2103.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((((x), (t), (e)))::xts), (env)))))
end))
end)) (([]), (env))))
in (match (_49_2108) with
| (lbs, env') -> begin
(

let _49_2123 = (let _150_817 = (let _150_816 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _150_816 (FStar_List.map (fun _49_2112 -> (match (_49_2112) with
| (x, t, e) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (

let _49_2114 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_815 = (FStar_Absyn_Print.lbname_to_string x)
in (let _150_814 = (FStar_Absyn_Print.exp_to_string e)
in (let _150_813 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _150_815 _150_814 _150_813))))
end else begin
()
end
in (

let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (

let _49_2120 = (tc_total_exp env' e)
in (match (_49_2120) with
| (e, t, g) -> begin
((((x), (t), (e))), (g))
end)))))
end)))))
in (FStar_All.pipe_right _150_817 FStar_List.unzip))
in (match (_49_2123) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (

let _49_2142 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _150_819 = (FStar_List.map (fun _49_2128 -> (match (_49_2128) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb ((x), (FStar_Absyn_Const.effect_Tot_lid), (t), (e)))
end)) lbs)
in ((_150_819), (g_lbs)))
end else begin
(

let _49_2129 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (

let ecs = (let _150_822 = (FStar_All.pipe_right lbs (FStar_List.map (fun _49_2134 -> (match (_49_2134) with
| (x, t, e) -> begin
(let _150_821 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb ((x), (t), (e))))
in ((x), (e), (_150_821)))
end))))
in (FStar_Tc_Util.generalize true env _150_822))
in (let _150_824 = (FStar_List.map (fun _49_2139 -> (match (_49_2139) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb ((x), (FStar_Absyn_Const.effect_Tot_lid), ((FStar_Absyn_Util.comp_result c)), (e)))
end)) ecs)
in ((_150_824), (FStar_Tc_Rel.trivial_guard)))))
end
in (match (_49_2142) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(

let cres = (let _150_825 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _150_825))
in (

let _49_2144 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (

let _49_2146 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _150_829 = (let _150_828 = (w cres)
in (FStar_All.pipe_left _150_828 (FStar_Absyn_Syntax.mk_Exp_let ((((true), (lbs))), (e1)))))
in ((_150_829), (cres), (FStar_Tc_Rel.trivial_guard))))))
end else begin
(

let _49_2162 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _49_2150 _49_2157 -> (match (((_49_2150), (_49_2157))) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _49_2154; FStar_Absyn_Syntax.lbdef = _49_2152}) -> begin
(

let b = (binding_of_lb x t)
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (((b)::bindings), (env))))
end)) (([]), (env))))
in (match (_49_2162) with
| (bindings, env) -> begin
(

let _49_2166 = (tc_exp env e1)
in (match (_49_2166) with
| (e1, cres, g1) -> begin
(

let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (

let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (

let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (

let cres = (

let _49_2170 = cres
in {FStar_Absyn_Syntax.eff_name = _49_2170.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _49_2170.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _49_2170.FStar_Absyn_Syntax.comp})
in (

let e = (let _150_834 = (w cres)
in (FStar_All.pipe_left _150_834 (FStar_Absyn_Syntax.mk_Exp_let ((((true), (lbs))), (e1)))))
in (match (topt) with
| Some (_49_2175) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun uu___186 -> (match (uu___186) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_49_2187); FStar_Absyn_Syntax.lbtyp = _49_2185; FStar_Absyn_Syntax.lbeff = _49_2183; FStar_Absyn_Syntax.lbdef = _49_2181} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _49_2195; FStar_Absyn_Syntax.lbeff = _49_2193; FStar_Absyn_Syntax.lbdef = _49_2191} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _49_2204; FStar_Absyn_Syntax.lbeff = _49_2202; FStar_Absyn_Syntax.lbdef = _49_2200}) -> begin
(

let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (

let _49_2210 = (let _150_836 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _150_836))
in ((e), (cres), (guard))))
end
| _49_2213 -> begin
((e), (cres), (guard))
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
and tc_eqn : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp)  ->  ((FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun scrutinee_x pat_t env _49_2220 -> (match (_49_2220) with
| (pattern, when_clause, branch) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _49_2228 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_49_2228) with
| (bindings, exps, p) -> begin
(

let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (

let _49_2237 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun uu___187 -> (match (uu___187) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _150_849 = (FStar_Absyn_Print.strBvd x)
in (let _150_848 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _150_849 _150_848)))
end
| _49_2236 -> begin
()
end))))
end else begin
()
end
in (

let _49_2242 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_49_2242) with
| (env1, _49_2241) -> begin
(

let env1 = (

let _49_2243 = env1
in {FStar_Tc_Env.solver = _49_2243.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_2243.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_2243.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_2243.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_2243.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_2243.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_2243.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_2243.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _49_2243.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_2243.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_2243.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_2243.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_2243.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_2243.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_2243.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_2243.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_2243.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_2243.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_2243.FStar_Tc_Env.default_effects})
in (

let expected_pat_t = (let _150_850 = (FStar_Tc_Rel.unrefine env pat_t)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env _150_850))
in (

let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _49_2248 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_853 = (FStar_Absyn_Print.exp_to_string e)
in (let _150_852 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _150_853 _150_852)))
end else begin
()
end
in (

let _49_2253 = (tc_exp env1 e)
in (match (_49_2253) with
| (e, lc, g) -> begin
(

let _49_2254 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_855 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _150_854 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _150_855 _150_854)))
end else begin
()
end
in (

let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_Tc_Rel.conj_guard g g')
in (

let _49_2258 = (let _150_856 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _150_856))
in (

let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (

let _49_2261 = if (let _150_859 = (let _150_858 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _150_857 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _150_858 _150_857)))
in (FStar_All.pipe_left Prims.op_Negation _150_859)) then begin
(let _150_864 = (let _150_863 = (let _150_862 = (let _150_861 = (FStar_Absyn_Print.exp_to_string e')
in (let _150_860 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _150_861 _150_860)))
in ((_150_862), (p.FStar_Absyn_Syntax.p)))
in FStar_Errors.Error (_150_863))
in (Prims.raise _150_864))
end else begin
()
end
in e))))))
end))))))
in (

let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (

let _49_2272 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun uu___188 -> (match (uu___188) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _150_867 = (FStar_Absyn_Print.strBvd x)
in (let _150_866 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _150_867 _150_866)))
end
| _49_2271 -> begin
()
end))))
end else begin
()
end
in ((p), (bindings), (pat_env), (exps), (FStar_Tc_Rel.trivial_guard)))))))
end))))
end)))
in (

let _49_2279 = (tc_pat true pat_t pattern)
in (match (_49_2279) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(

let _49_2289 = (match (when_clause) with
| None -> begin
((None), (FStar_Tc_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Errors.Error ((("When clauses are not yet supported in --verify mode; they soon will be"), (e.FStar_Absyn_Syntax.pos)))))
end else begin
(

let _49_2286 = (let _150_868 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _150_868 e))
in (match (_49_2286) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_49_2289) with
| (when_clause, g_when) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_870 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _150_869 -> Some (_150_869)) _150_870))
end)
in (

let _49_2297 = (tc_exp pat_env branch)
in (match (_49_2297) with
| (branch, c, g_branch) -> begin
(

let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (

let _49_2302 = (let _150_871 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var (((scrutinee_x), (pat_t)))))
in (FStar_All.pipe_right _150_871 FStar_Tc_Env.clear_expected_typ))
in (match (_49_2302) with
| (scrutinee_env, _49_2301) -> begin
(

let c = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _49_2316 -> begin
(

let clause = (let _150_875 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _150_874 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _150_875 _150_874 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _150_877 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _150_876 -> Some (_150_876)) _150_877))
end))
end))) None))
in (

let c = (match (((eqs), (when_condition))) with
| (None, None) -> begin
c
end
| (Some (f), None) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (f)))
end
| (Some (f), Some (w)) -> begin
(let _150_880 = (let _150_879 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _150_878 -> FStar_Tc_Rel.NonTrivial (_150_878)) _150_879))
in (FStar_Tc_Util.weaken_precondition env c _150_880))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (

let discriminate = (fun scrutinee f -> (

let disc = (let _150_886 = (let _150_885 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _150_885))
in (FStar_All.pipe_left _150_886 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (

let disc = (let _150_889 = (let _150_888 = (let _150_887 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_150_887)::[])
in ((disc), (_150_888)))
in (FStar_Absyn_Syntax.mk_Exp_app _150_889 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (

let rec mk_guard = (fun scrutinee pat_exp -> (

let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_49_2374) -> begin
(let _150_898 = (let _150_897 = (let _150_896 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _150_895 = (let _150_894 = (FStar_Absyn_Syntax.varg pat_exp)
in (_150_894)::[])
in (_150_896)::_150_895))
in ((FStar_Absyn_Util.teq), (_150_897)))
in (FStar_Absyn_Syntax.mk_Typ_app _150_898 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _49_2378) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _49_2391); FStar_Absyn_Syntax.tk = _49_2388; FStar_Absyn_Syntax.pos = _49_2386; FStar_Absyn_Syntax.fvs = _49_2384; FStar_Absyn_Syntax.uvs = _49_2382}, args) -> begin
(

let head = (discriminate scrutinee f)
in (

let sub_term_guards = (let _150_907 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_49_2402) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(

let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in if (let _150_901 = (FStar_Tc_Env.is_projector env projector)
in (FStar_All.pipe_left Prims.op_Negation _150_901)) then begin
[]
end else begin
(

let sub_term = (let _150_905 = (let _150_904 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _150_903 = (let _150_902 = (FStar_Absyn_Syntax.varg scrutinee)
in (_150_902)::[])
in ((_150_904), (_150_903))))
in (FStar_Absyn_Syntax.mk_Exp_app _150_905 None f.FStar_Absyn_Syntax.p))
in (let _150_906 = (mk_guard sub_term ei)
in (_150_906)::[]))
end)
end))))
in (FStar_All.pipe_right _150_907 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _49_2410 -> begin
(let _150_910 = (let _150_909 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _150_908 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _150_909 _150_908)))
in (failwith _150_910))
end)))
in (

let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(

let t = (mk_guard s pat)
in (

let _49_2419 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_49_2419) with
| (t, _49_2418) -> begin
t
end)))
end)
in (

let path_guard = (let _150_919 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _150_918 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _150_918)))))
in (FStar_All.pipe_right _150_919 FStar_Absyn_Util.mk_disj_l))
in (

let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (

let guard = (let _150_920 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _150_920))
in (

let _49_2427 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _150_921 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _150_921))
end else begin
()
end
in (let _150_923 = (let _150_922 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _150_922))
in ((((pattern), (when_clause), (branch))), (path_guard), (c), (_150_923)))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let _49_2433 = (tc_kind env k)
in (match (_49_2433) with
| (k, g) -> begin
(

let _49_2434 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd) = (fun env t -> (

let _49_2441 = (tc_typ env t)
in (match (_49_2441) with
| (t, k, g) -> begin
(

let _49_2442 = (FStar_Tc_Util.discharge_guard env g)
in ((t), (k)))
end)))
and tc_typ_check_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env t k -> (

let _49_2449 = (tc_typ_check env t k)
in (match (_49_2449) with
| (t, f) -> begin
(

let _49_2450 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (

let _49_2457 = (tc_exp env e)
in (match (_49_2457) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
((e), (c.FStar_Absyn_Syntax.res_typ), (g))
end else begin
(

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (

let c = (let _150_933 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _150_933 (norm_c env)))
in (match ((let _150_935 = (let _150_934 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _150_934))
in (FStar_Tc_Rel.sub_comp env c _150_935))) with
| Some (g') -> begin
(let _150_936 = (FStar_Tc_Rel.conj_guard g g')
in ((e), ((FStar_Absyn_Util.comp_result c)), (_150_936)))
end
| _49_2463 -> begin
(let _150_939 = (let _150_938 = (let _150_937 = (FStar_Tc_Errors.expected_pure_expression e c)
in ((_150_937), (e.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_938))
in (Prims.raise _150_939))
end)))
end
end)))
and tc_ghost_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (

let _49_2469 = (tc_exp env e)
in (match (_49_2469) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
((e), (c.FStar_Absyn_Syntax.res_typ), (g))
end else begin
(

let c = (let _150_942 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _150_942 (norm_c env)))
in (

let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (

let _49_2473 = env
in {FStar_Tc_Env.solver = _49_2473.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_2473.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_2473.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_2473.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_2473.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_2473.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_2473.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_2473.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_2473.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_2473.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_2473.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_2473.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_2473.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_2473.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_2473.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_2473.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _49_2473.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_2473.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_2473.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _150_943 = (FStar_Tc_Rel.conj_guard g g')
in ((e), ((FStar_Absyn_Util.comp_result c)), (_150_943)))
end
| _49_2478 -> begin
(let _150_946 = (let _150_945 = (let _150_944 = (FStar_Tc_Errors.expected_ghost_expression e c)
in ((_150_944), (e.FStar_Absyn_Syntax.pos)))
in FStar_Errors.Error (_150_945))
in (Prims.raise _150_946))
end))))
end
end)))


let tc_tparams : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env) = (fun env tps -> (

let _49_2484 = (tc_binders env tps)
in (match (_49_2484) with
| (tps, env, g) -> begin
(

let _49_2485 = (FStar_Tc_Util.force_trivial env g)
in ((tps), (env)))
end)))


let a_kwp_a : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (((FStar_Util.Inl (a), _49_2504))::((FStar_Util.Inl (wp), _49_2499))::((FStar_Util.Inl (_49_2491), _49_2494))::[], _49_2508) -> begin
((a), (wp.FStar_Absyn_Syntax.sort))
end
| _49_2512 -> begin
(let _150_959 = (let _150_958 = (let _150_957 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in ((_150_957), ((FStar_Ident.range_of_lid m))))
in FStar_Errors.Error (_150_958))
in (Prims.raise _150_959))
end))


let rec tc_eff_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.eff_decl = (fun env m -> (

let _49_2518 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_49_2518) with
| (binders, env, g) -> begin
(

let _49_2519 = (FStar_Tc_Util.discharge_guard env g)
in (

let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (

let _49_2524 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_49_2524) with
| (a, kwp_a) -> begin
(

let a_typ = (FStar_Absyn_Util.btvar_to_typ a)
in (

let b = (FStar_Absyn_Util.gen_bvar_p (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname) FStar_Absyn_Syntax.ktype)
in (

let b_typ = (FStar_Absyn_Util.btvar_to_typ b)
in (

let kwp_b = (FStar_Absyn_Util.subst_kind ((FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (b_typ))))::[]) kwp_a)
in (

let kwlp_a = kwp_a
in (

let kwlp_b = kwp_b
in (

let a_kwp_b = (let _150_972 = (let _150_971 = (let _150_970 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_150_970)::[])
in ((_150_971), (kwp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_972 a_typ.FStar_Absyn_Syntax.pos))
in (

let a_kwlp_b = a_kwp_b
in (

let w = (fun k -> (k (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname)))
in (

let ret = (

let expected_k = (let _150_986 = (let _150_985 = (let _150_984 = (let _150_983 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_982 = (let _150_981 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_150_981)::[])
in (_150_983)::_150_982))
in ((_150_984), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_985))
in (FStar_All.pipe_left w _150_986))
in (let _150_987 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _150_987 (norm_t env))))
in (

let bind_wp = (

let expected_k = (let _150_1002 = (let _150_1001 = (let _150_1000 = (let _150_999 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_998 = (let _150_997 = (FStar_Absyn_Syntax.t_binder b)
in (let _150_996 = (let _150_995 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _150_994 = (let _150_993 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _150_992 = (let _150_991 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _150_990 = (let _150_989 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_150_989)::[])
in (_150_991)::_150_990))
in (_150_993)::_150_992))
in (_150_995)::_150_994))
in (_150_997)::_150_996))
in (_150_999)::_150_998))
in ((_150_1000), (kwp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1001))
in (FStar_All.pipe_left w _150_1002))
in (let _150_1003 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _150_1003 (norm_t env))))
in (

let bind_wlp = (

let expected_k = (let _150_1014 = (let _150_1013 = (let _150_1012 = (let _150_1011 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1010 = (let _150_1009 = (FStar_Absyn_Syntax.t_binder b)
in (let _150_1008 = (let _150_1007 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _150_1006 = (let _150_1005 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_150_1005)::[])
in (_150_1007)::_150_1006))
in (_150_1009)::_150_1008))
in (_150_1011)::_150_1010))
in ((_150_1012), (kwlp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1013))
in (FStar_All.pipe_left w _150_1014))
in (let _150_1015 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _150_1015 (norm_t env))))
in (

let if_then_else = (

let expected_k = (let _150_1026 = (let _150_1025 = (let _150_1024 = (let _150_1023 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1022 = (let _150_1021 = (FStar_Absyn_Syntax.t_binder b)
in (let _150_1020 = (let _150_1019 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _150_1018 = (let _150_1017 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_150_1017)::[])
in (_150_1019)::_150_1018))
in (_150_1021)::_150_1020))
in (_150_1023)::_150_1022))
in ((_150_1024), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1025))
in (FStar_All.pipe_left w _150_1026))
in (let _150_1027 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _150_1027 (norm_t env))))
in (

let ite_wp = (

let expected_k = (let _150_1036 = (let _150_1035 = (let _150_1034 = (let _150_1033 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1032 = (let _150_1031 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _150_1030 = (let _150_1029 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_150_1029)::[])
in (_150_1031)::_150_1030))
in (_150_1033)::_150_1032))
in ((_150_1034), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1035))
in (FStar_All.pipe_left w _150_1036))
in (let _150_1037 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _150_1037 (norm_t env))))
in (

let ite_wlp = (

let expected_k = (let _150_1044 = (let _150_1043 = (let _150_1042 = (let _150_1041 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1040 = (let _150_1039 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_150_1039)::[])
in (_150_1041)::_150_1040))
in ((_150_1042), (kwlp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1043))
in (FStar_All.pipe_left w _150_1044))
in (let _150_1045 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _150_1045 (norm_t env))))
in (

let wp_binop = (

let expected_k = (let _150_1057 = (let _150_1056 = (let _150_1055 = (let _150_1054 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1053 = (let _150_1052 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _150_1051 = (let _150_1050 = (let _150_1047 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _150_1047))
in (let _150_1049 = (let _150_1048 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_150_1048)::[])
in (_150_1050)::_150_1049))
in (_150_1052)::_150_1051))
in (_150_1054)::_150_1053))
in ((_150_1055), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1056))
in (FStar_All.pipe_left w _150_1057))
in (let _150_1058 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _150_1058 (norm_t env))))
in (

let wp_as_type = (

let expected_k = (let _150_1065 = (let _150_1064 = (let _150_1063 = (let _150_1062 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1061 = (let _150_1060 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_150_1060)::[])
in (_150_1062)::_150_1061))
in ((_150_1063), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1064))
in (FStar_All.pipe_left w _150_1065))
in (let _150_1066 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _150_1066 (norm_t env))))
in (

let close_wp = (

let expected_k = (let _150_1075 = (let _150_1074 = (let _150_1073 = (let _150_1072 = (FStar_Absyn_Syntax.t_binder b)
in (let _150_1071 = (let _150_1070 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1069 = (let _150_1068 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_150_1068)::[])
in (_150_1070)::_150_1069))
in (_150_1072)::_150_1071))
in ((_150_1073), (kwp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1074))
in (FStar_All.pipe_left w _150_1075))
in (let _150_1076 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _150_1076 (norm_t env))))
in (

let close_wp_t = (

let expected_k = (let _150_1089 = (let _150_1088 = (let _150_1087 = (let _150_1086 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1085 = (let _150_1084 = (let _150_1083 = (let _150_1082 = (let _150_1081 = (let _150_1080 = (let _150_1079 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_150_1079)::[])
in ((_150_1080), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1081))
in (FStar_All.pipe_left w _150_1082))
in (FStar_Absyn_Syntax.null_t_binder _150_1083))
in (_150_1084)::[])
in (_150_1086)::_150_1085))
in ((_150_1087), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1088))
in (FStar_All.pipe_left w _150_1089))
in (let _150_1090 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _150_1090 (norm_t env))))
in (

let _49_2558 = (

let expected_k = (let _150_1099 = (let _150_1098 = (let _150_1097 = (let _150_1096 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1095 = (let _150_1094 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _150_1093 = (let _150_1092 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_150_1092)::[])
in (_150_1094)::_150_1093))
in (_150_1096)::_150_1095))
in ((_150_1097), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1098))
in (FStar_All.pipe_left w _150_1099))
in (let _150_1103 = (let _150_1100 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _150_1100 (norm_t env)))
in (let _150_1102 = (let _150_1101 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _150_1101 (norm_t env)))
in ((_150_1103), (_150_1102)))))
in (match (_49_2558) with
| (assert_p, assume_p) -> begin
(

let null_wp = (

let expected_k = (let _150_1108 = (let _150_1107 = (let _150_1106 = (let _150_1105 = (FStar_Absyn_Syntax.t_binder a)
in (_150_1105)::[])
in ((_150_1106), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1107))
in (FStar_All.pipe_left w _150_1108))
in (let _150_1109 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _150_1109 (norm_t env))))
in (

let trivial_wp = (

let expected_k = (let _150_1116 = (let _150_1115 = (let _150_1114 = (let _150_1113 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1112 = (let _150_1111 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_150_1111)::[])
in (_150_1113)::_150_1112))
in ((_150_1114), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1115))
in (FStar_All.pipe_left w _150_1116))
in (let _150_1117 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _150_1117 (norm_t env))))
in {FStar_Absyn_Syntax.mname = m.FStar_Absyn_Syntax.mname; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = m.FStar_Absyn_Syntax.qualifiers; FStar_Absyn_Syntax.signature = mk; FStar_Absyn_Syntax.ret = ret; FStar_Absyn_Syntax.bind_wp = bind_wp; FStar_Absyn_Syntax.bind_wlp = bind_wlp; FStar_Absyn_Syntax.if_then_else = if_then_else; FStar_Absyn_Syntax.ite_wp = ite_wp; FStar_Absyn_Syntax.ite_wlp = ite_wlp; FStar_Absyn_Syntax.wp_binop = wp_binop; FStar_Absyn_Syntax.wp_as_type = wp_as_type; FStar_Absyn_Syntax.close_wp = close_wp; FStar_Absyn_Syntax.close_wp_t = close_wp_t; FStar_Absyn_Syntax.assert_p = assert_p; FStar_Absyn_Syntax.assume_p = assume_p; FStar_Absyn_Syntax.null_wp = null_wp; FStar_Absyn_Syntax.trivial = trivial_wp}))
end)))))))))))))))))))))
end))))
end)))
and tc_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.bool  ->  (FStar_Absyn_Syntax.sigelt * FStar_Tc_Env.env) = (fun env se deserialized -> (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Absyn_Syntax.SetOptions (o) -> begin
(

let _49_2579 = (set_options FStar_Options.Set o)
in ((se), (env)))
end
| FStar_Absyn_Syntax.ResetOptions (sopt) -> begin
(

let _49_2583 = (let _150_1125 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _150_1125 Prims.ignore))
in (

let _49_2588 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _49_2590 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in ((se), (env)))))
end))
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env)))))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, r) -> begin
(

let _49_2605 = (let _150_1126 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _150_1126))
in (match (_49_2605) with
| (a, kwp_a_src) -> begin
(

let _49_2608 = (let _150_1127 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _150_1127))
in (match (_49_2608) with
| (b, kwp_b_tgt) -> begin
(

let kwp_a_tgt = (let _150_1131 = (let _150_1130 = (let _150_1129 = (let _150_1128 = (FStar_Absyn_Util.btvar_to_typ a)
in ((b.FStar_Absyn_Syntax.v), (_150_1128)))
in FStar_Util.Inl (_150_1129))
in (_150_1130)::[])
in (FStar_Absyn_Util.subst_kind _150_1131 kwp_b_tgt))
in (

let expected_k = (let _150_1137 = (let _150_1136 = (let _150_1135 = (let _150_1134 = (FStar_Absyn_Syntax.t_binder a)
in (let _150_1133 = (let _150_1132 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_150_1132)::[])
in (_150_1134)::_150_1133))
in ((_150_1135), (kwp_a_tgt)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _150_1136))
in (FStar_All.pipe_right r _150_1137))
in (

let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (

let sub = (

let _49_2612 = sub
in {FStar_Absyn_Syntax.source = _49_2612.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _49_2612.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
in (

let se = FStar_Absyn_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env))))))))
end))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _mutuals, _data, tags, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_2629 = (tc_tparams env tps)
in (match (_49_2629) with
| (tps, env) -> begin
(

let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _49_2632 -> begin
(tc_kind_trivial env k)
end)
in (

let _49_2634 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _150_1140 = (FStar_Absyn_Print.sli lid)
in (let _150_1139 = (let _150_1138 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _150_1138))
in (FStar_Util.print2 "Checked %s at kind %s\n" _150_1140 _150_1139)))
end else begin
()
end
in (

let k = (norm_k env k)
in (

let se = FStar_Absyn_Syntax.Sig_tycon (((lid), (tps), (k), (_mutuals), (_data), (tags), (r)))
in (

let _49_2652 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_49_2647); FStar_Absyn_Syntax.tk = _49_2645; FStar_Absyn_Syntax.pos = _49_2643; FStar_Absyn_Syntax.fvs = _49_2641; FStar_Absyn_Syntax.uvs = _49_2639} -> begin
(let _150_1141 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _150_1141))
end
| _49_2651 -> begin
()
end)
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env))))))))
end)))
end
| FStar_Absyn_Syntax.Sig_kind_abbrev (lid, tps, k, r) -> begin
(

let env0 = env
in (

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_2665 = (tc_tparams env tps)
in (match (_49_2665) with
| (tps, env) -> begin
(

let k = (tc_kind_trivial env k)
in (

let se = FStar_Absyn_Syntax.Sig_kind_abbrev (((lid), (tps), (k), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env0 se)
in ((se), (env)))))
end))))
end
| FStar_Absyn_Syntax.Sig_effect_abbrev (lid, tps, c, tags, r) -> begin
(

let env0 = env
in (

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_2680 = (tc_tparams env tps)
in (match (_49_2680) with
| (tps, env) -> begin
(

let _49_2683 = (tc_comp env c)
in (match (_49_2683) with
| (c, g) -> begin
(

let tags = (FStar_All.pipe_right tags (FStar_List.map (fun uu___189 -> (match (uu___189) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(

let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _150_1144 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _150_1143 -> Some (_150_1143)))
in FStar_Absyn_Syntax.DefaultEffect (_150_1144)))
end
| t -> begin
t
end))))
in (

let se = FStar_Absyn_Syntax.Sig_effect_abbrev (((lid), (tps), (c), (tags), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env0 se)
in ((se), (env)))))
end))
end))))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, tags, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_2703 = (tc_tparams env tps)
in (match (_49_2703) with
| (tps, env') -> begin
(

let _49_2709 = (let _150_1148 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _150_1148 (fun _49_2706 -> (match (_49_2706) with
| (t, k) -> begin
(let _150_1147 = (norm_t env' t)
in (let _150_1146 = (norm_k env' k)
in ((_150_1147), (_150_1146))))
end))))
in (match (_49_2709) with
| (t, k1) -> begin
(

let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _49_2712 -> begin
(

let k2 = (let _150_1149 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _150_1149 (norm_k env)))
in (

let _49_2714 = (let _150_1150 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _150_1150))
in k2))
end)
in (

let se = FStar_Absyn_Syntax.Sig_typ_abbrev (((lid), (tps), (k2), (t), (tags), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env)))))
end))
end)))
end
| FStar_Absyn_Syntax.Sig_datacon (lid, t, (tname, tps, k), quals, mutuals, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_2734 = (tc_binders env tps)
in (match (_49_2734) with
| (tps, env, g) -> begin
(

let tycon = ((tname), (tps), (k))
in (

let _49_2736 = (FStar_Tc_Util.discharge_guard env g)
in (

let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (

let t = (norm_t env t)
in (

let _49_2748 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
((formals), ((FStar_Absyn_Util.comp_result cod)))
end
| _49_2745 -> begin
(([]), (t))
end)
in (match (_49_2748) with
| (formals, result_t) -> begin
(

let cardinality_and_positivity_check = (fun formal -> (

let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _49_2756 -> (match (_49_2756) with
| (a, _49_2755) -> begin
(match (a) with
| FStar_Util.Inl (_49_2758) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(

let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _150_1158 = (FStar_Absyn_Util.compress_typ t)
in _150_1158.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _150_1162 = (let _150_1161 = (let _150_1160 = (let _150_1159 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _150_1159 tname))
in ((_150_1160), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_150_1161))
in (Prims.raise _150_1162))
end)
end
| _49_2771 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(

let _49_2774 = if (FStar_Options.warn_cardinality ()) then begin
(let _150_1163 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Errors.warn r _150_1163))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _150_1166 = (let _150_1165 = (let _150_1164 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in ((_150_1164), (r)))
in FStar_Errors.Error (_150_1165))
in (Prims.raise _150_1166))
end else begin
()
end
end
in (

let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_49_2778) -> begin
(

let _49_2783 = (FStar_Absyn_Util.kind_formals k)
in (match (_49_2783) with
| (formals, _49_2782) -> begin
(check_positivity formals)
end))
end
| _49_2785 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(

let _49_2792 = (let _150_1167 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _150_1167 FStar_Util.must))
in (match (_49_2792) with
| (formals, _49_2791) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (

let _49_2793 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (

let _49_2847 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _150_1171 = (let _150_1170 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _150_1170 Prims.fst))
in (FStar_List.forall2 (fun _49_2800 _49_2804 -> (match (((_49_2800), (_49_2804))) with
| ((a, _49_2799), (b, _49_2803)) -> begin
(match (((a), (b))) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _49_2812; FStar_Absyn_Syntax.pos = _49_2810; FStar_Absyn_Syntax.fvs = _49_2808; FStar_Absyn_Syntax.uvs = _49_2806}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _49_2827; FStar_Absyn_Syntax.pos = _49_2825; FStar_Absyn_Syntax.fvs = _49_2823; FStar_Absyn_Syntax.uvs = _49_2821}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _49_2836 -> begin
false
end)
end)) _150_1171 tps))))) then begin
(

let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _49_2839 -> begin
(

let _49_2843 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_49_2843) with
| (_49_2841, expected_args) -> begin
(let _150_1172 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _150_1172 expected_args))
end))
end)
in (let _150_1176 = (let _150_1175 = (let _150_1174 = (let _150_1173 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _150_1173 result_t expected_t))
in ((_150_1174), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_150_1175))
in (Prims.raise _150_1176)))
end else begin
()
end
end
| _49_2846 -> begin
(let _150_1181 = (let _150_1180 = (let _150_1179 = (let _150_1178 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _150_1177 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _150_1178 result_t _150_1177)))
in ((_150_1179), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_150_1180))
in (Prims.raise _150_1181))
end)
in (

let se = FStar_Absyn_Syntax.Sig_datacon (((lid), (t), (tycon), (quals), (mutuals), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in (

let _49_2851 = if (log env) then begin
(let _150_1183 = (let _150_1182 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _150_1182))
in (FStar_All.pipe_left FStar_Util.print_string _150_1183))
end else begin
()
end
in ((se), (env))))))))
end))))))
end)))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let t = (let _150_1184 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _150_1184 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (

let _49_2861 = (FStar_Tc_Util.check_uvars r t)
in (

let se = FStar_Absyn_Syntax.Sig_val_decl (((lid), (t), (quals), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in (

let _49_2865 = if (log env) then begin
(let _150_1186 = (let _150_1185 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _150_1185))
in (FStar_All.pipe_left FStar_Util.print_string _150_1186))
end else begin
()
end
in ((se), (env))))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let phi = (let _150_1187 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _150_1187 (norm_t env)))
in (

let _49_2875 = (FStar_Tc_Util.check_uvars r phi)
in (

let se = FStar_Absyn_Syntax.Sig_assume (((lid), (phi), (quals), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env)))))))
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_2928 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _49_2888 lb -> (match (_49_2888) with
| (gen, lbs) -> begin
(

let _49_2925 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_49_2897); FStar_Absyn_Syntax.lbtyp = _49_2895; FStar_Absyn_Syntax.lbeff = _49_2893; FStar_Absyn_Syntax.lbdef = _49_2891} -> begin
(failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _49_2902; FStar_Absyn_Syntax.lbdef = e} -> begin
(

let _49_2922 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
((gen), (lb))
end
| Some (t', _49_2910) -> begin
(

let _49_2913 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _150_1190 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _150_1190 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _150_1191 = (FStar_Absyn_Syntax.mk_lb ((FStar_Util.Inr (l)), (FStar_Absyn_Const.effect_ALL_lid), (t'), (e)))
in ((false), (_150_1191)))
end
| _49_2917 -> begin
(

let _49_2918 = if (not (deserialized)) then begin
(let _150_1193 = (let _150_1192 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _150_1192))
in (FStar_All.pipe_left FStar_Util.print_string _150_1193))
end else begin
()
end
in (let _150_1194 = (FStar_Absyn_Syntax.mk_lb ((FStar_Util.Inr (l)), (FStar_Absyn_Const.effect_ALL_lid), (t'), (e)))
in ((false), (_150_1194))))
end))
end)
in (match (_49_2922) with
| (gen, lb) -> begin
((gen), (lb))
end))
end)
in (match (_49_2925) with
| (gen, lb) -> begin
((gen), ((lb)::lbs))
end))
end)) ((true), ([]))))
in (match (_49_2928) with
| (generalize, lbs') -> begin
(

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _150_1199 = (let _150_1198 = (let _150_1197 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _150_1197 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((((Prims.fst lbs)), (lbs'))), (_150_1198)))
in (FStar_Absyn_Syntax.mk_Exp_let _150_1199 None r))
in (

let _49_2963 = (match ((tc_exp (

let _49_2931 = env
in {FStar_Tc_Env.solver = _49_2931.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_2931.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_2931.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_2931.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_2931.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_2931.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_2931.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_2931.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_2931.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_2931.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_2931.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_2931.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _49_2931.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_2931.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_2931.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_2931.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _49_2931.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _49_2931.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _49_2931.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _49_2940; FStar_Absyn_Syntax.pos = _49_2938; FStar_Absyn_Syntax.fvs = _49_2936; FStar_Absyn_Syntax.uvs = _49_2934}, _49_2947, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_49_2951, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _49_2957 -> begin
quals
end)
in ((FStar_Absyn_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _49_2960 -> begin
(failwith "impossible")
end)
in (match (_49_2963) with
| (se, lbs) -> begin
(

let _49_2969 = if (log env) then begin
(let _150_1205 = (let _150_1204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _150_1201 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _150_1201))) with
| None -> begin
true
end
| _49_2967 -> begin
false
end)
in if should_log then begin
(let _150_1203 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _150_1202 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _150_1203 _150_1202)))
end else begin
""
end))))
in (FStar_All.pipe_right _150_1204 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _150_1205))
end else begin
()
end
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env))))
end))))
end)))
end
| FStar_Absyn_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let env = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (

let _49_2981 = (tc_exp env e)
in (match (_49_2981) with
| (e, c, g1) -> begin
(

let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (

let _49_2987 = (let _150_1209 = (let _150_1206 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_150_1206))
in (let _150_1208 = (let _150_1207 = (c.FStar_Absyn_Syntax.comp ())
in ((e), (_150_1207)))
in (check_expected_effect env _150_1209 _150_1208)))
in (match (_49_2987) with
| (e, _49_2985, g) -> begin
(

let _49_2988 = (let _150_1210 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _150_1210))
in (

let se = FStar_Absyn_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env)))))
end)))
end))))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let _49_3007 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___190 -> (match (uu___190) with
| FStar_Absyn_Syntax.Sig_tycon (_49_3001) -> begin
true
end
| _49_3004 -> begin
false
end))))
in (match (_49_3007) with
| (tycons, rest) -> begin
(

let _49_3016 = (FStar_All.pipe_right rest (FStar_List.partition (fun uu___191 -> (match (uu___191) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_49_3010) -> begin
true
end
| _49_3013 -> begin
false
end))))
in (match (_49_3016) with
| (abbrevs, rest) -> begin
(

let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun uu___192 -> (match (uu___192) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(

let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _150_1214 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _150_1214 Prims.fst))
end
| _49_3028 -> begin
k
end)
in ((FStar_Absyn_Syntax.Sig_tycon (((lid), (tps), (k), ([]), ([]), ([]), (r)))), (t)))
end
| _49_3031 -> begin
(failwith "impossible")
end))))
in (

let _49_3035 = (FStar_List.split recs)
in (match (_49_3035) with
| (recs, abbrev_defs) -> begin
(

let msg = if (FStar_Options.log_queries ()) then begin
(let _150_1215 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _150_1215))
end else begin
""
end
in (

let _49_3037 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (

let _49_3042 = (tc_decls env tycons deserialized)
in (match (_49_3042) with
| (tycons, _49_3041) -> begin
(

let _49_3046 = (tc_decls env recs deserialized)
in (match (_49_3046) with
| (recs, _49_3045) -> begin
(

let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle ((((FStar_List.append tycons recs)), (quals), (lids), (r)))))
in (

let _49_3051 = (tc_decls env1 rest deserialized)
in (match (_49_3051) with
| (rest, _49_3050) -> begin
(

let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(

let tt = (let _150_1218 = (FStar_Absyn_Syntax.mk_Typ_ascribed ((t), (k)) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _150_1218))
in (

let _49_3067 = (tc_typ_trivial env1 tt)
in (match (_49_3067) with
| (tt, _49_3066) -> begin
(

let _49_3076 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
((bs), (t))
end
| _49_3073 -> begin
(([]), (tt))
end)
in (match (_49_3076) with
| (tps, t) -> begin
(let _150_1220 = (let _150_1219 = (FStar_Absyn_Util.compress_kind k)
in ((lid), (tps), (_150_1219), (t), ([]), (r)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_150_1220))
end))
end)))
end
| _49_3078 -> begin
(let _150_1222 = (let _150_1221 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _150_1221))
in (failwith _150_1222))
end)) recs abbrev_defs)
in (

let _49_3080 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
in (

let se = FStar_Absyn_Syntax.Sig_bundle ((((FStar_List.append tycons (FStar_List.append abbrevs rest))), (quals), (lids), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in ((se), (env))))))
end)))
end))
end))))
end)))
end))
end)))
end))
and tc_decls : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.bool  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Tc_Env.env) = (fun env ses deserialized -> (

let time_tc_decl = (fun env se ds -> (

let start = (FStar_Util.now ())
in (

let res = (tc_decl env se ds)
in (

let stop = (FStar_Util.now ())
in (

let _49_3097 = (FStar_Util.time_diff start stop)
in (match (_49_3097) with
| (diff, _49_3096) -> begin
(

let _49_3098 = (let _150_1232 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _150_1232))
in res)
end))))))
in (

let _49_3113 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _49_3102 se -> (match (_49_3102) with
| (ses, env) -> begin
(

let _49_3104 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _150_1236 = (let _150_1235 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _150_1235))
in (FStar_Util.print_string _150_1236))
end else begin
()
end
in (

let _49_3108 = if (FStar_Options.timing ()) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_49_3108) with
| (se, env) -> begin
(

let _49_3109 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in (((se)::ses), (env)))
end)))
end)) (([]), (env))))
in (match (_49_3113) with
| (ses, env) -> begin
(((FStar_List.rev ses)), (env))
end))))


let rec for_export : FStar_Tc_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___193 -> (match (uu___193) with
| FStar_Absyn_Syntax.Abstract -> begin
true
end
| _49_3122 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Absyn_Syntax.Projector (l, _)) | (FStar_Absyn_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _49_3132 -> begin
false
end))
in (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (_49_3134) -> begin
(([]), (hidden))
end
| FStar_Absyn_Syntax.Sig_datacon (_49_3137) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_tycon (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, binders, knd, def, quals, r) -> begin
if (is_abstract quals) then begin
(

let se = FStar_Absyn_Syntax.Sig_tycon (((lid), (binders), (knd), ([]), ([]), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))
in (((se)::[]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _49_3157, _49_3159) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _49_3165 -> (match (_49_3165) with
| (out, hidden) -> begin
(match (se) with
| FStar_Absyn_Syntax.Sig_tycon (l, bs, t, _49_3170, _49_3172, quals, r) -> begin
(

let dec = FStar_Absyn_Syntax.Sig_tycon (((l), (bs), (t), ([]), ([]), (quals), (r)))
in (((dec)::out), (hidden)))
end
| FStar_Absyn_Syntax.Sig_datacon (l, t, _tc, quals, _mutuals, r) -> begin
(

let t = (FStar_Tc_Env.lookup_datacon env l)
in (

let dec = FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden))))
end
| se -> begin
(for_export env hidden se)
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Absyn_Syntax.Sig_assume (_49_3190, _49_3192, quals, _49_3195) -> begin
if (is_abstract quals) then begin
(([]), (hidden))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Absyn_Syntax.Sig_val_decl (l, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
(((FStar_Absyn_Syntax.Sig_val_decl (((l), (t), ((FStar_Absyn_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___194 -> (match (uu___194) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _49_3213 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Absyn_Syntax.Sig_main (_49_3215) -> begin
(([]), (hidden))
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Absyn_Syntax.Sig_let ((false, (lb)::[]), _49_3231, _49_3233, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let lid = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
(([]), (hidden))
end else begin
(

let dec = FStar_Absyn_Syntax.Sig_val_decl (((lid), (lb.FStar_Absyn_Syntax.lbtyp), ((FStar_Absyn_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end)
end
| FStar_Absyn_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _150_1254 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _150_1253 = (let _150_1252 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in ((_150_1252), (lb.FStar_Absyn_Syntax.lbtyp), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))
in FStar_Absyn_Syntax.Sig_val_decl (_150_1253)))))
in ((_150_1254), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let get_exports : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env modul -> (

let _49_3258 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.fold_left (fun _49_3250 se -> (match (_49_3250) with
| (exports, hidden) -> begin
(

let _49_3254 = (for_export env hidden se)
in (match (_49_3254) with
| (exports', hidden) -> begin
(((exports')::exports), (hidden))
end))
end)) (([]), ([]))))
in (match (_49_3258) with
| (exports, _49_3257) -> begin
(FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
end)))


let tc_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _49_3263 = env
in (let _150_1265 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _49_3263.FStar_Tc_Env.solver; FStar_Tc_Env.range = _49_3263.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _49_3263.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _49_3263.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _49_3263.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _49_3263.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _49_3263.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _49_3263.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _49_3263.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _49_3263.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _49_3263.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _49_3263.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _49_3263.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _49_3263.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _49_3263.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _49_3263.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _49_3263.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _150_1265; FStar_Tc_Env.default_effects = _49_3263.FStar_Tc_Env.default_effects}))
in (

let _49_3266 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (

let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (

let _49_3271 = (tc_decls env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_49_3271) with
| (ses, env) -> begin
(((

let _49_3272 = modul
in {FStar_Absyn_Syntax.name = _49_3272.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _49_3272.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _49_3272.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _49_3272.FStar_Absyn_Syntax.is_deserialized})), (env))
end))))))))


let tc_more_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul decls -> (

let _49_3279 = (tc_decls env decls false)
in (match (_49_3279) with
| (ses, env) -> begin
(

let modul = (

let _49_3280 = modul
in {FStar_Absyn_Syntax.name = _49_3280.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _49_3280.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _49_3280.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _49_3280.FStar_Absyn_Syntax.is_deserialized})
in ((modul), (env)))
end)))


let finish_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (

let exports = (get_exports env modul)
in (

let modul = (

let _49_3286 = modul
in {FStar_Absyn_Syntax.name = _49_3286.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _49_3286.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (

let env = (FStar_Tc_Env.finish_module env modul)
in (

let _49_3296 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(

let _49_3290 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (

let _49_3292 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
in (

let _49_3294 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _150_1276 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _150_1276 Prims.ignore)))))
end else begin
()
end
in ((modul), (env)))))))


let tc_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (

let _49_3302 = (tc_partial_modul env modul)
in (match (_49_3302) with
| (modul, env) -> begin
(finish_partial_modul env modul)
end)))


let add_modul_to_tcenv : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Tc_Env.env = (fun en m -> (

let do_sigelt = (fun en elt -> (

let env = (FStar_Tc_Env.push_sigelt en elt)
in (

let _49_3309 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (

let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _150_1289 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _150_1289 m)))))


let check_module : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env) = (fun env m -> (

let _49_3314 = if (FStar_Options.debug_any ()) then begin
(let _150_1294 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _150_1294))
end else begin
()
end
in (

let _49_3318 = (tc_modul env m)
in (match (_49_3318) with
| (m, env) -> begin
(

let _49_3319 = if (FStar_Options.dump_module m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _150_1295 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _150_1295))
end else begin
()
end
in (((m)::[]), (env)))
end))))




