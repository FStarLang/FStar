
open Prims

type effect_cost =
| ForFree
| NotForFree


let is_ForFree = (fun _discr_ -> (match (_discr_) with
| ForFree (_) -> begin
true
end
| _ -> begin
false
end))


let is_NotForFree = (fun _discr_ -> (match (_discr_) with
| NotForFree (_) -> begin
true
end
| _ -> begin
false
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _146_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _146_5))))))


let rng : FStar_TypeChecker_Env.env  ->  FStar_Range.range = (fun env -> (FStar_TypeChecker_Env.get_range env))


let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_17 = env
in {FStar_TypeChecker_Env.solver = _57_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _57_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_17.FStar_TypeChecker_Env.use_bv_sorts}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _57_20 = env
in {FStar_TypeChecker_Env.solver = _57_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _57_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_20.FStar_TypeChecker_Env.use_bv_sorts}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _146_19 = (let _146_18 = (FStar_Syntax_Syntax.as_arg v)
in (let _146_17 = (let _146_16 = (FStar_Syntax_Syntax.as_arg tl)
in (_146_16)::[])
in (_146_18)::_146_17))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _146_19 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _57_30 -> begin
false
end))


let steps : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::[]
end else begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]
end)


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_32 = (steps env)
in (FStar_TypeChecker_Normalize.normalize _146_32 env t)))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _146_37 = (steps env)
in (FStar_TypeChecker_Normalize.normalize_comp _146_37 env c)))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
()
end
| _57_47 -> begin
(

let fvs' = (let _146_50 = if try_norm then begin
(norm env t)
end else begin
t
end
in (FStar_Syntax_Free.names _146_50))
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
()
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _57_54 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _146_54 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _146_54))
end
| Some (head) -> begin
(let _146_56 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_55 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _146_56 _146_55)))
end)
in (let _146_59 = (let _146_58 = (let _146_57 = (FStar_TypeChecker_Env.get_range env)
in (msg, _146_57))
in FStar_Syntax_Syntax.Error (_146_58))
in (Prims.raise _146_59)))
end))
in (

let s = (let _146_61 = (let _146_60 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_60))
in (FStar_TypeChecker_Util.new_uvar env _146_61))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env g)
end
| _57_63 -> begin
(fail ())
end)))
end
end))
end))
in (aux false kt)))


let maybe_push_binding : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_TypeChecker_Env.env = (fun env b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
env
end else begin
(

let _57_66 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_67 = (FStar_Syntax_Print.bv_to_string (Prims.fst b))
in (let _146_66 = (FStar_Syntax_Print.term_to_string (Prims.fst b).FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_67 _146_66)))
end else begin
()
end
in (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))
end)


let maybe_make_subst = (fun _57_2 -> (match (_57_2) with
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Syntax_Syntax.Name2Term ((x, e)))::[]
end
| _57_75 -> begin
[]
end))


let maybe_extend_subst : FStar_Syntax_Syntax.instantiation  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.instantiation = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.Name2Term (((Prims.fst b), v)))::s
end)


let maybe_extend_renaming : FStar_Syntax_Subst.renaming  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Subst.renaming = (fun s b n -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.Name2Name (((Prims.fst b), n)))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _57_84 = lc
in {FStar_Syntax_Syntax.eff_name = _57_84.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_84.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_86 -> (match (()) with
| () -> begin
(let _146_86 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _146_86 t))
end))}))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _146_95 = if (not ((FStar_Syntax_Util.is_pure_or_ghost_function t))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _146_95))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_118 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, guard)
end
| Some (t') -> begin
(

let _57_100 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_97 = (FStar_Syntax_Print.term_to_string t)
in (let _146_96 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _146_97 _146_96)))
end else begin
()
end
in (

let _57_104 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_57_104) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _57_108 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_57_108) with
| (e, g) -> begin
(

let _57_109 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_99 = (FStar_Syntax_Print.term_to_string t)
in (let _146_98 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "check_and_ascribe: type is %s\n\tguard is %s\n" _146_99 _146_98)))
end else begin
()
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _57_114 = (let _146_105 = (FStar_All.pipe_left (fun _146_104 -> Some (_146_104)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
in (FStar_TypeChecker_Util.strengthen_precondition _146_105 env e lc g))
in (match (_57_114) with
| (lc, g) -> begin
(e, (set_lcomp_result lc t'), g)
end))))
end)))
end)))
end)
in (match (_57_118) with
| (e, lc, g) -> begin
(

let _57_119 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_106 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _146_106))
end else begin
()
end
in (e, lc, g))
end)))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(e, lc, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (t) -> begin
(

let _57_129 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_57_129) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _57_134 -> (match (_57_134) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_57_136) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _146_119 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_146_119))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _146_120 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_146_120))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _146_121 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_146_121))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _146_122 = (norm_c env c)
in (e, _146_122, FStar_TypeChecker_Rel.trivial_guard))
end
| Some (expected_c) -> begin
(

let _57_143 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_125 = (FStar_Syntax_Print.term_to_string e)
in (let _146_124 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_123 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_125 _146_124 _146_123))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_146 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_128 = (FStar_Syntax_Print.term_to_string e)
in (let _146_127 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_126 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _146_128 _146_127 _146_126))))
end else begin
()
end
in (

let _57_152 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_57_152) with
| (e, _57_150, g) -> begin
(

let g = (let _146_129 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _146_129 "could not prove post-condition" g))
in (

let _57_154 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_131 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_130 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _146_131 _146_130)))
end else begin
()
end
in (e, expected_c, g)))
end)))))
end))
end))


let no_logical_guard = (fun env _57_160 -> (match (_57_160) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
(te, kt, f)
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _146_137 = (let _146_136 = (let _146_135 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _146_134 = (FStar_TypeChecker_Env.get_range env)
in (_146_135, _146_134)))
in FStar_Syntax_Syntax.Error (_146_136))
in (Prims.raise _146_137))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _146_140 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _146_140))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _57_184; FStar_Syntax_Syntax.result_typ = _57_182; FStar_Syntax_Syntax.effect_args = _pre::_post::(pats, _57_176)::[]; FStar_Syntax_Syntax.flags = _57_173}) -> begin
(

let pat_vars = (FStar_Syntax_Free.names pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _57_191 -> (match (_57_191) with
| (b, _57_190) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _57_195) -> begin
(let _146_147 = (let _146_146 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _146_146))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _146_147))
end))
end
| _57_199 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let _57_206 = env
in {FStar_TypeChecker_Env.solver = _57_206.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_206.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_206.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_206.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_206.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_206.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_206.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_206.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_206.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_206.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_206.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_206.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_206.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_206.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_206.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_206.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_206.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_206.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_206.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_206.FStar_TypeChecker_Env.use_bv_sorts})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _57_218 -> (match (_57_218) with
| (b, _57_217) -> begin
(

let t = (let _146_161 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _146_161))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _57_227 -> begin
(let _146_162 = (FStar_Syntax_Syntax.bv_to_name b)
in (_146_162)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _57_233 = (FStar_Syntax_Util.head_and_args dec)
in (match (_57_233) with
| (head, _57_232) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _57_237 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.tryFind (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.DECREASES (_57_241) -> begin
true
end
| _57_244 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _57_249 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| x::[] -> begin
x
end
| _57_254 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _57_259 -> (match (_57_259) with
| (l, t) -> begin
(match ((let _146_168 = (FStar_Syntax_Subst.compress t)
in _146_168.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _57_266 -> (match (_57_266) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _146_172 = (let _146_171 = (let _146_170 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_146_170))
in (FStar_Syntax_Syntax.new_bv _146_171 x.FStar_Syntax_Syntax.sort))
in (_146_172, imp))
end else begin
(x, imp)
end
end))))
in (

let _57_270 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_57_270) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _146_176 = (let _146_175 = (FStar_Syntax_Syntax.as_arg dec)
in (let _146_174 = (let _146_173 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_146_173)::[])
in (_146_175)::_146_174))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _146_176 None r))
in (

let _57_277 = (FStar_Util.prefix formals)
in (match (_57_277) with
| (bs, (last, imp)) -> begin
(

let last = (

let _57_278 = last
in (let _146_177 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _57_278.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_278.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_177}))
in (

let refined_formals = (FStar_List.append bs (((last, imp))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _57_283 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_180 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_179 = (FStar_Syntax_Print.term_to_string t)
in (let _146_178 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _146_180 _146_179 _146_178))))
end else begin
()
end
in (l, t')))))
end))))
end)))
end
| _57_286 -> begin
(FStar_All.failwith "Impossible: Annotated type of \'let rec\' is not an arrow")
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end))


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _57_289 = env
in {FStar_TypeChecker_Env.solver = _57_289.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_289.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_289.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_289.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_289.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_289.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_289.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_289.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_289.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_289.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_289.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_289.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_289.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_289.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_289.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_289.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_289.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_289.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_289.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_289.FStar_TypeChecker_Env.use_bv_sorts}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _57_294 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_248 = (let _146_246 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _146_246))
in (let _146_247 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _146_248 _146_247)))
end else begin
()
end
in (

let top = e
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_57_298) -> begin
(let _146_252 = (FStar_Syntax_Subst.compress e)
in (tc_term env _146_252))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _57_339 = (tc_tot_or_gtot_term env e)
in (match (_57_339) with
| (e, c, g) -> begin
(

let g = (

let _57_340 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_340.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_340.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_340.FStar_TypeChecker_Env.implicits})
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _57_350 = (FStar_Syntax_Util.type_u ())
in (match (_57_350) with
| (t, u) -> begin
(

let _57_354 = (tc_check_tot_or_gtot_term env e t)
in (match (_57_354) with
| (e, c, g) -> begin
(

let _57_361 = (

let _57_358 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_358) with
| (env, _57_357) -> begin
(tc_pats env pats)
end))
in (match (_57_361) with
| (pats, g') -> begin
(

let g' = (

let _57_362 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_362.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_362.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_362.FStar_TypeChecker_Env.implicits})
in (let _146_254 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_pattern (pats)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_253 = (FStar_TypeChecker_Rel.conj_guard g g')
in (_146_254, c, _146_253))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _146_255 = (FStar_Syntax_Subst.compress e)
in _146_255.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_57_371, {FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _57_378; FStar_Syntax_Syntax.lbtyp = _57_376; FStar_Syntax_Syntax.lbeff = _57_374; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(

let _57_389 = (let _146_256 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _146_256 e1))
in (match (_57_389) with
| (e1, c1, g1) -> begin
(

let _57_393 = (tc_term env e2)
in (match (_57_393) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (None, c2))
in (

let e = (let _146_261 = (let _146_260 = (let _146_259 = (let _146_258 = (let _146_257 = (FStar_Syntax_Syntax.mk_lb (x, [], c1.FStar_Syntax_Syntax.eff_name, FStar_TypeChecker_Common.t_unit, e1))
in (_146_257)::[])
in (false, _146_258))
in (_146_259, e2))
in FStar_Syntax_Syntax.Tm_let (_146_260))
in (FStar_Syntax_Syntax.mk _146_261 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_262 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (e, c, _146_262)))))
end))
end))
end
| _57_398 -> begin
(

let _57_402 = (tc_term env e)
in (match (_57_402) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _57_411 = (tc_term env e)
in (match (_57_411) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, m))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (e, c, g))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _57_417) -> begin
(

let _57_424 = (tc_comp env expected_c)
in (match (_57_424) with
| (expected_c, _57_422, g) -> begin
(

let _57_428 = (tc_term env e)
in (match (_57_428) with
| (e, c', g') -> begin
(

let _57_432 = (let _146_264 = (let _146_263 = (c'.FStar_Syntax_Syntax.comp ())
in (e, _146_263))
in (check_expected_effect env (Some (expected_c)) _146_264))
in (match (_57_432) with
| (e, expected_c, g'') -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (let _146_267 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t_res), Some ((FStar_Syntax_Util.comp_effect_name expected_c))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_266 = (let _146_265 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _146_265))
in (_146_267, (FStar_Syntax_Util.lcomp_of_comp expected_c), _146_266))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _57_438) -> begin
(

let _57_443 = (FStar_Syntax_Util.type_u ())
in (match (_57_443) with
| (k, u) -> begin
(

let _57_448 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_448) with
| (t, _57_446, f) -> begin
(

let _57_452 = (let _146_268 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _146_268 e))
in (match (_57_452) with
| (e, c, g) -> begin
(

let _57_456 = (let _146_272 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_453 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_272 e c f))
in (match (_57_456) with
| (c, f) -> begin
(

let _57_460 = (let _146_273 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (t), Some (c.FStar_Syntax_Syntax.eff_name)))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _146_273 c))
in (match (_57_460) with
| (e, c, f2) -> begin
(let _146_275 = (let _146_274 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _146_274))
in (e, c, _146_275))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _146_277 = (let _146_276 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_276 Prims.fst))
in (FStar_All.pipe_right _146_277 instantiate_both))
in (

let _57_467 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_279 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_278 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _146_279 _146_278)))
end else begin
()
end
in (

let _57_472 = (tc_term (no_inst env) head)
in (match (_57_472) with
| (head, chead, g_head) -> begin
(

let _57_476 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _146_280 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _146_280))
end else begin
(let _146_281 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _146_281))
end
in (match (_57_476) with
| (e, c, g) -> begin
(

let _57_477 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_282 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _146_282))
end else begin
()
end
in (

let c = if (((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _57_483 = (comp_check_expected_typ env0 e c)
in (match (_57_483) with
| (e, c, g') -> begin
(

let gimp = (match ((let _146_283 = (FStar_Syntax_Subst.compress head)
in _146_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _57_486) -> begin
(

let imp = ("head of application is a uvar", env0, u, e, c.FStar_Syntax_Syntax.res_typ, head.FStar_Syntax_Syntax.pos)
in (

let _57_490 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_490.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_490.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_490.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _57_493 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _146_284 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _146_284))
in (

let _57_496 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_285 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print1 "Guard from application node is %s\n" _146_285))
end else begin
()
end
in (e, c, gres))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _57_504 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_504) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _57_509 = (tc_term env1 e1)
in (match (_57_509) with
| (e1, c1, g1) -> begin
(

let _57_520 = (match (topt) with
| Some (t) -> begin
(env, t)
end
| None -> begin
(

let _57_516 = (FStar_Syntax_Util.type_u ())
in (match (_57_516) with
| (k, _57_515) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _146_286 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in (_146_286, res_t)))
end))
end)
in (match (_57_520) with
| (env_branches, res_t) -> begin
(

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _57_537 = (

let _57_534 = (FStar_List.fold_right (fun _57_528 _57_531 -> (match ((_57_528, _57_531)) with
| ((_57_524, f, c, g), (caccum, gaccum)) -> begin
(let _146_289 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((f, c))::caccum, _146_289))
end)) t_eqns ([], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_534) with
| (cases, g) -> begin
(let _146_290 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in (_146_290, g))
end))
in (match (_57_537) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (guard_x), c_branches))
in (

let e = (let _146_294 = (let _146_293 = (let _146_292 = (FStar_List.map (fun _57_546 -> (match (_57_546) with
| (f, _57_541, _57_543, _57_545) -> begin
f
end)) t_eqns)
in (e1, _146_292))
in FStar_Syntax_Syntax.Tm_match (_146_293))
in (FStar_Syntax_Syntax.mk _146_294 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed ((e, FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ), Some (cres.FStar_Syntax_Syntax.eff_name)))) None e.FStar_Syntax_Syntax.pos)
in (

let _57_549 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_297 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_296 = (let _146_295 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_295))
in (FStar_Util.print2 "(%s) comp type = %s\n" _146_297 _146_296)))
end else begin
()
end
in (let _146_298 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in (e, cres, _146_298))))))
end))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_561); FStar_Syntax_Syntax.lbunivs = _57_559; FStar_Syntax_Syntax.lbtyp = _57_557; FStar_Syntax_Syntax.lbeff = _57_555; FStar_Syntax_Syntax.lbdef = _57_553}::[]), _57_567) -> begin
(

let _57_570 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_299 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_299))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _57_574), _57_577) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_57_592); FStar_Syntax_Syntax.lbunivs = _57_590; FStar_Syntax_Syntax.lbtyp = _57_588; FStar_Syntax_Syntax.lbeff = _57_586; FStar_Syntax_Syntax.lbdef = _57_584}::_57_582), _57_598) -> begin
(

let _57_601 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_300 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _146_300))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _57_605), _57_608) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _57_622 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_622) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_314 = (let _146_313 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_313))
in FStar_Util.Inr (_146_314))
end
in (

let is_data_ctor = (fun _57_4 -> (match (_57_4) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _57_632 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _146_320 = (let _146_319 = (let _146_318 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _146_317 = (FStar_TypeChecker_Env.get_range env)
in (_146_318, _146_317)))
in FStar_Syntax_Syntax.Error (_146_319))
in (Prims.raise _146_320))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(FStar_All.failwith "Impossible: Violation of locally nameless convention")
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _146_321 = (FStar_Syntax_Subst.compress t1)
in _146_321.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_643) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _57_646 -> begin
(

let imp = ("uvar in term", env, u, top, t1, top.FStar_Syntax_Syntax.pos)
in (

let _57_648 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_648.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_648.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_648.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_654 = (FStar_Syntax_Util.type_u ())
in (match (_57_654) with
| (k, u) -> begin
(

let t = (FStar_TypeChecker_Util.new_uvar env k)
in (

let e = (FStar_TypeChecker_Util.new_uvar env t)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let _57_660 = x
in {FStar_Syntax_Syntax.ppname = _57_660.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_660.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _57_666 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_57_666) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _146_323 = (let _146_322 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_322))
in FStar_Util.Inr (_146_323))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_673; FStar_Syntax_Syntax.pos = _57_671; FStar_Syntax_Syntax.vars = _57_669}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _57_683 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_683) with
| (us', t) -> begin
(

let _57_690 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _146_326 = (let _146_325 = (let _146_324 = (FStar_TypeChecker_Env.get_range env)
in ("Unexpected number of universe instantiations", _146_324))
in FStar_Syntax_Syntax.Error (_146_325))
in (Prims.raise _146_326))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _57_689 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _57_692 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_694 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_694.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_694.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_692.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_692.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _146_329 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_329 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _57_702 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_702) with
| (us, t) -> begin
(

let fv' = (

let _57_703 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _57_705 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _57_705.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _57_705.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _57_703.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _57_703.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _146_330 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_330 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t)))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_719 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_719) with
| (bs, c) -> begin
(

let env0 = env
in (

let _57_724 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_724) with
| (env, _57_723) -> begin
(

let _57_729 = (tc_binders env bs)
in (match (_57_729) with
| (bs, env, g, us) -> begin
(

let _57_733 = (tc_comp env c)
in (match (_57_733) with
| (c, uc, f) -> begin
(

let e = (

let _57_734 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _57_734.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_734.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_734.FStar_Syntax_Syntax.vars})
in (

let _57_737 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _146_331 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _146_331))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (tc_universe env u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _57_753 = (let _146_333 = (let _146_332 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_332)::[])
in (FStar_Syntax_Subst.open_term _146_333 phi))
in (match (_57_753) with
| (x, phi) -> begin
(

let env0 = env
in (

let _57_758 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_758) with
| (env, _57_757) -> begin
(

let _57_763 = (let _146_334 = (FStar_List.hd x)
in (tc_binder env _146_334))
in (match (_57_763) with
| (x, env, f1, u) -> begin
(

let _57_764 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_337 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _146_336 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_335 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _146_337 _146_336 _146_335))))
end else begin
()
end
in (

let _57_769 = (FStar_Syntax_Util.type_u ())
in (match (_57_769) with
| (t_phi, _57_768) -> begin
(

let _57_774 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_57_774) with
| (phi, _57_772, f2) -> begin
(

let e = (

let _57_775 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _57_775.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _57_775.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_775.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _146_338 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _146_338))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_783) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _57_789 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_339 = (FStar_Syntax_Print.term_to_string (

let _57_787 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((bs, body, None)); FStar_Syntax_Syntax.tk = _57_787.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_787.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_787.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _146_339))
end else begin
()
end
in (

let _57_793 = (FStar_Syntax_Subst.open_term bs body)
in (match (_57_793) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _57_795 -> begin
(let _146_341 = (let _146_340 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Unexpected value: %s" _146_340))
in (FStar_All.failwith _146_341))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_57_800) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_57_803, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_57_808, Some (FStar_Const.Unsigned, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_uint8
end
| FStar_Const.Const_int (_57_816, Some (FStar_Const.Signed, FStar_Const.Int8)) -> begin
FStar_TypeChecker_Common.t_int8
end
| FStar_Const.Const_int (_57_824, Some (FStar_Const.Unsigned, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_uint16
end
| FStar_Const.Const_int (_57_832, Some (FStar_Const.Signed, FStar_Const.Int16)) -> begin
FStar_TypeChecker_Common.t_int16
end
| FStar_Const.Const_int (_57_840, Some (FStar_Const.Unsigned, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_uint32
end
| FStar_Const.Const_int (_57_848, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
FStar_TypeChecker_Common.t_int32
end
| FStar_Const.Const_int (_57_856, Some (FStar_Const.Unsigned, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_uint64
end
| FStar_Const.Const_int (_57_864, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
FStar_TypeChecker_Common.t_int64
end
| FStar_Const.Const_string (_57_872) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_57_875) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_57_878) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_57_882) -> begin
FStar_TypeChecker_Common.t_range
end
| _57_885 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unsupported constant", r))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _57_892 = (FStar_Syntax_Util.type_u ())
in (match (_57_892) with
| (k, u) -> begin
(

let _57_897 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_897) with
| (t, _57_895, g) -> begin
(let _146_346 = (FStar_Syntax_Syntax.mk_Total t)
in (_146_346, u, g))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _57_902 = (FStar_Syntax_Util.type_u ())
in (match (_57_902) with
| (k, u) -> begin
(

let _57_907 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_907) with
| (t, _57_905, g) -> begin
(let _146_347 = (FStar_Syntax_Syntax.mk_GTotal t)
in (_146_347, u, g))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let tc = (let _146_349 = (let _146_348 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_348)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _146_349 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _57_916 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_57_916) with
| (tc, _57_914, f) -> begin
(

let _57_920 = (FStar_Syntax_Util.head_and_args tc)
in (match (_57_920) with
| (_57_918, args) -> begin
(

let _57_923 = (let _146_351 = (FStar_List.hd args)
in (let _146_350 = (FStar_List.tl args)
in (_146_351, _146_350)))
in (match (_57_923) with
| (res, args) -> begin
(

let _57_939 = (let _146_353 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _57_5 -> (match (_57_5) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _57_930 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_930) with
| (env, _57_929) -> begin
(

let _57_935 = (tc_tot_or_gtot_term env e)
in (match (_57_935) with
| (e, _57_933, g) -> begin
(FStar_Syntax_Syntax.DECREASES (e), g)
end))
end))
end
| f -> begin
(f, FStar_TypeChecker_Rel.trivial_guard)
end))))
in (FStar_All.pipe_right _146_353 FStar_List.unzip))
in (match (_57_939) with
| (flags, guards) -> begin
(

let u = (match ((FStar_ST.read (Prims.fst res).FStar_Syntax_Syntax.tk)) with
| Some (FStar_Syntax_Syntax.Tm_type (u)) -> begin
u
end
| _57_944 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _146_355 = (FStar_Syntax_Syntax.mk_Comp (

let _57_946 = c
in {FStar_Syntax_Syntax.effect_name = _57_946.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _57_946.FStar_Syntax_Syntax.flags}))
in (let _146_354 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in (_146_355, u, _146_354))))
end))
end))
end))
end))))
end))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_57_954) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_360 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_360))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_361 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_361))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _146_365 = (let _146_364 = (let _146_363 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _146_362 = (FStar_TypeChecker_Env.get_range env)
in (_146_363, _146_362)))
in FStar_Syntax_Syntax.Error (_146_364))
in (Prims.raise _146_365))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _146_366 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_366 Prims.snd))
end
| _57_969 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _146_375 = (let _146_374 = (let _146_373 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in (_146_373, top.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_374))
in (Prims.raise _146_375)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _57_987 bs bs_expected -> (match (_57_987) with
| (env, out, g, subst) -> begin
(match ((bs, bs_expected)) with
| ([], []) -> begin
(env, (FStar_List.rev out), None, g, subst)
end
| ((hd, imp)::bs, (hd_expected, imp')::bs_expected) -> begin
(

let _57_1018 = (match ((imp, imp')) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _146_392 = (let _146_391 = (let _146_390 = (let _146_388 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _146_388))
in (let _146_389 = (FStar_Syntax_Syntax.range_of_bv hd)
in (_146_390, _146_389)))
in FStar_Syntax_Syntax.Error (_146_391))
in (Prims.raise _146_392))
end
| _57_1017 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Renaming (subst)) hd_expected.FStar_Syntax_Syntax.sort)
in (

let _57_1035 = (match ((let _146_393 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _146_393.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(expected_t, g)
end
| _57_1023 -> begin
(

let _57_1024 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_394 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _146_394))
end else begin
()
end
in (

let _57_1030 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_57_1030) with
| (t, _57_1028, g1) -> begin
(

let g2 = (let _146_396 = (FStar_TypeChecker_Env.get_range env)
in (let _146_395 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _146_396 "Type annotation on parameter incompatible with the expected type" _146_395)))
in (

let g = (let _146_397 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _146_397))
in (t, g)))
end)))
end)
in (match (_57_1035) with
| (t, g) -> begin
(

let hd = (

let _57_1036 = hd
in {FStar_Syntax_Syntax.ppname = _57_1036.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1036.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = (hd, imp)
in (

let b_expected = (hd_expected, imp')
in (

let env = (maybe_push_binding env b)
in (

let subst = (maybe_extend_renaming subst b_expected hd)
in (aux (env, (b)::out, g, subst) bs bs_expected))))))
end))))
end
| (rest, []) -> begin
(env, (FStar_List.rev out), Some (FStar_Util.Inl (rest)), g, subst)
end
| ([], rest) -> begin
(env, (FStar_List.rev out), Some (FStar_Util.Inr (rest)), g, subst)
end)
end))
in (aux (env, [], FStar_TypeChecker_Rel.trivial_guard, []) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(

let _57_1057 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1056 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _57_1064 = (tc_binders env bs)
in (match (_57_1064) with
| (bs, envbody, g, _57_1063) -> begin
(

let _57_1082 = (match ((let _146_404 = (FStar_Syntax_Subst.compress body)
in _146_404.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _57_1069) -> begin
(

let _57_1076 = (tc_comp envbody c)
in (match (_57_1076) with
| (c, _57_1074, g') -> begin
(let _146_405 = (FStar_TypeChecker_Rel.conj_guard g g')
in (Some (c), body, _146_405))
end))
end
| _57_1078 -> begin
(None, body, g)
end)
in (match (_57_1082) with
| (copt, body, g) -> begin
(None, bs, [], copt, envbody, body, g)
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _146_410 = (FStar_Syntax_Subst.compress t)
in _146_410.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _57_1109 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _57_1108 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _57_1116 = (tc_binders env bs)
in (match (_57_1116) with
| (bs, envbody, g, _57_1115) -> begin
(

let _57_1120 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_57_1120) with
| (envbody, _57_1119) -> begin
(Some ((t, true)), bs, [], None, envbody, body, g)
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _57_1123) -> begin
(

let _57_1134 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_57_1134) with
| (_57_1127, bs, bs', copt, env, body, g) -> begin
(Some ((t, false)), bs, bs', copt, env, body, g)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1141 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_57_1141) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _57_1152 c_expected -> (match (_57_1152) with
| (env, bs, more, guard, renaming) -> begin
(match (more) with
| None -> begin
(let _146_421 = (FStar_Syntax_Subst.subst_comp (FStar_Syntax_Syntax.Renaming (renaming)) c_expected)
in (env, bs, guard, _146_421))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _146_422 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _146_422))
in (let _146_423 = (FStar_Syntax_Subst.subst_comp (FStar_Syntax_Syntax.Renaming (renaming)) c)
in (env, bs, guard, _146_423)))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp (FStar_Syntax_Syntax.Renaming (renaming)) c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _57_1173 = (check_binders env more_bs bs_expected)
in (match (_57_1173) with
| (env, bs', more, guard', subst) -> begin
(let _146_425 = (let _146_424 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (env, (FStar_List.append bs bs'), more, _146_424, subst))
in (handle_more _146_425 c_expected))
end))
end
| _57_1175 -> begin
(let _146_427 = (let _146_426 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _146_426))
in (fail _146_427 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _146_428 = (check_binders env bs bs_expected)
in (handle_more _146_428 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _57_1181 = envbody
in {FStar_TypeChecker_Env.solver = _57_1181.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1181.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1181.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1181.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1181.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1181.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1181.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1181.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1181.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1181.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1181.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1181.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _57_1181.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1181.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1181.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1181.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1181.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1181.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1181.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1181.FStar_TypeChecker_Env.use_bv_sorts})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _57_1186 _57_1189 -> (match ((_57_1186, _57_1189)) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _57_1195 = (let _146_438 = (let _146_437 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_437 Prims.fst))
in (tc_term _146_438 t))
in (match (_57_1195) with
| (t, _57_1192, _57_1194) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l ([], t))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _146_439 = (FStar_Syntax_Syntax.mk_binder (

let _57_1199 = x
in {FStar_Syntax_Syntax.ppname = _57_1199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_146_439)::letrec_binders)
end
| _57_1202 -> begin
letrec_binders
end)
in (env, lb)))
end))
end)) (envbody, []))))))
in (

let _57_1208 = (check_actuals_against_formals env bs bs_expected)
in (match (_57_1208) with
| (envbody, bs, g, c) -> begin
(

let _57_1211 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_env envbody bs c)
end else begin
(envbody, [])
end
in (match (_57_1211) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in (Some ((t, false)), bs, letrecs, Some (c), envbody, body, g))
end))
end))))
end))
end
| _57_1214 -> begin
if (not (norm)) then begin
(let _146_440 = (unfold_whnf env t)
in (as_function_typ true _146_440))
end else begin
(

let _57_1224 = (expected_function_typ env None body)
in (match (_57_1224) with
| (_57_1216, bs, _57_1219, c_opt, envbody, body, g) -> begin
(Some ((t, false)), bs, [], c_opt, envbody, body, g)
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _57_1228 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1228) with
| (env, topt) -> begin
(

let _57_1232 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_441 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _146_441 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _57_1241 = (expected_function_typ env topt body)
in (match (_57_1241) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _57_1247 = (tc_term (

let _57_1242 = envbody
in {FStar_TypeChecker_Env.solver = _57_1242.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1242.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1242.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1242.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1242.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1242.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1242.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1242.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1242.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1242.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1242.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1242.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1242.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1242.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1242.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1242.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1242.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1242.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1242.FStar_TypeChecker_Env.use_bv_sorts}) body)
in (match (_57_1247) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _57_1249 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _146_444 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _146_443 = (let _146_442 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _146_442))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _146_444 _146_443)))
end else begin
()
end
in (

let _57_1256 = (let _146_446 = (let _146_445 = (cbody.FStar_Syntax_Syntax.comp ())
in (body, _146_445))
in (check_expected_effect (

let _57_1251 = envbody
in {FStar_TypeChecker_Env.solver = _57_1251.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1251.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1251.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1251.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1251.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1251.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1251.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1251.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1251.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1251.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1251.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1251.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1251.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1251.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1251.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _57_1251.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1251.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1251.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1251.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1251.FStar_TypeChecker_Env.use_bv_sorts}) c_opt _146_446))
in (match (_57_1256) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)))) then begin
(let _146_447 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _146_447))
end else begin
(

let guard = (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_TypeChecker_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _146_450 = (let _146_449 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _146_448 -> FStar_Util.Inl (_146_448)))
in Some (_146_449))
in (FStar_Syntax_Util.abs bs body _146_450))
in (

let _57_1279 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_1268) -> begin
(e, t, guard)
end
| _57_1271 -> begin
(

let _57_1274 = if use_teq then begin
(let _146_451 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in (e, _146_451))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_57_1274) with
| (e, guard') -> begin
(let _146_452 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in (e, t, _146_452))
end))
end))
end
| None -> begin
(e, tfun_computed, guard)
end)
in (match (_57_1279) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _57_1283 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_57_1283) with
| (c, g) -> begin
(e, c, g)
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in (

let _57_1293 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_461 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _146_460 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _146_461 _146_460)))
end else begin
()
end
in (

let rec check_function_app = (fun norm tf -> (match ((let _146_466 = (FStar_Syntax_Util.unrefine tf)
in _146_466.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
([], [], FStar_TypeChecker_Rel.trivial_guard)
end
| (e, imp)::tl -> begin
(

let _57_1327 = (tc_term env e)
in (match (_57_1327) with
| (e, c, g_e) -> begin
(

let _57_1331 = (tc_args env tl)
in (match (_57_1331) with
| (args, comps, g_rest) -> begin
(let _146_471 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((e, imp))::args, ((e.FStar_Syntax_Syntax.pos, c))::comps, _146_471))
end))
end))
end))
in (

let _57_1335 = (tc_args env args)
in (match (_57_1335) with
| (args, comps, g_args) -> begin
(

let bs = (let _146_473 = (FStar_All.pipe_right comps (FStar_List.map (fun _57_1339 -> (match (_57_1339) with
| (_57_1337, c) -> begin
(c.FStar_Syntax_Syntax.res_typ, None)
end))))
in (FStar_Syntax_Util.null_binders_of_tks _146_473))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _57_1345 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _146_488 = (FStar_Syntax_Subst.compress t)
in _146_488.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1351) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _57_1356 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _146_493 = (let _146_492 = (let _146_491 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_491 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _146_492))
in (ml_or_tot _146_493 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _57_1360 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_496 = (FStar_Syntax_Print.term_to_string head)
in (let _146_495 = (FStar_Syntax_Print.term_to_string tf)
in (let _146_494 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _146_496 _146_495 _146_494))))
end else begin
()
end
in (

let _57_1362 = (let _146_497 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _146_497))
in (

let comp = (let _146_500 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _57_1366 out -> (match (_57_1366) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (None, out))
end)) (((head.FStar_Syntax_Syntax.pos, chead))::comps) _146_500))
in (let _146_502 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _146_501 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in (_146_502, comp, _146_501)))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _57_1375 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1375) with
| (bs, c) -> begin
(

let rec tc_args = (fun _57_1383 bs cres args -> (match (_57_1383) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match ((bs, args)) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (_57_1390)))::rest, (_57_1398, None)::_57_1396) -> begin
(

let t = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) x.FStar_Syntax_Syntax.sort)
in (

let _57_1404 = (check_no_escape (Some (head)) env fvs t)
in (

let _57_1410 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_57_1410) with
| (varg, _57_1408, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.Name2Term ((x, varg)))::subst
in (

let arg = (let _146_511 = (FStar_Syntax_Syntax.as_implicit true)
in (varg, _146_511))
in (let _146_513 = (let _146_512 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in (subst, (arg)::outargs, (arg)::arg_rets, comps, _146_512, fvs))
in (tc_args _146_513 rest cres args))))
end))))
end
| ((x, aqual)::rest, (e, aq)::rest') -> begin
(

let _57_1442 = (match ((aqual, aq)) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _57_1441 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifier", e.FStar_Syntax_Syntax.pos))))
end)
in (

let targ = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_1445 = x
in {FStar_Syntax_Syntax.ppname = _57_1445.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1445.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _57_1448 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_514 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _146_514))
end else begin
()
end
in (

let _57_1450 = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _57_1453 = env
in {FStar_TypeChecker_Env.solver = _57_1453.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1453.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1453.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1453.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1453.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1453.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1453.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1453.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1453.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1453.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1453.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1453.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1453.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1453.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1453.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _57_1453.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1453.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1453.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1453.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1453.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1456 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_517 = (FStar_Syntax_Print.tag_of_term e)
in (let _146_516 = (FStar_Syntax_Print.term_to_string e)
in (let _146_515 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _146_517 _146_516 _146_515))))
end else begin
()
end
in (

let _57_1461 = (tc_term env e)
in (match (_57_1461) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = (e, aq)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _146_518 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_518 e))
in (tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, g, fvs) rest cres rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _146_519 = (FStar_List.hd bs)
in (maybe_extend_subst subst _146_519 e))
in (

let _57_1468 = (((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g)
in (match (_57_1468) with
| (comps, guard) -> begin
(tc_args (subst, (arg)::outargs, (arg)::arg_rets, comps, guard, fvs) rest cres rest')
end)))
end else begin
if (let _146_520 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _146_520)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _146_521 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_521))
in (tc_args (subst, (arg)::outargs, (arg')::arg_rets, ((e.FStar_Syntax_Syntax.pos, Some (newx), c))::comps, g, fvs) rest cres rest')))
end else begin
(let _146_525 = (let _146_524 = (let _146_523 = (let _146_522 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_522))
in (_146_523)::arg_rets)
in (subst, (arg)::outargs, _146_524, ((e.FStar_Syntax_Syntax.pos, Some (x), c))::comps, g, (x)::fvs))
in (tc_args _146_525 rest cres rest'))
end
end
end))
end))))))))))
end
| (_57_1472, []) -> begin
(

let _57_1475 = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let _57_1495 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp (FStar_Syntax_Syntax.Instantiation (subst)) cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _57_1485 -> (match (_57_1485) with
| (_57_1481, _57_1483, c) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _146_527 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _146_527 cres))
end else begin
(

let _57_1487 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_530 = (FStar_Syntax_Print.term_to_string head)
in (let _146_529 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _146_528 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _146_530 _146_529 _146_528))))
end else begin
()
end
in cres)
end
in (cres, g)))))
end
| _57_1491 -> begin
(

let g = (let _146_531 = (FStar_TypeChecker_Rel.conj_guard ghead g)
in (FStar_All.pipe_right _146_531 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _146_536 = (let _146_535 = (let _146_534 = (let _146_533 = (let _146_532 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _146_532))
in (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Instantiation (subst)) _146_533))
in (FStar_Syntax_Syntax.mk_Total _146_534))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_535))
in (_146_536, g)))
end)
in (match (_57_1495) with
| (cres, g) -> begin
(

let _57_1496 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_537 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _146_537))
end else begin
()
end
in (

let comp = (FStar_List.fold_left (fun out _57_1502 -> (match (_57_1502) with
| (r1, x, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c (x, out))
end)) cres comps)
in (

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead (None, comp))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev outargs) (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let _57_1508 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp g)
in (match (_57_1508) with
| (comp, g) -> begin
(app, comp, g)
end))))))
end)))
end
| ([], arg::_57_1511) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _146_545 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _146_545 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _57_1523 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_546 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _146_546))
end else begin
()
end
in (let _146_550 = (let _146_549 = (let _146_548 = (let _146_547 = (FStar_TypeChecker_Env.get_range env)
in (_146_547, None, cres))
in (_146_548)::comps)
in (subst, outargs, arg_rets, _146_549, g, fvs))
in (tc_args _146_550 bs (FStar_Syntax_Util.lcomp_of_comp cres') args)))
end
| _57_1526 when (not (norm)) -> begin
(let _146_551 = (unfold_whnf env tres)
in (aux true _146_551))
end
| _57_1528 -> begin
(let _146_557 = (let _146_556 = (let _146_555 = (let _146_553 = (FStar_TypeChecker_Normalize.term_to_string env tf)
in (let _146_552 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _146_553 _146_552)))
in (let _146_554 = (FStar_Syntax_Syntax.argpos arg)
in (_146_555, _146_554)))
in FStar_Syntax_Syntax.Error (_146_556))
in (Prims.raise _146_557))
end)))
in (aux false cres.FStar_Syntax_Syntax.res_typ))
end)
end))
in (tc_args ([], [], [], [], FStar_TypeChecker_Rel.trivial_guard, []) bs (FStar_Syntax_Util.lcomp_of_comp c) args))
end))
end
| _57_1530 -> begin
if (not (norm)) then begin
(let _146_558 = (unfold_whnf env tf)
in (check_function_app true _146_558))
end else begin
(let _146_561 = (let _146_560 = (let _146_559 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in (_146_559, head.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_560))
in (Prims.raise _146_561))
end
end))
in (let _146_563 = (let _146_562 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_562))
in (check_function_app false _146_563))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _57_1566 = (FStar_List.fold_left2 (fun _57_1547 _57_1550 _57_1553 -> (match ((_57_1547, _57_1550, _57_1553)) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _57_1554 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inconsistent implicit qualifiers", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_1559 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_57_1559) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _146_573 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _146_573 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _146_577 = (let _146_575 = (let _146_574 = (FStar_Syntax_Syntax.as_arg e)
in (_146_574)::[])
in (FStar_List.append seen _146_575))
in (let _146_576 = (FStar_TypeChecker_Rel.conj_guard guard g)
in (_146_577, _146_576, ghost))))))
end)))
end)) ([], g_head, false) args bs)
in (match (_57_1566) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _146_578 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _146_578 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _57_1571 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_57_1571) with
| (c, g) -> begin
(e, c, g)
end))))
end)))
end
| _57_1573 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _57_1580 = (FStar_Syntax_Subst.open_branch branch)
in (match (_57_1580) with
| (pattern, when_clause, branch_exp) -> begin
(

let _57_1585 = branch
in (match (_57_1585) with
| (cpat, _57_1583, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _57_1593 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_57_1593) with
| (pat_bvs, exps, p) -> begin
(

let _57_1594 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_590 = (FStar_Syntax_Print.pat_to_string p0)
in (let _146_589 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _146_590 _146_589)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _57_1600 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_57_1600) with
| (env1, _57_1599) -> begin
(

let env1 = (

let _57_1601 = env1
in {FStar_TypeChecker_Env.solver = _57_1601.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1601.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1601.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1601.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1601.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1601.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1601.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1601.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _57_1601.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1601.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1601.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1601.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1601.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1601.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1601.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1601.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1601.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1601.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1601.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1601.FStar_TypeChecker_Env.use_bv_sorts})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _57_1640 = (let _146_613 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _57_1606 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_593 = (FStar_Syntax_Print.term_to_string e)
in (let _146_592 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _146_593 _146_592)))
end else begin
()
end
in (

let _57_1611 = (tc_term env1 e)
in (match (_57_1611) with
| (e, lc, g) -> begin
(

let _57_1612 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_595 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_594 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _146_595 _146_594)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _57_1618 = (let _146_596 = (FStar_TypeChecker_Rel.discharge_guard env (

let _57_1616 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1616.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1616.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1616.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _146_596 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _146_601 = (let _146_600 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _146_600 (FStar_List.map (fun _57_1626 -> (match (_57_1626) with
| (u, _57_1625) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _146_601 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _57_1634 = if (let _146_602 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _146_602)) then begin
(

let unresolved = (let _146_603 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _146_603 FStar_Util.set_elements))
in (let _146_611 = (let _146_610 = (let _146_609 = (let _146_608 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _146_607 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _146_606 = (let _146_605 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _57_1633 -> (match (_57_1633) with
| (u, _57_1632) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_605 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _146_608 _146_607 _146_606))))
in (_146_609, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_610))
in (Prims.raise _146_611)))
end else begin
()
end
in (

let _57_1636 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_612 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _146_612))
end else begin
()
end
in (e, e')))))))))))
end))))))
in (FStar_All.pipe_right _146_613 FStar_List.unzip))
in (match (_57_1640) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in (p, pat_bvs, pat_env, exps, norm_exps))
end))))
end))))
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let _57_1647 = (let _146_614 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _146_614 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_57_1647) with
| (scrutinee_env, _57_1646) -> begin
(

let _57_1653 = (tc_pat true pat_t pattern)
in (match (_57_1653) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _57_1663 = (match (when_clause) with
| None -> begin
(None, FStar_TypeChecker_Rel.trivial_guard)
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("When clauses are not yet supported in --verify mode; they will be some day", e.FStar_Syntax_Syntax.pos))))
end else begin
(

let _57_1660 = (let _146_615 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _146_615 e))
in (match (_57_1660) with
| (e, c, g) -> begin
(Some (e), g)
end))
end
end)
in (match (_57_1663) with
| (when_clause, g_when) -> begin
(

let _57_1667 = (tc_term pat_env branch_exp)
in (match (_57_1667) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_617 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _146_616 -> Some (_146_616)) _146_617))
end)
in (

let _57_1723 = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _57_1685 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _146_621 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _146_620 -> Some (_146_620)) _146_621))
end))
end))) None))
in (

let _57_1693 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_57_1693) with
| (c, g_branch) -> begin
(

let _57_1718 = (match ((eqs, when_condition)) with
| (None, None) -> begin
(c, g_when)
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _146_624 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _146_623 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in (_146_624, _146_623)))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _146_625 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_146_625))
in (let _146_628 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _146_627 = (let _146_626 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _146_626 g_when))
in (_146_628, _146_627)))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _146_629 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in (_146_629, g_when))))
end)
in (match (_57_1718) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _146_631 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _146_630 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in (_146_631, _146_630, g_branch))))
end))
end)))
in (match (_57_1723) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = (

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _146_641 = (let _146_640 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _146_640))
in (FStar_List.length _146_641)) > 1) then begin
(

let disc = (let _146_642 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _146_642 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _146_644 = (let _146_643 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_643)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _146_644 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _146_645 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_146_645)::[])))
end else begin
[]
end)
in (

let fail = (fun _57_1733 -> (match (()) with
| () -> begin
(let _146_651 = (let _146_650 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _146_649 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _146_648 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _146_650 _146_649 _146_648))))
in (FStar_All.failwith _146_651))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_1740) -> begin
(head_constructor t)
end
| _57_1744 -> begin
(fail ())
end))
in (

let pat_exp = (let _146_654 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _146_654 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_57_1769) -> begin
(let _146_659 = (let _146_658 = (let _146_657 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _146_656 = (let _146_655 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_146_655)::[])
in (_146_657)::_146_656))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _146_658 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_146_659)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _146_660 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _146_660))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _146_667 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _57_1787 -> (match (_57_1787) with
| (ei, _57_1786) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _57_1791 -> begin
(

let sub_term = (let _146_666 = (let _146_663 = (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.fvar _146_663 FStar_Syntax_Syntax.Delta_equational None))
in (let _146_665 = (let _146_664 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_146_664)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _146_666 _146_665 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _146_667 FStar_List.flatten))
in (let _146_668 = (discriminate scrutinee_tm f)
in (FStar_List.append _146_668 sub_term_guards)))
end)
end
| _57_1795 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _146_673 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _146_673))
in (

let _57_1803 = (FStar_Syntax_Util.type_u ())
in (match (_57_1803) with
| (k, _57_1802) -> begin
(

let _57_1809 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_57_1809) with
| (t, _57_1806, _57_1808) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _146_674 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _146_674 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (

let _57_1817 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_675 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _146_675))
end else begin
()
end
in (let _146_676 = (FStar_Syntax_Subst.close_branch (pattern, when_clause, branch_exp))
in (_146_676, branch_guard, c, guard)))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(

let _57_1834 = (check_let_bound_def true env lb)
in (match (_57_1834) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _57_1846 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(g1, e1, univ_vars, c1)
end else begin
(

let g1 = (let _146_679 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _146_679 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _57_1841 = (let _146_683 = (let _146_682 = (let _146_681 = (let _146_680 = (c1.FStar_Syntax_Syntax.comp ())
in (lb.FStar_Syntax_Syntax.lbname, e1, _146_680))
in (_146_681)::[])
in (FStar_TypeChecker_Util.generalize env _146_682))
in (FStar_List.hd _146_683))
in (match (_57_1841) with
| (_57_1837, univs, e1, c1) -> begin
(g1, e1, univs, (FStar_Syntax_Util.lcomp_of_comp c1))
end)))
end
in (match (_57_1846) with
| (g1, e1, univ_vars, c1) -> begin
(

let _57_1856 = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(

let _57_1849 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_57_1849) with
| (ok, c1) -> begin
if ok then begin
(e2, c1)
end else begin
(

let _57_1850 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _146_684 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _146_684 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _146_685 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e2, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)))) None e2.FStar_Syntax_Syntax.pos)
in (_146_685, c1)))
end
end))
end else begin
(

let _57_1852 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (let _146_686 = (c1.FStar_Syntax_Syntax.comp ())
in (e2, _146_686)))
end
in (match (_57_1856) with
| (e2, c1) -> begin
(

let cres = (let _146_687 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_687))
in (

let _57_1858 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _146_688 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (_146_688, cres, FStar_TypeChecker_Rel.trivial_guard)))))
end))
end))
end))
end
| _57_1862 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), e2) -> begin
(

let env = (

let _57_1873 = env
in {FStar_TypeChecker_Env.solver = _57_1873.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1873.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1873.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1873.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1873.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1873.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1873.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1873.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1873.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1873.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1873.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1873.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1873.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_1873.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_1873.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_1873.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1873.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_1873.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1873.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1873.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_1882 = (let _146_692 = (let _146_691 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _146_691 Prims.fst))
in (check_let_bound_def false _146_692 lb))
in (match (_57_1882) with
| (e1, _57_1878, c1, g1, annotated) -> begin
(

let x = (

let _57_1883 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1883.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1883.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let _57_1889 = (let _146_694 = (let _146_693 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_693)::[])
in (FStar_Syntax_Subst.open_term _146_694 e2))
in (match (_57_1889) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _57_1895 = (let _146_695 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _146_695 e2))
in (match (_57_1895) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 (Some (x), c2))
in (

let e = (let _146_698 = (let _146_697 = (let _146_696 = (FStar_Syntax_Subst.close xb e2)
in ((false, (lb)::[]), _146_696))
in FStar_Syntax_Syntax.Tm_let (_146_697))
in (FStar_Syntax_Syntax.mk _146_698 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let x_eq_e1 = (let _146_701 = (let _146_700 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _146_700 e1))
in (FStar_All.pipe_left (fun _146_699 -> FStar_TypeChecker_Common.NonTrivial (_146_699)) _146_701))
in (

let g2 = (let _146_703 = (let _146_702 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _146_702 g2))
in (FStar_TypeChecker_Rel.close_guard xb _146_703))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if annotated then begin
(e, cres, guard)
end else begin
(

let _57_1901 = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (e, cres, guard))
end)))))
end))))
end))))
end)))
end
| _57_1904 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1916 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1916) with
| (lbs, e2) -> begin
(

let _57_1919 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1919) with
| (env0, topt) -> begin
(

let _57_1922 = (build_let_rec_env true env0 lbs)
in (match (_57_1922) with
| (lbs, rec_env) -> begin
(

let _57_1925 = (check_let_recs rec_env lbs)
in (match (_57_1925) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _146_706 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _146_706 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _146_709 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _146_709 (fun _146_708 -> Some (_146_708))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _146_713 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _146_712 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in (lb.FStar_Syntax_Syntax.lbname, lb.FStar_Syntax_Syntax.lbdef, _146_712)))))
in (FStar_TypeChecker_Util.generalize env _146_713))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1936 -> (match (_57_1936) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _146_715 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_715))
in (

let _57_1939 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _57_1943 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1943) with
| (lbs, e2) -> begin
(let _146_717 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _146_716 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in (_146_717, cres, _146_716)))
end)))))))
end))
end))
end))
end))
end
| _57_1945 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _57_1957 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_57_1957) with
| (lbs, e2) -> begin
(

let _57_1960 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_1960) with
| (env0, topt) -> begin
(

let _57_1963 = (build_let_rec_env false env0 lbs)
in (match (_57_1963) with
| (lbs, rec_env) -> begin
(

let _57_1966 = (check_let_recs rec_env lbs)
in (match (_57_1966) with
| (lbs, g_lbs) -> begin
(

let _57_1978 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _57_1969 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _57_1969.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1969.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _57_1972 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _57_1972.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1972.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1972.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1972.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], lb.FStar_Syntax_Syntax.lbtyp))
in (env, lb))))) env))
in (match (_57_1978) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _57_1984 = (tc_term env e2)
in (match (_57_1984) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _57_1988 = cres
in {FStar_Syntax_Syntax.eff_name = _57_1988.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _57_1988.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1988.FStar_Syntax_Syntax.comp})
in (

let _57_1993 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_57_1993) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), e2))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_57_1996) -> begin
(e, cres, guard)
end
| None -> begin
(

let _57_1999 = (check_no_escape None env bvs tres)
in (e, cres, guard))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _57_2002 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let _57_2035 = (FStar_List.fold_left (fun _57_2009 lb -> (match (_57_2009) with
| (lbs, env) -> begin
(

let _57_2014 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_57_2014) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(

let _57_2023 = (let _146_729 = (let _146_728 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _146_728))
in (tc_check_tot_or_gtot_term (

let _57_2017 = env0
in {FStar_TypeChecker_Env.solver = _57_2017.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2017.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2017.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2017.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2017.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2017.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2017.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2017.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2017.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2017.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2017.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2017.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2017.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2017.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _57_2017.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2017.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2017.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2017.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2017.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2017.FStar_TypeChecker_Env.use_bv_sorts}) t _146_729))
in (match (_57_2023) with
| (t, _57_2021, g) -> begin
(

let _57_2024 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((FStar_Syntax_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)) then begin
(

let _57_2027 = env
in {FStar_TypeChecker_Env.solver = _57_2027.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2027.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2027.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2027.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2027.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2027.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2027.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2027.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2027.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2027.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2027.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2027.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = ((lb.FStar_Syntax_Syntax.lbname, t))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_2027.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_2027.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2027.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2027.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2027.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2027.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2027.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2027.FStar_TypeChecker_Env.use_bv_sorts})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname ([], t))
end
in (

let lb = (

let _57_2030 = lb
in {FStar_Syntax_Syntax.lbname = _57_2030.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_2030.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in ((lb)::lbs, env))))))
end))
end)) ([], env) lbs)
in (match (_57_2035) with
| (lbs, env) -> begin
((FStar_List.rev lbs), env)
end))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _57_2048 = (let _146_734 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _57_2042 = (let _146_733 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _146_733 lb.FStar_Syntax_Syntax.lbdef))
in (match (_57_2042) with
| (e, c, g) -> begin
(

let _57_2043 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Expected let rec to be a Tot term; got effect GTot", e.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in (lb, g)))
end)))))
in (FStar_All.pipe_right _146_734 FStar_List.unzip))
in (match (_57_2048) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in (lbs, g_lbs))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _57_2056 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_57_2056) with
| (env1, _57_2055) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _57_2062 = (check_lbtyp top_level env lb)
in (match (_57_2062) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _57_2063 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Inner let-bound definitions cannot be universe polymorphic", e1.FStar_Syntax_Syntax.pos))))
end else begin
()
end
in (

let _57_2070 = (tc_maybe_toplevel_term (

let _57_2065 = env1
in {FStar_TypeChecker_Env.solver = _57_2065.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_2065.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_2065.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_2065.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_2065.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_2065.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_2065.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_2065.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_2065.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_2065.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_2065.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_2065.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_2065.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _57_2065.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_2065.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_2065.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_2065.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_2065.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_2065.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_2065.FStar_TypeChecker_Env.use_bv_sorts}) e1)
in (match (_57_2070) with
| (e1, c1, g1) -> begin
(

let _57_2074 = (let _146_741 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _57_2071 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _146_741 e1 c1 wf_annot))
in (match (_57_2074) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _57_2076 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_742 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print1 "checked top-level def, guard is %s\n" _146_742))
end else begin
()
end
in (let _146_743 = (FStar_Option.isSome topt)
in (e1, univ_vars, c1, g1, _146_743))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_2083 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (None, FStar_TypeChecker_Rel.trivial_guard, [], env))
end
| _57_2086 -> begin
(

let _57_2089 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_57_2089) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _146_747 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), FStar_TypeChecker_Rel.trivial_guard, univ_vars, _146_747))
end else begin
(

let _57_2094 = (FStar_Syntax_Util.type_u ())
in (match (_57_2094) with
| (k, _57_2093) -> begin
(

let _57_2099 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_57_2099) with
| (t, _57_2097, g) -> begin
(

let _57_2100 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_750 = (let _146_748 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _146_748))
in (let _146_749 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _146_750 _146_749)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _146_751 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in (Some (t), g, univ_vars, _146_751))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _57_2106 -> (match (_57_2106) with
| (x, imp) -> begin
(

let _57_2109 = (FStar_Syntax_Util.type_u ())
in (match (_57_2109) with
| (tu, u) -> begin
(

let _57_2114 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_57_2114) with
| (t, _57_2112, g) -> begin
(

let x = ((

let _57_2115 = x
in {FStar_Syntax_Syntax.ppname = _57_2115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp)
in (

let _57_2118 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_755 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _146_754 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _146_755 _146_754)))
end else begin
()
end
in (let _146_756 = (maybe_push_binding env x)
in (x, _146_756, g, u))))
end))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe Prims.list) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
([], env, FStar_TypeChecker_Rel.trivial_guard, [])
end
| b::bs -> begin
(

let _57_2133 = (tc_binder env b)
in (match (_57_2133) with
| (b, env', g, u) -> begin
(

let _57_2138 = (aux env' bs)
in (match (_57_2138) with
| (bs, env', g', us) -> begin
(let _146_764 = (let _146_763 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _146_763))
in ((b)::bs, env', _146_764, (u)::us))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _57_2146 _57_2149 -> (match ((_57_2146, _57_2149)) with
| ((t, imp), (args, g)) -> begin
(

let _57_2154 = (tc_term env t)
in (match (_57_2154) with
| (t, _57_2152, g') -> begin
(let _146_773 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((t, imp))::args, _146_773))
end))
end)) args ([], FStar_TypeChecker_Rel.trivial_guard)))
in (FStar_List.fold_right (fun p _57_2158 -> (match (_57_2158) with
| (pats, g) -> begin
(

let _57_2161 = (tc_args env p)
in (match (_57_2161) with
| (args, g') -> begin
(let _146_776 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((args)::pats, _146_776))
end))
end)) pats ([], FStar_TypeChecker_Rel.trivial_guard))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_2167 = (tc_maybe_toplevel_term env e)
in (match (_57_2167) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(e, c, g)
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_2170 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_779 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "About to normalize %s\n" _146_779))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _57_2175 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _146_780 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in (_146_780, false))
end else begin
(let _146_781 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in (_146_781, true))
end
in (match (_57_2175) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _146_782 = (FStar_TypeChecker_Rel.conj_guard g g')
in (e, (FStar_Syntax_Util.lcomp_of_comp target_comp), _146_782))
end
| _57_2179 -> begin
if allow_ghost then begin
(let _146_785 = (let _146_784 = (let _146_783 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in (_146_783, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_784))
in (Prims.raise _146_785))
end else begin
(let _146_788 = (let _146_787 = (let _146_786 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in (_146_786, e.FStar_Syntax_Syntax.pos))
in FStar_Syntax_Syntax.Error (_146_787))
in (Prims.raise _146_788))
end
end)
end))))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))


let tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _57_2189 = (tc_tot_or_gtot_term env t)
in (match (_57_2189) with
| (t, c, g) -> begin
(

let _57_2190 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (t, c))
end)))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _57_2198 = (tc_check_tot_or_gtot_term env t k)
in (match (_57_2198) with
| (t, c, g) -> begin
(

let _57_2199 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _146_808 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _146_808)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _146_812 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in ([], _146_812))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _57_2214 = (tc_binders env tps)
in (match (_57_2214) with
| (tps, env, g, us) -> begin
(

let _57_2215 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (tps, env, us))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _57_2221 -> (match (()) with
| () -> begin
(let _146_827 = (let _146_826 = (let _146_825 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in (_146_825, (FStar_Ident.range_of_lid m)))
in FStar_Syntax_Syntax.Error (_146_826))
in (Prims.raise _146_827))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2238)::(wp, _57_2234)::(_wlp, _57_2230)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2242 -> begin
(fail ())
end))
end
| _57_2244 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _57_2251 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_57_2251) with
| (uvs, c) -> begin
(uvs, [], c)
end))
end
| _57_2253 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _57_2257 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_57_2257) with
| (uvs, t') -> begin
(match ((let _146_834 = (FStar_Syntax_Subst.compress t')
in _146_834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(uvs, binders, c)
end
| _57_2263 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let open_effect_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env mname signature -> (

let fail = (fun t -> (let _146_845 = (let _146_844 = (let _146_843 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in (_146_843, (FStar_Ident.range_of_lid mname)))
in FStar_Syntax_Syntax.Error (_146_844))
in (Prims.raise _146_845)))
in (match ((let _146_846 = (FStar_Syntax_Subst.compress signature)
in _146_846.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| (a, _57_2284)::(wp, _57_2280)::(_wlp, _57_2276)::[] -> begin
(a, wp.FStar_Syntax_Syntax.sort)
end
| _57_2288 -> begin
(fail signature)
end))
end
| _57_2290 -> begin
(fail signature)
end)))


let open_effect_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env ed -> (

let _57_2295 = (open_effect_signature env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_57_2295) with
| (a, wp) -> begin
(

let ed = (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
ed
end
| _57_2298 -> begin
(

let opening = (FStar_Syntax_Subst.opening_of_binders ed.FStar_Syntax_Syntax.binders)
in (

let op = (fun ts -> (

let _57_2302 = ()
in (

let t0 = (Prims.snd ts)
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in ([], t1)))))
in (

let _57_2306 = ed
in (let _146_865 = (op ed.FStar_Syntax_Syntax.ret)
in (let _146_864 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _146_863 = (op ed.FStar_Syntax_Syntax.bind_wlp)
in (let _146_862 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _146_861 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _146_860 = (op ed.FStar_Syntax_Syntax.ite_wlp)
in (let _146_859 = (op ed.FStar_Syntax_Syntax.wp_binop)
in (let _146_858 = (op ed.FStar_Syntax_Syntax.wp_as_type)
in (let _146_857 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _146_856 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _146_855 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _146_854 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _146_853 = (op ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _57_2306.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2306.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2306.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2306.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2306.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _146_865; FStar_Syntax_Syntax.bind_wp = _146_864; FStar_Syntax_Syntax.bind_wlp = _146_863; FStar_Syntax_Syntax.if_then_else = _146_862; FStar_Syntax_Syntax.ite_wp = _146_861; FStar_Syntax_Syntax.ite_wlp = _146_860; FStar_Syntax_Syntax.wp_binop = _146_859; FStar_Syntax_Syntax.wp_as_type = _146_858; FStar_Syntax_Syntax.close_wp = _146_857; FStar_Syntax_Syntax.assert_p = _146_856; FStar_Syntax_Syntax.assume_p = _146_855; FStar_Syntax_Syntax.null_wp = _146_854; FStar_Syntax_Syntax.trivial = _146_853}))))))))))))))))
end)
in (ed, a, wp))
end)))


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env binders a wp_a ed -> (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let normalize_and_make_binders_explicit = (fun tm -> (

let tm = (normalize tm)
in (

let rec visit_term = (fun tm -> (

let n = (match ((let _146_887 = (FStar_Syntax_Subst.compress tm)
in _146_887.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let comp = (visit_comp comp)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(

let comp = (visit_maybe_lcomp comp)
in (

let term = (visit_term term)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_2341 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_2343 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2343.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2343.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2343.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_2347 -> (match (_57_2347) with
| (bv, a) -> begin
(let _146_891 = (

let _57_2348 = bv
in (let _146_889 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_2348.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2348.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_889}))
in (let _146_890 = (FStar_Syntax_Syntax.as_implicit false)
in (_146_891, _146_890)))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _146_896 = (let _146_895 = (let _146_894 = (let _146_893 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _146_893))
in (FStar_Syntax_Util.lcomp_of_comp _146_894))
in FStar_Util.Inl (_146_895))
in Some (_146_896))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _146_898 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_146_898))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _146_899 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_146_899))
end
| comp -> begin
comp
end)
in (

let _57_2362 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_2362.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2362.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2362.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_2367 -> (match (_57_2367) with
| (tm, q) -> begin
(let _146_902 = (visit_term tm)
in (_146_902, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_2371 = (let _146_907 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _146_907))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_2386 = (tc_term env t)
in (match (_57_2386) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_2382; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_2379; FStar_Syntax_Syntax.comp = _57_2377}, _57_2385) -> begin
(

let _57_2387 = (let _146_910 = (let _146_909 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _146_909))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _146_910))
in (let _146_912 = (let _146_911 = (normalize e)
in (FStar_Syntax_Print.term_to_string _146_911))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _146_912)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _146_915 = (FStar_Syntax_Subst.compress t)
in _146_915.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_2398 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _146_916 = (collect_binders rest)
in (FStar_List.append bs _146_916)))
end
| FStar_Syntax_Syntax.Tm_type (_57_2401) -> begin
[]
end
| _57_2404 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_2419 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _146_923 = (normalize wp_a)
in (collect_binders _146_923))
in ((fun t -> (let _146_929 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _146_929))), (fun t -> (let _146_932 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _146_932))), (fun _57_2409 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_2413 -> (match (_57_2413) with
| (bv, _57_2412) -> begin
(

let _57_2414 = (let _146_936 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _146_936))
in (let _146_939 = (let _146_938 = (let _146_937 = (FStar_ST.read i)
in (FStar_Util.string_of_int _146_937))
in (Prims.strcat "g" _146_938))
in (FStar_Syntax_Syntax.gen_bv _146_939 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_2419) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_2422 -> (match (_57_2422) with
| (t, b) -> begin
(let _146_945 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _146_945))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _146_948 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _146_948))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _146_951 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _146_951))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _146_952 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _146_952))
in (

let ret = (let _146_957 = (let _146_956 = (let _146_955 = (let _146_954 = (let _146_953 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _146_953))
in (FStar_Syntax_Syntax.mk_Total _146_954))
in (FStar_Syntax_Util.lcomp_of_comp _146_955))
in FStar_Util.Inl (_146_956))
in Some (_146_957))
in (

let gamma = (mk_gamma ())
in (

let body = (let _146_959 = (implicit_binders_of_list gamma)
in (let _146_958 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _146_959 _146_958 ret)))
in (let _146_960 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _146_960 body ret)))))))
in (

let _57_2434 = (let _146_964 = (let _146_963 = (let _146_962 = (let _146_961 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_961)::[])
in (FStar_List.append binders _146_962))
in (FStar_Syntax_Util.abs _146_963 c_pure None))
in (check "pure" _146_964))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _146_972 = (let _146_971 = (let _146_970 = (let _146_967 = (let _146_966 = (let _146_965 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _146_965))
in (FStar_Syntax_Syntax.mk_binder _146_966))
in (_146_967)::[])
in (let _146_969 = (let _146_968 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_968))
in (FStar_Syntax_Util.arrow _146_970 _146_969)))
in (mk_gctx _146_971))
in (FStar_Syntax_Syntax.gen_bv "l" None _146_972))
in (

let r = (let _146_974 = (let _146_973 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_973))
in (FStar_Syntax_Syntax.gen_bv "r" None _146_974))
in (

let ret = (let _146_979 = (let _146_978 = (let _146_977 = (let _146_976 = (let _146_975 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_975))
in (FStar_Syntax_Syntax.mk_Total _146_976))
in (FStar_Syntax_Util.lcomp_of_comp _146_977))
in FStar_Util.Inl (_146_978))
in Some (_146_979))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _146_985 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_984 = (let _146_983 = (let _146_982 = (let _146_981 = (let _146_980 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _146_980 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _146_981))
in (_146_982)::[])
in (FStar_List.append gamma_as_args _146_983))
in (FStar_Syntax_Util.mk_app _146_985 _146_984)))
in (let _146_986 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _146_986 inner_body ret)))))
in (let _146_987 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _146_987 outer_body ret))))))))
in (

let _57_2446 = (let _146_991 = (let _146_990 = (let _146_989 = (let _146_988 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_988)::[])
in (FStar_List.append binders _146_989))
in (FStar_Syntax_Util.abs _146_990 c_app None))
in (check "app" _146_991))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_996 = (let _146_993 = (let _146_992 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_992))
in (_146_993)::[])
in (let _146_995 = (let _146_994 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_994))
in (FStar_Syntax_Util.arrow _146_996 _146_995)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _146_998 = (let _146_997 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_997))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_998))
in (

let ret = (let _146_1003 = (let _146_1002 = (let _146_1001 = (let _146_1000 = (let _146_999 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_999))
in (FStar_Syntax_Syntax.mk_Total _146_1000))
in (FStar_Syntax_Util.lcomp_of_comp _146_1001))
in FStar_Util.Inl (_146_1002))
in Some (_146_1003))
in (let _146_1016 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
in (let _146_1015 = (let _146_1014 = (let _146_1013 = (let _146_1012 = (let _146_1011 = (let _146_1010 = (let _146_1007 = (let _146_1006 = (let _146_1005 = (let _146_1004 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1004)::[])
in (unknown)::_146_1005)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1006))
in (FStar_Syntax_Util.mk_app c_pure _146_1007))
in (let _146_1009 = (let _146_1008 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1008)::[])
in (_146_1010)::_146_1009))
in (unknown)::_146_1011)
in (unknown)::_146_1012)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1013))
in (FStar_Syntax_Util.mk_app c_app _146_1014))
in (FStar_Syntax_Util.abs _146_1016 _146_1015 ret)))))))))
in (

let _57_2456 = (let _146_1020 = (let _146_1019 = (let _146_1018 = (let _146_1017 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1017)::[])
in (FStar_List.append binders _146_1018))
in (FStar_Syntax_Util.abs _146_1019 c_lift1 None))
in (check "lift1" _146_1020))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_1028 = (let _146_1025 = (let _146_1021 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1021))
in (let _146_1024 = (let _146_1023 = (let _146_1022 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _146_1022))
in (_146_1023)::[])
in (_146_1025)::_146_1024))
in (let _146_1027 = (let _146_1026 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _146_1026))
in (FStar_Syntax_Util.arrow _146_1028 _146_1027)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _146_1030 = (let _146_1029 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _146_1029))
in (FStar_Syntax_Syntax.gen_bv "a1" None _146_1030))
in (

let a2 = (let _146_1032 = (let _146_1031 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1031))
in (FStar_Syntax_Syntax.gen_bv "a2" None _146_1032))
in (

let ret = (let _146_1037 = (let _146_1036 = (let _146_1035 = (let _146_1034 = (let _146_1033 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _146_1033))
in (FStar_Syntax_Syntax.mk_Total _146_1034))
in (FStar_Syntax_Util.lcomp_of_comp _146_1035))
in FStar_Util.Inl (_146_1036))
in Some (_146_1037))
in (let _146_1057 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
in (let _146_1056 = (let _146_1055 = (let _146_1054 = (let _146_1053 = (let _146_1052 = (let _146_1051 = (let _146_1048 = (let _146_1047 = (let _146_1046 = (let _146_1045 = (let _146_1044 = (let _146_1041 = (let _146_1040 = (let _146_1039 = (let _146_1038 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1038)::[])
in (unknown)::_146_1039)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1040))
in (FStar_Syntax_Util.mk_app c_pure _146_1041))
in (let _146_1043 = (let _146_1042 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_146_1042)::[])
in (_146_1044)::_146_1043))
in (unknown)::_146_1045)
in (unknown)::_146_1046)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1047))
in (FStar_Syntax_Util.mk_app c_app _146_1048))
in (let _146_1050 = (let _146_1049 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_146_1049)::[])
in (_146_1051)::_146_1050))
in (unknown)::_146_1052)
in (unknown)::_146_1053)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1054))
in (FStar_Syntax_Util.mk_app c_app _146_1055))
in (FStar_Syntax_Util.abs _146_1057 _146_1056 ret)))))))))))
in (

let _57_2467 = (let _146_1061 = (let _146_1060 = (let _146_1059 = (let _146_1058 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1058)::[])
in (FStar_List.append binders _146_1059))
in (FStar_Syntax_Util.abs _146_1060 c_lift2 None))
in (check "lift2" _146_1061))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_1067 = (let _146_1063 = (let _146_1062 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1062))
in (_146_1063)::[])
in (let _146_1066 = (let _146_1065 = (let _146_1064 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _146_1064))
in (FStar_Syntax_Syntax.mk_Total _146_1065))
in (FStar_Syntax_Util.arrow _146_1067 _146_1066)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _146_1077 = (let _146_1076 = (let _146_1075 = (let _146_1074 = (let _146_1073 = (let _146_1072 = (let _146_1069 = (let _146_1068 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _146_1068))
in (_146_1069)::[])
in (let _146_1071 = (let _146_1070 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _146_1070))
in (FStar_Syntax_Util.arrow _146_1072 _146_1071)))
in (mk_ctx _146_1073))
in (FStar_Syntax_Syntax.mk_Total _146_1074))
in (FStar_Syntax_Util.lcomp_of_comp _146_1075))
in FStar_Util.Inl (_146_1076))
in Some (_146_1077))
in (

let e1 = (let _146_1078 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _146_1078))
in (

let gamma = (mk_gamma ())
in (

let body = (let _146_1088 = (let _146_1081 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _146_1080 = (let _146_1079 = (FStar_Syntax_Syntax.mk_binder e1)
in (_146_1079)::[])
in (FStar_List.append _146_1081 _146_1080)))
in (let _146_1087 = (let _146_1086 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _146_1085 = (let _146_1084 = (let _146_1082 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _146_1082))
in (let _146_1083 = (args_of_bv gamma)
in (_146_1084)::_146_1083))
in (FStar_Syntax_Util.mk_app _146_1086 _146_1085)))
in (FStar_Syntax_Util.abs _146_1088 _146_1087 ret)))
in (let _146_1089 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _146_1089 body ret))))))))))
in (

let _57_2478 = (let _146_1093 = (let _146_1092 = (let _146_1091 = (let _146_1090 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1090)::[])
in (FStar_List.append binders _146_1091))
in (FStar_Syntax_Util.abs _146_1092 c_push None))
in (check "push" _146_1093))
in (

let ret_tot_wp_a = (let _146_1096 = (let _146_1095 = (let _146_1094 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _146_1094))
in FStar_Util.Inl (_146_1095))
in Some (_146_1096))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _146_1107 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _146_1106 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _146_1105 = (let _146_1104 = (let _146_1103 = (let _146_1102 = (let _146_1101 = (let _146_1100 = (let _146_1099 = (let _146_1098 = (let _146_1097 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _146_1097))
in (_146_1098)::[])
in (FStar_Syntax_Util.mk_app l_ite _146_1099))
in (_146_1100)::[])
in (unknown)::_146_1101)
in (unknown)::_146_1102)
in (unknown)::_146_1103)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1104))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1105)))
in (FStar_Syntax_Util.abs _146_1107 _146_1106 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_2485 = (let _146_1108 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _146_1108))
in (

let wp_binop = (

let l = (FStar_Syntax_Syntax.gen_bv "l" None wp_a)
in (

let op = (let _146_1114 = (let _146_1113 = (let _146_1111 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (let _146_1110 = (let _146_1109 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.ktype0)
in (_146_1109)::[])
in (_146_1111)::_146_1110))
in (let _146_1112 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_1113 _146_1112)))
in (FStar_Syntax_Syntax.gen_bv "op" None _146_1114))
in (

let r = (FStar_Syntax_Syntax.gen_bv "r" None wp_a)
in (let _146_1126 = (FStar_Syntax_Syntax.binders_of_list ((a)::(l)::(op)::(r)::[]))
in (let _146_1125 = (let _146_1124 = (let _146_1123 = (let _146_1122 = (let _146_1121 = (let _146_1120 = (let _146_1119 = (FStar_Syntax_Syntax.bv_to_name op)
in (let _146_1118 = (let _146_1117 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _146_1116 = (let _146_1115 = (FStar_Syntax_Syntax.bv_to_name r)
in (_146_1115)::[])
in (_146_1117)::_146_1116))
in (_146_1119)::_146_1118))
in (unknown)::_146_1120)
in (unknown)::_146_1121)
in (unknown)::_146_1122)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1123))
in (FStar_Syntax_Util.mk_app c_lift2 _146_1124))
in (FStar_Syntax_Util.abs _146_1126 _146_1125 ret_tot_wp_a))))))
in (

let wp_binop = (normalize_and_make_binders_explicit wp_binop)
in (

let _57_2492 = (let _146_1127 = (FStar_Syntax_Util.abs binders wp_binop None)
in (check "wp_binop" _146_1127))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _146_1141 = (let _146_1140 = (let _146_1139 = (let _146_1138 = (let _146_1137 = (let _146_1134 = (let _146_1133 = (let _146_1132 = (let _146_1131 = (let _146_1130 = (let _146_1129 = (let _146_1128 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1128))
in (_146_1129)::[])
in (FStar_Syntax_Util.mk_app l_and _146_1130))
in (_146_1131)::[])
in (unknown)::_146_1132)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1133))
in (FStar_Syntax_Util.mk_app c_pure _146_1134))
in (let _146_1136 = (let _146_1135 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1135)::[])
in (_146_1137)::_146_1136))
in (unknown)::_146_1138)
in (unknown)::_146_1139)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1140))
in (FStar_Syntax_Util.mk_app c_app _146_1141))
in (let _146_1142 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1142 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_2500 = (let _146_1143 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _146_1143))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _146_1157 = (let _146_1156 = (let _146_1155 = (let _146_1154 = (let _146_1153 = (let _146_1150 = (let _146_1149 = (let _146_1148 = (let _146_1147 = (let _146_1146 = (let _146_1145 = (let _146_1144 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _146_1144))
in (_146_1145)::[])
in (FStar_Syntax_Util.mk_app l_imp _146_1146))
in (_146_1147)::[])
in (unknown)::_146_1148)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1149))
in (FStar_Syntax_Util.mk_app c_pure _146_1150))
in (let _146_1152 = (let _146_1151 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1151)::[])
in (_146_1153)::_146_1152))
in (unknown)::_146_1154)
in (unknown)::_146_1155)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1156))
in (FStar_Syntax_Util.mk_app c_app _146_1157))
in (let _146_1158 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1158 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_2508 = (let _146_1159 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _146_1159))
in (

let tforall = (let _146_1162 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1161 = (let _146_1160 = (FStar_Syntax_Syntax.as_arg unknown)
in (_146_1160)::[])
in (FStar_Syntax_Util.mk_app _146_1162 _146_1161)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _146_1166 = (let _146_1164 = (let _146_1163 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1163))
in (_146_1164)::[])
in (let _146_1165 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1166 _146_1165)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _146_1179 = (let _146_1178 = (let _146_1177 = (let _146_1176 = (let _146_1175 = (let _146_1167 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _146_1167))
in (let _146_1174 = (let _146_1173 = (let _146_1172 = (let _146_1171 = (let _146_1170 = (let _146_1169 = (let _146_1168 = (FStar_Syntax_Syntax.bv_to_name f)
in (_146_1168)::[])
in (unknown)::_146_1169)
in (unknown)::_146_1170)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1171))
in (FStar_Syntax_Util.mk_app c_push _146_1172))
in (_146_1173)::[])
in (_146_1175)::_146_1174))
in (unknown)::_146_1176)
in (unknown)::_146_1177)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1178))
in (FStar_Syntax_Util.mk_app c_app _146_1179))
in (let _146_1180 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _146_1180 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_2517 = (let _146_1181 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _146_1181))
in (

let ret_tot_type0 = (let _146_1184 = (let _146_1183 = (let _146_1182 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1182))
in FStar_Util.Inl (_146_1183))
in Some (_146_1184))
in (

let mk_forall = (fun x body -> (

let tforall = (let _146_1191 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _146_1190 = (let _146_1189 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_146_1189)::[])
in (FStar_Syntax_Util.mk_app _146_1191 _146_1190)))
in (let _146_1198 = (let _146_1197 = (let _146_1196 = (let _146_1195 = (let _146_1194 = (let _146_1193 = (let _146_1192 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1192)::[])
in (FStar_Syntax_Util.abs _146_1193 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _146_1194))
in (_146_1195)::[])
in (tforall, _146_1196))
in FStar_Syntax_Syntax.Tm_app (_146_1197))
in (FStar_Syntax_Syntax.mk _146_1198 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _146_1206 = (let _146_1205 = (FStar_Syntax_Subst.compress t)
in (normalize _146_1205))
in _146_1206.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_2529) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binder::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _146_1218 = (let _146_1208 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _146_1207 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _146_1208 _146_1207)))
in (let _146_1217 = (let _146_1216 = (let _146_1211 = (let _146_1210 = (let _146_1209 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _146_1209))
in (_146_1210)::[])
in (FStar_Syntax_Util.mk_app x _146_1211))
in (let _146_1215 = (let _146_1214 = (let _146_1213 = (let _146_1212 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _146_1212))
in (_146_1213)::[])
in (FStar_Syntax_Util.mk_app y _146_1214))
in (mk_leq b _146_1216 _146_1215)))
in (FStar_Syntax_Util.mk_imp _146_1218 _146_1217)))
in (let _146_1219 = (mk_forall a2 body)
in (mk_forall a1 _146_1219))))))
end
| FStar_Syntax_Syntax.Tm_arrow (binder::binders, comp) -> begin
(

let t = (

let _57_2565 = t
in (let _146_1223 = (let _146_1222 = (let _146_1221 = (let _146_1220 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _146_1220))
in ((binder)::[], _146_1221))
in FStar_Syntax_Syntax.Tm_arrow (_146_1222))
in {FStar_Syntax_Syntax.n = _146_1223; FStar_Syntax_Syntax.tk = _57_2565.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_2565.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_2565.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_2569) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_2572 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _146_1225 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _146_1224 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _146_1225 _146_1224)))
in (let _146_1226 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _146_1226 body ret_tot_type0)))))
in (

let _57_2577 = (let _146_1230 = (let _146_1229 = (let _146_1228 = (let _146_1227 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1227)::[])
in (FStar_List.append binders _146_1228))
in (FStar_Syntax_Util.abs _146_1229 stronger None))
in (check "stronger" _146_1230))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _146_1238 = (let _146_1237 = (let _146_1236 = (let _146_1233 = (let _146_1232 = (let _146_1231 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _146_1231))
in (_146_1232)::[])
in (FStar_Syntax_Util.mk_app null_wp _146_1233))
in (let _146_1235 = (let _146_1234 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_146_1234)::[])
in (_146_1236)::_146_1235))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _146_1237))
in (FStar_Syntax_Util.mk_app stronger _146_1238))
in (let _146_1239 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _146_1239 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_2584 = (let _146_1240 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _146_1240))
in (

let _57_2586 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2586.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2586.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2586.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_2586.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_2586.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret = _57_2586.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2586.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2586.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_2586.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2586.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = ([], wp_binop); FStar_Syntax_Syntax.wp_as_type = _57_2586.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_2586.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial)})))))))))))))))))))))))))))))))))))))))))
end))))))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  effect_cost  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed is_for_free -> (

let _57_2591 = ()
in (

let _57_2595 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_57_2595) with
| (binders_un, signature_un) -> begin
(

let _57_2600 = (tc_tparams env0 binders_un)
in (match (_57_2600) with
| (binders, env, _57_2599) -> begin
(

let _57_2604 = (tc_trivial_guard env signature_un)
in (match (_57_2604) with
| (signature, _57_2603) -> begin
(

let ed = (

let _57_2605 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_2605.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2605.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_2605.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _57_2605.FStar_Syntax_Syntax.ret; FStar_Syntax_Syntax.bind_wp = _57_2605.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.bind_wlp = _57_2605.FStar_Syntax_Syntax.bind_wlp; FStar_Syntax_Syntax.if_then_else = _57_2605.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _57_2605.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.ite_wlp = _57_2605.FStar_Syntax_Syntax.ite_wlp; FStar_Syntax_Syntax.wp_binop = _57_2605.FStar_Syntax_Syntax.wp_binop; FStar_Syntax_Syntax.wp_as_type = _57_2605.FStar_Syntax_Syntax.wp_as_type; FStar_Syntax_Syntax.close_wp = _57_2605.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _57_2605.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _57_2605.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _57_2605.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_2605.FStar_Syntax_Syntax.trivial})
in (

let _57_2611 = (open_effect_decl env ed)
in (match (_57_2611) with
| (ed, a, wp_a) -> begin
(

let get_effect_signature = (fun _57_2613 -> (match (()) with
| () -> begin
(

let _57_2617 = (tc_trivial_guard env signature_un)
in (match (_57_2617) with
| (signature, _57_2616) -> begin
(open_effect_signature env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _146_1249 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _146_1249))
in (

let _57_2619 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _146_1252 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _146_1251 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _146_1250 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (FStar_Util.print3 "Checking effect signature: %s %s : %s\n" _146_1252 _146_1251 _146_1250))))
end else begin
()
end
in (

let check_and_gen' = (fun env _57_2626 k -> (match (_57_2626) with
| (_57_2624, t) -> begin
(check_and_gen env t k)
end))
in (

let ed = (match (is_for_free) with
| NotForFree -> begin
ed
end
| ForFree -> begin
(gen_wps_for_free env binders a wp_a ed)
end)
in (

let ret = (

let expected_k = (let _146_1264 = (let _146_1262 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1261 = (let _146_1260 = (let _146_1259 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1259))
in (_146_1260)::[])
in (_146_1262)::_146_1261))
in (let _146_1263 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _146_1264 _146_1263)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret expected_k))
in (

let bind_wp = (

let wlp_a = wp_a
in (

let _57_2636 = (get_effect_signature ())
in (match (_57_2636) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _146_1268 = (let _146_1266 = (let _146_1265 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1265))
in (_146_1266)::[])
in (let _146_1267 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1268 _146_1267)))
in (

let a_wlp_b = a_wp_b
in (

let expected_k = (let _146_1283 = (let _146_1281 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1280 = (let _146_1279 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1278 = (let _146_1277 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1276 = (let _146_1275 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1274 = (let _146_1273 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1272 = (let _146_1271 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (let _146_1270 = (let _146_1269 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1269)::[])
in (_146_1271)::_146_1270))
in (_146_1273)::_146_1272))
in (_146_1275)::_146_1274))
in (_146_1277)::_146_1276))
in (_146_1279)::_146_1278))
in (_146_1281)::_146_1280))
in (let _146_1282 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _146_1283 _146_1282)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k))))
end)))
in (

let bind_wlp = (

let wlp_a = wp_a
in (

let _57_2644 = (get_effect_signature ())
in (match (_57_2644) with
| (b, wlp_b) -> begin
(

let a_wlp_b = (let _146_1287 = (let _146_1285 = (let _146_1284 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _146_1284))
in (_146_1285)::[])
in (let _146_1286 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1287 _146_1286)))
in (

let expected_k = (let _146_1298 = (let _146_1296 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _146_1295 = (let _146_1294 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1293 = (let _146_1292 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1291 = (let _146_1290 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1289 = (let _146_1288 = (FStar_Syntax_Syntax.null_binder a_wlp_b)
in (_146_1288)::[])
in (_146_1290)::_146_1289))
in (_146_1292)::_146_1291))
in (_146_1294)::_146_1293))
in (_146_1296)::_146_1295))
in (let _146_1297 = (FStar_Syntax_Syntax.mk_Total wlp_b)
in (FStar_Syntax_Util.arrow _146_1298 _146_1297)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wlp expected_k)))
end)))
in (

let if_then_else = (

let p = (let _146_1300 = (let _146_1299 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1299 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1300))
in (

let expected_k = (let _146_1309 = (let _146_1307 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1306 = (let _146_1305 = (FStar_Syntax_Syntax.mk_binder p)
in (let _146_1304 = (let _146_1303 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1302 = (let _146_1301 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1301)::[])
in (_146_1303)::_146_1302))
in (_146_1305)::_146_1304))
in (_146_1307)::_146_1306))
in (let _146_1308 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1309 _146_1308)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let wlp_a = wp_a
in (

let expected_k = (let _146_1316 = (let _146_1314 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1313 = (let _146_1312 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (let _146_1311 = (let _146_1310 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1310)::[])
in (_146_1312)::_146_1311))
in (_146_1314)::_146_1313))
in (let _146_1315 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1316 _146_1315)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k)))
in (

let ite_wlp = (

let wlp_a = wp_a
in (

let expected_k = (let _146_1321 = (let _146_1319 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1318 = (let _146_1317 = (FStar_Syntax_Syntax.null_binder wlp_a)
in (_146_1317)::[])
in (_146_1319)::_146_1318))
in (let _146_1320 = (FStar_Syntax_Syntax.mk_Total wlp_a)
in (FStar_Syntax_Util.arrow _146_1321 _146_1320)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wlp expected_k)))
in (

let wp_binop = (

let bin_op = (

let _57_2659 = (FStar_Syntax_Util.type_u ())
in (match (_57_2659) with
| (t1, u1) -> begin
(

let _57_2662 = (FStar_Syntax_Util.type_u ())
in (match (_57_2662) with
| (t2, u2) -> begin
(

let t = (let _146_1322 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_max ((u1)::(u2)::[]))) None _146_1322))
in (let _146_1327 = (let _146_1325 = (FStar_Syntax_Syntax.null_binder t1)
in (let _146_1324 = (let _146_1323 = (FStar_Syntax_Syntax.null_binder t2)
in (_146_1323)::[])
in (_146_1325)::_146_1324))
in (let _146_1326 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1327 _146_1326))))
end))
end))
in (

let expected_k = (let _146_1336 = (let _146_1334 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1333 = (let _146_1332 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _146_1331 = (let _146_1330 = (FStar_Syntax_Syntax.null_binder bin_op)
in (let _146_1329 = (let _146_1328 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1328)::[])
in (_146_1330)::_146_1329))
in (_146_1332)::_146_1331))
in (_146_1334)::_146_1333))
in (let _146_1335 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1336 _146_1335)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_binop expected_k)))
in (

let wp_as_type = (

let _57_2670 = (FStar_Syntax_Util.type_u ())
in (match (_57_2670) with
| (t, _57_2669) -> begin
(

let expected_k = (let _146_1341 = (let _146_1339 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1338 = (let _146_1337 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1337)::[])
in (_146_1339)::_146_1338))
in (let _146_1340 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _146_1341 _146_1340)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.wp_as_type expected_k))
end))
in (

let close_wp = (

let b = (let _146_1343 = (let _146_1342 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1342 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _146_1343))
in (

let b_wp_a = (let _146_1347 = (let _146_1345 = (let _146_1344 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _146_1344))
in (_146_1345)::[])
in (let _146_1346 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1347 _146_1346)))
in (

let expected_k = (let _146_1354 = (let _146_1352 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1351 = (let _146_1350 = (FStar_Syntax_Syntax.mk_binder b)
in (let _146_1349 = (let _146_1348 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_146_1348)::[])
in (_146_1350)::_146_1349))
in (_146_1352)::_146_1351))
in (let _146_1353 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1354 _146_1353)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _146_1363 = (let _146_1361 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1360 = (let _146_1359 = (let _146_1356 = (let _146_1355 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1355 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1356))
in (let _146_1358 = (let _146_1357 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1357)::[])
in (_146_1359)::_146_1358))
in (_146_1361)::_146_1360))
in (let _146_1362 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1363 _146_1362)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _146_1372 = (let _146_1370 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1369 = (let _146_1368 = (let _146_1365 = (let _146_1364 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1364 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _146_1365))
in (let _146_1367 = (let _146_1366 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1366)::[])
in (_146_1368)::_146_1367))
in (_146_1370)::_146_1369))
in (let _146_1371 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1372 _146_1371)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _146_1375 = (let _146_1373 = (FStar_Syntax_Syntax.mk_binder a)
in (_146_1373)::[])
in (let _146_1374 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _146_1375 _146_1374)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _57_2686 = (FStar_Syntax_Util.type_u ())
in (match (_57_2686) with
| (t, _57_2685) -> begin
(

let expected_k = (let _146_1380 = (let _146_1378 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1377 = (let _146_1376 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_146_1376)::[])
in (_146_1378)::_146_1377))
in (let _146_1379 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _146_1380 _146_1379)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let t = (let _146_1381 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _146_1381))
in (

let _57_2692 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_57_2692) with
| (univs, t) -> begin
(

let _57_2708 = (match ((let _146_1383 = (let _146_1382 = (FStar_Syntax_Subst.compress t)
in _146_1382.FStar_Syntax_Syntax.n)
in (binders, _146_1383))) with
| ([], _57_2695) -> begin
([], t)
end
| (_57_2698, FStar_Syntax_Syntax.Tm_arrow (binders, c)) -> begin
(binders, (FStar_Syntax_Util.comp_result c))
end
| _57_2705 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_2708) with
| (binders, signature) -> begin
(

let close = (fun n ts -> (

let ts = (let _146_1388 = (FStar_Syntax_Subst.close_tscheme binders ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _146_1388))
in (

let _57_2713 = ()
in ts)))
in (

let ed = (

let _57_2715 = ed
in (let _146_1401 = (close 0 ret)
in (let _146_1400 = (close 1 bind_wp)
in (let _146_1399 = (close 1 bind_wlp)
in (let _146_1398 = (close 0 if_then_else)
in (let _146_1397 = (close 0 ite_wp)
in (let _146_1396 = (close 0 ite_wlp)
in (let _146_1395 = (close 0 wp_binop)
in (let _146_1394 = (close 0 wp_as_type)
in (let _146_1393 = (close 1 close_wp)
in (let _146_1392 = (close 0 assert_p)
in (let _146_1391 = (close 0 assume_p)
in (let _146_1390 = (close 0 null_wp)
in (let _146_1389 = (close 0 trivial_wp)
in {FStar_Syntax_Syntax.qualifiers = _57_2715.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_2715.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret = _146_1401; FStar_Syntax_Syntax.bind_wp = _146_1400; FStar_Syntax_Syntax.bind_wlp = _146_1399; FStar_Syntax_Syntax.if_then_else = _146_1398; FStar_Syntax_Syntax.ite_wp = _146_1397; FStar_Syntax_Syntax.ite_wlp = _146_1396; FStar_Syntax_Syntax.wp_binop = _146_1395; FStar_Syntax_Syntax.wp_as_type = _146_1394; FStar_Syntax_Syntax.close_wp = _146_1393; FStar_Syntax_Syntax.assert_p = _146_1392; FStar_Syntax_Syntax.assume_p = _146_1391; FStar_Syntax_Syntax.null_wp = _146_1390; FStar_Syntax_Syntax.trivial = _146_1389}))))))))))))))
in (

let _57_2718 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1402 = (FStar_Syntax_Print.eff_decl_to_string ed)
in (FStar_Util.print_string _146_1402))
end else begin
()
end
in ed)))
end))
end)))))))))))))))))))))
end)))
end))
end))
end))))


let tc_lex_t = (fun env ses quals lids -> (

let _57_2724 = ()
in (

let _57_2732 = ()
in (match (ses) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _57_2761, _57_2763, [], r)::FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, 0, [], _57_2752, r1)::FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, 0, [], _57_2741, r2)::[] when (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid)) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ ((lex_t, (u)::[], [], t, [], (FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[], [], r))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (let _146_1410 = (let _146_1409 = (let _146_1408 = (let _146_1407 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _146_1407 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1408, (FStar_Syntax_Syntax.U_name (utop))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1409))
in (FStar_Syntax_Syntax.mk _146_1410 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon ((lex_top, (utop)::[], lex_top_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r1))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _146_1411 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1411))
in (

let hd = (let _146_1412 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1412))
in (

let tl = (let _146_1417 = (let _146_1416 = (let _146_1415 = (let _146_1414 = (let _146_1413 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1413 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1414, (FStar_Syntax_Syntax.U_name (ucons2))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1415))
in (FStar_Syntax_Syntax.mk _146_1416 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _146_1417))
in (

let res = (let _146_1421 = (let _146_1420 = (let _146_1419 = (let _146_1418 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _146_1418 FStar_Syntax_Syntax.Delta_constant None))
in (_146_1419, (FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[]))
in FStar_Syntax_Syntax.Tm_uinst (_146_1420))
in (FStar_Syntax_Syntax.mk _146_1421 None r2))
in (let _146_1422 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow (((a, Some (FStar_Syntax_Syntax.imp_tag)))::((hd, None))::((tl, None))::[]) _146_1422))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon ((lex_cons, (ucons1)::(ucons2)::[], lex_cons_t, FStar_Syntax_Const.lex_t_lid, 0, [], [], r2))
in (let _146_1424 = (let _146_1423 = (FStar_TypeChecker_Env.get_range env)
in ((tc)::(dc_lextop)::(dc_lexcons)::[], [], lids, _146_1423))
in FStar_Syntax_Syntax.Sig_bundle (_146_1424)))))))))))))))
end
| _57_2787 -> begin
(let _146_1426 = (let _146_1425 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle ((ses, [], lids, FStar_Range.dummyRange))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _146_1425))
in (FStar_All.failwith _146_1426))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _146_1440 = (let _146_1439 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _146_1439))
in (FStar_TypeChecker_Errors.diag r _146_1440)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _57_2809 = ()
in (

let _57_2811 = (warn_positivity tc r)
in (

let _57_2815 = (FStar_Syntax_Subst.open_term tps k)
in (match (_57_2815) with
| (tps, k) -> begin
(

let _57_2819 = (tc_tparams env tps)
in (match (_57_2819) with
| (tps, env_tps, us) -> begin
(

let _57_2822 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2822) with
| (indices, t) -> begin
(

let _57_2826 = (tc_tparams env_tps indices)
in (match (_57_2826) with
| (indices, env', us') -> begin
(

let _57_2830 = (tc_trivial_guard env' t)
in (match (_57_2830) with
| (t, _57_2829) -> begin
(

let k = (let _146_1445 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _146_1445))
in (

let _57_2834 = (FStar_Syntax_Util.type_u ())
in (match (_57_2834) with
| (t_type, u) -> begin
(

let _57_2835 = (let _146_1446 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _146_1446))
in (

let t_tc = (let _146_1447 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _146_1447))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _146_1448 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) ([], t_tc))
in (_146_1448, FStar_Syntax_Syntax.Sig_inductive_typ ((tc, [], tps, k, mutuals, data, quals, r)), u)))))))
end)))
end))
end))
end))
end))
end))))
end
| _57_2842 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _57_2844 l -> ())
in (

let tc_data = (fun env tcs _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _57_2861 = ()
in (

let _57_2896 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _57_2865 -> (match (_57_2865) with
| (se, u_tc) -> begin
if (let _146_1461 = (let _146_1460 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _146_1460))
in (FStar_Ident.lid_equals tc_lid _146_1461)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2867, _57_2869, tps, _57_2872, _57_2874, _57_2876, _57_2878, _57_2880) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _57_2886 -> (match (_57_2886) with
| (x, _57_2885) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
end
| _57_2888 -> begin
(FStar_All.failwith "Impossible")
end)
in Some ((tps, u_tc)))
end else begin
None
end
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
if (FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid) then begin
([], FStar_Syntax_Syntax.U_zero)
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected data constructor", r))))
end
end))
in (match (_57_2896) with
| (tps, u_tc) -> begin
(

let _57_2916 = (match ((let _146_1463 = (FStar_Syntax_Subst.compress t)
in _146_1463.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _57_2904 = (FStar_Util.first_N ntps bs)
in (match (_57_2904) with
| (_57_2902, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs', res))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _57_2910 -> (match (_57_2910) with
| (x, _57_2909) -> begin
FStar_Syntax_Syntax.Index2Name (((ntps - (1 + i)), x))
end))))
in (let _146_1466 = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Renaming (subst)) t)
in (FStar_Syntax_Util.arrow_formals _146_1466))))
end))
end
| _57_2913 -> begin
([], t)
end)
in (match (_57_2916) with
| (arguments, result) -> begin
(

let _57_2917 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1469 = (FStar_Syntax_Print.lid_to_string c)
in (let _146_1468 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _146_1467 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _146_1469 _146_1468 _146_1467))))
end else begin
()
end
in (

let _57_2922 = (tc_tparams env arguments)
in (match (_57_2922) with
| (arguments, env', us) -> begin
(

let _57_2926 = (tc_trivial_guard env' result)
in (match (_57_2926) with
| (result, _57_2925) -> begin
(

let _57_2930 = (FStar_Syntax_Util.head_and_args result)
in (match (_57_2930) with
| (head, _57_2929) -> begin
(

let _57_2935 = (match ((let _146_1470 = (FStar_Syntax_Subst.compress head)
in _146_1470.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _57_2934 -> begin
(let _146_1474 = (let _146_1473 = (let _146_1472 = (let _146_1471 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (FStar_Util.format1 "Expected a constructor of type %s" _146_1471))
in (_146_1472, r))
in FStar_Syntax_Syntax.Error (_146_1473))
in (Prims.raise _146_1474))
end)
in (

let g = (FStar_List.fold_left2 (fun g _57_2941 u_x -> (match (_57_2941) with
| (x, _57_2940) -> begin
(

let _57_2943 = ()
in (let _146_1478 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _146_1478)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _146_1482 = (let _146_1480 = (FStar_All.pipe_right tps (FStar_List.map (fun _57_2949 -> (match (_57_2949) with
| (x, _57_2948) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end))))
in (FStar_List.append _146_1480 arguments))
in (let _146_1481 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _146_1482 _146_1481)))
in (FStar_Syntax_Syntax.Sig_datacon ((c, [], t, tc_lid, ntps, quals, [], r)), g))))
end))
end))
end)))
end))
end)))
end
| _57_2952 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _57_2958 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_7 -> (match (_57_7) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2962, _57_2964, tps, k, _57_2968, _57_2970, _57_2972, _57_2974) -> begin
(let _146_1493 = (let _146_1492 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _146_1492))
in (FStar_Syntax_Syntax.null_binder _146_1493))
end
| _57_2978 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.Sig_datacon (_57_2982, _57_2984, t, _57_2987, _57_2989, _57_2991, _57_2993, _57_2995) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _57_2999 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _146_1495 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _146_1495))
in (

let _57_3002 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1496 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _146_1496))
end else begin
()
end
in (

let _57_3006 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_57_3006) with
| (uvs, t) -> begin
(

let _57_3008 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1500 = (let _146_1498 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _146_1498 (FStar_String.concat ", ")))
in (let _146_1499 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _146_1500 _146_1499)))
end else begin
()
end
in (

let _57_3012 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_57_3012) with
| (uvs, t) -> begin
(

let _57_3016 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_3016) with
| (args, _57_3015) -> begin
(

let _57_3019 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_57_3019) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _57_3023 se -> (match (_57_3023) with
| (x, _57_3022) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3027, tps, _57_3030, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _57_3053 = (match ((let _146_1503 = (FStar_Syntax_Subst.compress ty)
in _146_1503.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _57_3044 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_57_3044) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_3047 -> begin
(let _146_1504 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) _146_1504 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in (tps, t))
end))
end
| _57_3050 -> begin
([], ty)
end)
in (match (_57_3053) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ ((tc, uvs, tps, t, mutuals, datas, quals, r))
end)))
end
| _57_3055 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _57_3059 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _146_1505 -> FStar_Syntax_Syntax.U_name (_146_1505))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _57_3064, _57_3066, _57_3068, _57_3070, _57_3072, _57_3074, _57_3076) -> begin
(tc, uvs_universes)
end
| _57_3080 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _57_3085 d -> (match (_57_3085) with
| (t, _57_3084) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _57_3089, _57_3091, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _146_1509 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_1509 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon ((l, uvs, ty, tc, ntps, quals, mutuals, r)))
end
| _57_3101 -> begin
(FStar_All.failwith "Impossible")
end)
end)) data_types datas)))
end)
in (tcs, datas)))
end))
end))
end)))
end))))))))
in (

let _57_3111 = (FStar_All.pipe_right ses (FStar_List.partition (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_3105) -> begin
true
end
| _57_3108 -> begin
false
end))))
in (match (_57_3111) with
| (tys, datas) -> begin
(

let env0 = env
in (

let _57_3128 = (FStar_List.fold_right (fun tc _57_3117 -> (match (_57_3117) with
| (env, all_tcs, g) -> begin
(

let _57_3121 = (tc_tycon env tc)
in (match (_57_3121) with
| (env, tc, tc_u) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _57_3123 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1513 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _146_1513))
end else begin
()
end
in (let _146_1514 = (FStar_TypeChecker_Rel.conj_guard g g')
in (env, ((tc, tc_u))::all_tcs, _146_1514))))
end))
end)) tys (env, [], FStar_TypeChecker_Rel.trivial_guard))
in (match (_57_3128) with
| (env, tcs, g) -> begin
(

let _57_3138 = (FStar_List.fold_right (fun se _57_3132 -> (match (_57_3132) with
| (datas, g) -> begin
(

let _57_3135 = (tc_data env tcs se)
in (match (_57_3135) with
| (data, g') -> begin
(let _146_1517 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((data)::datas, _146_1517))
end))
end)) datas ([], g))
in (match (_57_3138) with
| (datas, g) -> begin
(

let _57_3141 = (let _146_1518 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _146_1518 datas))
in (match (_57_3141) with
| (tcs, datas) -> begin
(let _146_1520 = (let _146_1519 = (FStar_TypeChecker_Env.get_range env0)
in ((FStar_List.append tcs datas), quals, lids, _146_1519))
in FStar_Syntax_Syntax.Sig_bundle (_146_1520))
end))
end))
end)))
end)))))))))


let rec tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt * FStar_TypeChecker_Env.env) = (fun env se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _146_1525 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1525))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_inductive env ses quals lids)
in (let _146_1526 = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, _146_1526))))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.GoOn -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to process pragma: use \'fstar --help\' to see which options are available", r))))
end
| FStar_Getopt.Die (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Failed to process pragma: " s), r))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _57_3179 = (set_options FStar_Options.Set o)
in (se, env))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _57_3183 = (let _146_1531 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _146_1531 Prims.ignore))
in (

let _57_3188 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _57_3190 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (se, env))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let ne = (tc_eff_decl env ne ForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne NotForFree)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect ((ne, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let _57_3212 = (let _146_1532 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _146_1532))
in (match (_57_3212) with
| (a, wp_a_src) -> begin
(

let _57_3215 = (let _146_1533 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _146_1533))
in (match (_57_3215) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (FStar_Syntax_Subst.subst (FStar_Syntax_Syntax.Renaming ((FStar_Syntax_Syntax.Name2Name ((b, a)))::[])) wp_b_tgt)
in (

let expected_k = (let _146_1538 = (let _146_1536 = (FStar_Syntax_Syntax.mk_binder a)
in (let _146_1535 = (let _146_1534 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_146_1534)::[])
in (_146_1536)::_146_1535))
in (let _146_1537 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _146_1538 _146_1537)))
in (

let lift = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift) expected_k)
in (

let sub = (

let _57_3219 = sub
in {FStar_Syntax_Syntax.source = _57_3219.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _57_3219.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect ((sub, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _57_3232 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3238 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_57_3238) with
| (tps, c) -> begin
(

let _57_3242 = (tc_tparams env tps)
in (match (_57_3242) with
| (tps, env, us) -> begin
(

let _57_3246 = (tc_comp env c)
in (match (_57_3246) with
| (c, u, g) -> begin
(

let _57_3247 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _57_3253 = (let _146_1539 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((tps, c))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _146_1539))
in (match (_57_3253) with
| (uvs, t) -> begin
(

let _57_3272 = (match ((let _146_1541 = (let _146_1540 = (FStar_Syntax_Subst.compress t)
in _146_1540.FStar_Syntax_Syntax.n)
in (tps, _146_1541))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_57_3256, c)) -> begin
([], c)
end
| (_57_3262, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
(tps, c)
end
| _57_3269 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_57_3272) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev ((lid, uvs, tps, c, tags, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (se, env)))
end))
end)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3283 = ()
in (

let _57_3287 = (let _146_1543 = (let _146_1542 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _146_1542))
in (check_and_gen env t _146_1543))
in (match (_57_3287) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ ((lid, uvs, t, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _57_3300 = (FStar_Syntax_Util.type_u ())
in (match (_57_3300) with
| (k, _57_3299) -> begin
(

let phi = (let _146_1544 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _146_1544 (norm env)))
in (

let _57_3302 = (FStar_TypeChecker_Util.check_uvars r phi)
in (

let se = FStar_Syntax_Syntax.Sig_assume ((lid, phi, quals, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _57_3315 = (tc_term env e)
in (match (_57_3315) with
| (e, c, g1) -> begin
(

let _57_3320 = (let _146_1548 = (let _146_1545 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_146_1545))
in (let _146_1547 = (let _146_1546 = (c.FStar_Syntax_Syntax.comp ())
in (e, _146_1546))
in (check_expected_effect env _146_1548 _146_1547)))
in (match (_57_3320) with
| (e, _57_3318, g) -> begin
(

let _57_3321 = (let _146_1549 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _146_1549))
in (

let se = FStar_Syntax_Syntax.Sig_main ((e, r))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _146_1561 = (let _146_1560 = (let _146_1559 = (let _146_1558 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_1557 = (FStar_Syntax_Print.quals_to_string q)
in (let _146_1556 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _146_1558 _146_1557 _146_1556))))
in (_146_1559, r))
in FStar_Syntax_Syntax.Error (_146_1560))
in (Prims.raise _146_1561))
end
end))
in (

let _57_3365 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _57_3342 lb -> (match (_57_3342) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _57_3361 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(gen, lb, quals_opt)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _57_3356 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _57_3355 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _146_1564 = (FStar_Syntax_Syntax.mk_lb (FStar_Util.Inr (lbname), uvs, FStar_Syntax_Const.effect_ALL_lid, tval, lb.FStar_Syntax_Syntax.lbdef))
in (false, _146_1564, quals_opt))))
end)
in (match (_57_3361) with
| (gen, lb, quals_opt) -> begin
(gen, (lb)::lbs, quals_opt)
end)))
end)) (true, [], if (quals = []) then begin
None
end else begin
Some (quals)
end)))
in (match (_57_3365) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _57_3374 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _146_1568 = (let _146_1567 = (let _146_1566 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((Prims.fst lbs), lbs'), _146_1566))
in FStar_Syntax_Syntax.Tm_let (_146_1567))
in (FStar_Syntax_Syntax.mk _146_1568 None r))
in (

let _57_3408 = (match ((tc_maybe_toplevel_term (

let _57_3378 = env
in {FStar_TypeChecker_Env.solver = _57_3378.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3378.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3378.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3378.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3378.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3378.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3378.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3378.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3378.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3378.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3378.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _57_3378.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _57_3378.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3378.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3378.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3378.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3378.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3378.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3378.FStar_TypeChecker_Env.use_bv_sorts}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _57_3385; FStar_Syntax_Syntax.pos = _57_3383; FStar_Syntax_Syntax.vars = _57_3381}, _57_3392, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_57_3396, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _57_3402 -> begin
quals
end)
in (FStar_Syntax_Syntax.Sig_let ((lbs, r, lids, quals)), lbs))
end
| _57_3405 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_57_3408) with
| (se, lbs) -> begin
(

let _57_3414 = if (log env) then begin
(let _146_1576 = (let _146_1575 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _146_1572 = (let _146_1571 = (let _146_1570 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1570.FStar_Syntax_Syntax.fv_name)
in _146_1571.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _146_1572))) with
| None -> begin
true
end
| _57_3412 -> begin
false
end)
in if should_log then begin
(let _146_1574 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _146_1573 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _146_1574 _146_1573)))
end else begin
""
end))))
in (FStar_All.pipe_right _146_1575 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _146_1576))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (se, env)))
end)))))
end))))
end))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_12 -> (match (_57_12) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _57_3424 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _57_3434 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_57_3436) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _57_3447, _57_3449) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _57_3455 -> (match (_57_3455) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _57_3461, _57_3463, quals, r) -> begin
(

let dec = (let _146_1592 = (let _146_1591 = (let _146_1590 = (let _146_1589 = (let _146_1588 = (FStar_Syntax_Syntax.mk_Total t)
in (bs, _146_1588))
in FStar_Syntax_Syntax.Tm_arrow (_146_1589))
in (FStar_Syntax_Syntax.mk _146_1590 None r))
in (l, us, _146_1591, (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1592))
in ((dec)::out, hidden))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _57_3473, _57_3475, _57_3477, _57_3479, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r))
in ((dec)::out, (l)::hidden))
end
| _57_3485 -> begin
(out, hidden)
end)
end)) ses ([], hidden))
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_3487, _57_3489, quals, _57_3492) -> begin
if (is_abstract quals) then begin
([], hidden)
end else begin
((se)::[], hidden)
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
((FStar_Syntax_Syntax.Sig_declare_typ ((l, us, t, (FStar_Syntax_Syntax.Assumption)::[], r)))::[], (l)::hidden)
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _57_3511 -> begin
false
end)))) then begin
((se)::[], hidden)
end else begin
([], hidden)
end
end
end
| FStar_Syntax_Syntax.Sig_main (_57_3513) -> begin
([], hidden)
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
((se)::[], hidden)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _57_3532, _57_3534, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
([], hidden)
end else begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::[], (FStar_Ident.range_of_lid lid)))
in ((dec)::[], (lid)::hidden))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _146_1599 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _146_1598 = (let _146_1597 = (let _146_1596 = (let _146_1595 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _146_1595.FStar_Syntax_Syntax.fv_name)
in _146_1596.FStar_Syntax_Syntax.v)
in (_146_1597, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, (FStar_Syntax_Syntax.Assumption)::quals, r))
in FStar_Syntax_Syntax.Sig_declare_typ (_146_1598)))))
in (_146_1599, hidden))
end else begin
((se)::[], hidden)
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let _57_3573 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _57_3554 se -> (match (_57_3554) with
| (ses, exports, env, hidden) -> begin
(

let _57_3556 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_1606 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _146_1606))
end else begin
()
end
in (

let _57_3560 = (tc_decl env se)
in (match (_57_3560) with
| (se, env) -> begin
(

let _57_3561 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _146_1607 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "Checked: %s\n" _146_1607))
end else begin
()
end
in (

let _57_3563 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)
in (

let _57_3567 = (for_export hidden se)
in (match (_57_3567) with
| (exported, hidden) -> begin
((se)::ses, (exported)::exports, env, hidden)
end))))
end)))
end)) ([], [], env, [])))
in (match (_57_3573) with
| (ses, exports, env, _57_3572) -> begin
(let _146_1608 = (FStar_All.pipe_right (FStar_List.rev exports) FStar_List.flatten)
in ((FStar_List.rev ses), _146_1608, env))
end)))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _57_3578 = env
in (let _146_1613 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _57_3578.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3578.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3578.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3578.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3578.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3578.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3578.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3578.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3578.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3578.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3578.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3578.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3578.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3578.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3578.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3578.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _146_1613; FStar_TypeChecker_Env.type_of = _57_3578.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3578.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3578.FStar_TypeChecker_Env.use_bv_sorts}))
in (

let _57_3581 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _57_3587 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_57_3587) with
| (ses, exports, env) -> begin
((

let _57_3588 = modul
in {FStar_Syntax_Syntax.name = _57_3588.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _57_3588.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3588.FStar_Syntax_Syntax.is_interface}), exports, env)
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _57_3596 = (tc_decls env decls)
in (match (_57_3596) with
| (ses, exports, env) -> begin
(

let modul = (

let _57_3597 = modul
in {FStar_Syntax_Syntax.name = _57_3597.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _57_3597.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _57_3597.FStar_Syntax_Syntax.is_interface})
in (modul, exports, env))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _57_3603 = modul
in {FStar_Syntax_Syntax.name = _57_3603.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _57_3603.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _57_3613 = if (not ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid))) then begin
(

let _57_3607 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _57_3609 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _57_3611 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _146_1626 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _146_1626 Prims.ignore)))))
end else begin
()
end
in (modul, env)))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _57_3620 = (tc_partial_modul env modul)
in (match (_57_3620) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let type_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _57_3623 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1635 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _146_1635))
end else begin
()
end
in (

let env = (

let _57_3625 = env
in {FStar_TypeChecker_Env.solver = _57_3625.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3625.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3625.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3625.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3625.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3625.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3625.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3625.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3625.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3625.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3625.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3625.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3625.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _57_3625.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3625.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3625.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3625.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _57_3625.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3625.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_3625.FStar_TypeChecker_Env.use_bv_sorts})
in (

let _57_3641 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _57_3633) -> begin
(let _146_1640 = (let _146_1639 = (let _146_1638 = (FStar_TypeChecker_Env.get_range env)
in ((Prims.strcat "Implicit argument: " msg), _146_1638))
in FStar_Syntax_Syntax.Error (_146_1639))
in (Prims.raise _146_1640))
end
in (match (_57_3641) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
(t, c.FStar_Syntax_Syntax.res_typ, g)
end else begin
(let _146_1645 = (let _146_1644 = (let _146_1643 = (let _146_1641 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _146_1641))
in (let _146_1642 = (FStar_TypeChecker_Env.get_range env)
in (_146_1643, _146_1642)))
in FStar_Syntax_Syntax.Error (_146_1644))
in (Prims.raise _146_1645))
end
end)))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _57_3644 = if (FStar_Options.debug_any ()) then begin
(let _146_1650 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _146_1650))
end else begin
()
end
in (

let _57_3648 = (tc_modul env m)
in (match (_57_3648) with
| (m, env) -> begin
(

let _57_3649 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _146_1651 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _146_1651))
end else begin
()
end
in (m, env))
end))))




