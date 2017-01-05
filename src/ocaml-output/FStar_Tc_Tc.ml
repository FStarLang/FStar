
open Prims

let syn' = (fun env k -> (let _147_11 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Syntax.syn _147_11 (Some (k)))))


let log : FStar_Tc_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _147_14 = (FStar_Tc_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _147_14))))))


let rng : FStar_Tc_Env.env  ->  FStar_Range.range = (fun env -> (FStar_Tc_Env.get_range env))


let instantiate_both : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (

let _48_24 = env
in {FStar_Tc_Env.solver = _48_24.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_24.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_24.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_24.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_24.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_24.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_24.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_24.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_24.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = true; FStar_Tc_Env.instantiate_vargs = true; FStar_Tc_Env.effects = _48_24.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_24.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_24.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_24.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_24.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_24.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_24.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_24.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_24.FStar_Tc_Env.default_effects}))


let no_inst : FStar_Tc_Env.env  ->  FStar_Tc_Env.env = (fun env -> (

let _48_27 = env
in {FStar_Tc_Env.solver = _48_27.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_27.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_27.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_27.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_27.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_27.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_27.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_27.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_27.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = false; FStar_Tc_Env.instantiate_vargs = false; FStar_Tc_Env.effects = _48_27.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_27.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_27.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_27.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_27.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_27.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_27.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_27.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_27.FStar_Tc_Env.default_effects}))


let mk_lex_list : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
v.FStar_Absyn_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Absyn_Syntax.pos tl.FStar_Absyn_Syntax.pos)
end
in (let _147_34 = (let _147_33 = (let _147_32 = (let _147_27 = (let _147_26 = (FStar_Tc_Recheck.recompute_typ v)
in (FStar_All.pipe_left (fun _147_25 -> FStar_Util.Inl (_147_25)) _147_26))
in ((_147_27), (Some (FStar_Absyn_Syntax.Implicit (false)))))
in (let _147_31 = (let _147_30 = (FStar_Absyn_Syntax.varg v)
in (let _147_29 = (let _147_28 = (FStar_Absyn_Syntax.varg tl)
in (_147_28)::[])
in (_147_30)::_147_29))
in (_147_32)::_147_31))
in ((FStar_Absyn_Util.lex_pair), (_147_33)))
in (FStar_Absyn_Syntax.mk_Exp_app _147_34 (Some (FStar_Absyn_Util.lex_t)) r)))) vs FStar_Absyn_Util.lex_top))


let is_eq : FStar_Absyn_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _48_1 -> (match (_48_1) with
| Some (FStar_Absyn_Syntax.Equality) -> begin
true
end
| _48_37 -> begin
false
end))


let steps : FStar_Tc_Env.env  ->  FStar_Tc_Normalize.step Prims.list = (fun env -> if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]
end else begin
(FStar_Tc_Normalize.Beta)::[]
end)


let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::[]) env t))


let norm_t : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _147_47 = (steps env)
in (FStar_Tc_Normalize.norm_typ _147_47 env t)))


let norm_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let _147_52 = (steps env)
in (FStar_Tc_Normalize.norm_kind _147_52 env k)))


let norm_c : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp = (fun env c -> (let _147_57 = (steps env)
in (FStar_Tc_Normalize.norm_comp _147_57 env c)))


let fxv_check : FStar_Absyn_Syntax.exp  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either  ->  FStar_Absyn_Syntax.bvvar FStar_Util.set  ->  Prims.unit = (fun head env kt fvs -> (

let rec aux = (fun norm kt -> if (FStar_Util.set_is_empty fvs) then begin
()
end else begin
(

let fvs' = (match (kt) with
| FStar_Util.Inl (k) -> begin
(let _147_70 = if norm then begin
(norm_k env k)
end else begin
k
end
in (FStar_Absyn_Util.freevars_kind _147_70))
end
| FStar_Util.Inr (t) -> begin
(let _147_71 = if norm then begin
(norm_t env t)
end else begin
t
end
in (FStar_Absyn_Util.freevars_typ _147_71))
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

let fail = (fun _48_61 -> (match (()) with
| () -> begin
(

let escaping = (let _147_76 = (let _147_75 = (FStar_Util.set_elements a)
in (FStar_All.pipe_right _147_75 (FStar_List.map (fun x -> (FStar_Absyn_Print.strBvd x.FStar_Absyn_Syntax.v)))))
in (FStar_All.pipe_right _147_76 (FStar_String.concat ", ")))
in (

let msg = if ((FStar_Util.set_count a) > (Prims.parse_int "1")) then begin
(let _147_77 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variables \'{%s}\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" escaping _147_77))
end else begin
(let _147_78 = (FStar_Tc_Normalize.exp_norm_to_string env head)
in (FStar_Util.format2 "Bound variable \'%s\' in the type of \'%s\' escapes because of impure applications; add explicit let-bindings" escaping _147_78))
end
in (let _147_81 = (let _147_80 = (let _147_79 = (FStar_Tc_Env.get_range env)
in ((msg), (_147_79)))
in FStar_Absyn_Syntax.Error (_147_80))
in (Prims.raise _147_81))))
end))
in (match (kt) with
| FStar_Util.Inl (k) -> begin
(

let s = (FStar_Tc_Util.new_kvar env)
in (match ((FStar_Tc_Rel.try_keq env k s)) with
| Some (g) -> begin
(FStar_Tc_Rel.try_discharge_guard env g)
end
| _48_71 -> begin
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
| _48_78 -> begin
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


let maybe_make_subst = (fun _48_2 -> (match (_48_2) with
| FStar_Util.Inl (Some (a), t) -> begin
(FStar_Util.Inl (((a), (t))))::[]
end
| FStar_Util.Inr (Some (x), e) -> begin
(FStar_Util.Inr (((x), (e))))::[]
end
| _48_99 -> begin
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
(let _147_92 = (let _147_91 = (let _147_90 = (FStar_Absyn_Util.btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_147_90)))
in FStar_Util.Inl (_147_91))
in (_147_92)::s)
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
s
end else begin
(let _147_95 = (let _147_94 = (let _147_93 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_147_93)))
in FStar_Util.Inr (_147_94))
in (_147_95)::s)
end
end
| _48_114 -> begin
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
| _48_129 -> begin
(failwith "Impossible")
end)
end)


let set_lcomp_result : FStar_Absyn_Syntax.lcomp  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.lcomp = (fun lc t -> (

let _48_132 = lc
in {FStar_Absyn_Syntax.eff_name = _48_132.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = t; FStar_Absyn_Syntax.cflags = _48_132.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = (fun _48_134 -> (match (()) with
| () -> begin
(let _147_104 = (lc.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Util.set_result_typ _147_104 t))
end))}))


let value_check_expected_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, FStar_Absyn_Syntax.lcomp) FStar_Util.either  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e tlc -> (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _147_111 = if (not ((FStar_Absyn_Util.is_pure_or_ghost_function t))) then begin
(FStar_Absyn_Syntax.mk_Total t)
end else begin
(FStar_Tc_Util.return_value env t e)
end
in (FStar_Tc_Util.lcomp_of_comp _147_111))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Absyn_Syntax.res_typ
in (

let _48_158 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
((e), (lc), (FStar_Tc_Rel.trivial_guard))
end
| Some (t') -> begin
(

let _48_147 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_113 = (FStar_Absyn_Print.typ_to_string t)
in (let _147_112 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _147_113 _147_112)))
end else begin
()
end
in (

let _48_151 = (FStar_Tc_Util.check_and_ascribe env e t t')
in (match (_48_151) with
| (e, g) -> begin
(

let _48_154 = (let _147_119 = (FStar_All.pipe_left (fun _147_118 -> Some (_147_118)) (FStar_Tc_Errors.subtyping_failed env t t'))
in (FStar_Tc_Util.strengthen_precondition _147_119 env e lc g))
in (match (_48_154) with
| (lc, g) -> begin
((e), ((set_lcomp_result lc t')), (g))
end))
end)))
end)
in (match (_48_158) with
| (e, lc, g) -> begin
(

let _48_159 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_120 = (FStar_Absyn_Print.lcomp_typ_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _147_120))
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


let check_expected_effect : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp Prims.option  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp)  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env copt _48_171 -> (match (_48_171) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_48_173) -> begin
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
(let _147_133 = (norm_c env c)
in ((e), (_147_133), (FStar_Tc_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _48_187 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_136 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _147_135 = (FStar_Absyn_Print.comp_typ_to_string c)
in (let _147_134 = (FStar_Absyn_Print.comp_typ_to_string expected_c)
in (FStar_Util.print3 "(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _147_136 _147_135 _147_134))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let expected_c' = (let _147_137 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp expected_c)
in (FStar_Tc_Util.refresh_comp_label env true _147_137))
in (

let _48_195 = (let _147_138 = (expected_c'.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_left (FStar_Tc_Util.check_comp env e c) _147_138))
in (match (_48_195) with
| (e, _48_193, g) -> begin
(

let _48_196 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_140 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _147_139 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _147_140 _147_139)))
end else begin
()
end
in ((e), (expected_c), (g)))
end)))))
end))
end))


let no_logical_guard = (fun env _48_202 -> (match (_48_202) with
| (te, kt, f) -> begin
(match ((FStar_Tc_Rel.guard_form f)) with
| FStar_Tc_Rel.Trivial -> begin
((te), (kt), (f))
end
| FStar_Tc_Rel.NonTrivial (f) -> begin
(let _147_146 = (let _147_145 = (let _147_144 = (FStar_Tc_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _147_143 = (FStar_Tc_Env.get_range env)
in ((_147_144), (_147_143))))
in FStar_Absyn_Syntax.Error (_147_145))
in (Prims.raise _147_146))
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
(let _147_153 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Expected type is %s" _147_153))
end))


let with_implicits = (fun imps _48_220 -> (match (_48_220) with
| (e, l, g) -> begin
((e), (l), ((

let _48_221 = g
in {FStar_Tc_Rel.guard_f = _48_221.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _48_221.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (FStar_List.append imps g.FStar_Tc_Rel.implicits)})))
end))


let add_implicit : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * FStar_Range.range), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * FStar_Range.range)) FStar_Util.either  ->  FStar_Tc_Rel.guard_t  ->  FStar_Tc_Rel.guard_t = (fun u g -> (

let _48_225 = g
in {FStar_Tc_Rel.guard_f = _48_225.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _48_225.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = (u)::g.FStar_Tc_Rel.implicits}))


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

let _48_244 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _147_206 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (let _147_205 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print2 "(%s) - Checking kind %s" _147_206 _147_205)))
end else begin
()
end
in (

let _48_249 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_48_249) with
| (env, _48_248) -> begin
(

let _48_252 = (tc_args env args)
in (match (_48_252) with
| (args, g) -> begin
(let _147_208 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_uvar ((u), (args))))
in ((_147_208), (g)))
end))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev ((l, args), {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _48_263; FStar_Absyn_Syntax.pos = _48_261; FStar_Absyn_Syntax.fvs = _48_259; FStar_Absyn_Syntax.uvs = _48_257}) -> begin
(

let _48_272 = (FStar_Tc_Env.lookup_kind_abbrev env l)
in (match (_48_272) with
| (_48_269, binders, body) -> begin
(

let _48_275 = (tc_args env args)
in (match (_48_275) with
| (args, g) -> begin
if ((FStar_List.length binders) <> (FStar_List.length args)) then begin
(let _147_212 = (let _147_211 = (let _147_210 = (let _147_209 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Unexpected number of arguments to kind abbreviation " _147_209))
in ((_147_210), (k.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_211))
in (Prims.raise _147_212))
end else begin
(

let _48_308 = (FStar_List.fold_left2 (fun _48_279 b a -> (match (_48_279) with
| (subst, args, guards) -> begin
(match ((((Prims.fst b)), ((Prims.fst a)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (t)) -> begin
(

let _48_289 = (let _147_216 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (tc_typ_check env t _147_216))
in (match (_48_289) with
| (t, g) -> begin
(

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t))))::subst
in (let _147_218 = (let _147_217 = (FStar_Absyn_Syntax.targ t)
in (_147_217)::args)
in ((subst), (_147_218), ((g)::guards))))
end))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (e)) -> begin
(

let env = (let _147_219 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Env.set_expected_typ env _147_219))
in (

let _48_301 = (tc_ghost_exp env e)
in (match (_48_301) with
| (e, _48_299, g) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (e))))::subst
in (let _147_221 = (let _147_220 = (FStar_Absyn_Syntax.varg e)
in (_147_220)::args)
in ((subst), (_147_221), ((g)::guards))))
end)))
end
| _48_304 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Ill-typed argument to kind abbreviation"), ((FStar_Absyn_Util.range_of_arg a))))))
end)
end)) (([]), ([]), ([])) binders args)
in (match (_48_308) with
| (subst, args, guards) -> begin
(

let args = (FStar_List.rev args)
in (

let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
in (

let k' = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.DeltaHard)::[]) env k)
in (

let k = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (k'))))
in (let _147_224 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard g guards)
in ((k'), (_147_224)))))))
end))
end
end))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (kabr, k) -> begin
(

let _48_319 = (tc_kind env k)
in (match (_48_319) with
| (k, f) -> begin
(

let _48_322 = (FStar_All.pipe_left (tc_args env) (Prims.snd kabr))
in (match (_48_322) with
| (args, g) -> begin
(

let kabr = (((Prims.fst kabr)), (args))
in (

let kk = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_abbrev ((kabr), (k))))
in (let _147_226 = (FStar_Tc_Rel.conj_guard f g)
in ((kk), (_147_226)))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _48_332 = (tc_binders env bs)
in (match (_48_332) with
| (bs, env, g) -> begin
(

let _48_335 = (tc_kind env k)
in (match (_48_335) with
| (k, f) -> begin
(

let f = (FStar_Tc_Rel.close_guard bs f)
in (let _147_229 = (FStar_All.pipe_left w (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k))))
in (let _147_228 = (FStar_Tc_Rel.conj_guard g f)
in ((_147_229), (_147_228)))))
end))
end))
end
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _147_230 = (FStar_Tc_Util.new_kvar env)
in ((_147_230), (FStar_Tc_Rel.trivial_guard)))
end))))
and tc_vbinder : FStar_Tc_Env.env  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t * FStar_Tc_Env.env * FStar_Tc_Rel.guard_t) = (fun env x -> (

let _48_342 = (tc_typ_check env x.FStar_Absyn_Syntax.sort FStar_Absyn_Syntax.ktype)
in (match (_48_342) with
| (t, g) -> begin
(

let x = (

let _48_343 = x
in {FStar_Absyn_Syntax.v = _48_343.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _48_343.FStar_Absyn_Syntax.p})
in (

let env' = (let _147_233 = (FStar_Absyn_Syntax.v_binder x)
in (maybe_push_binding env _147_233))
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

let _48_362 = (tc_kind env a.FStar_Absyn_Syntax.sort)
in (match (_48_362) with
| (k, g) -> begin
(

let b = ((FStar_Util.Inl ((

let _48_363 = a
in {FStar_Absyn_Syntax.v = _48_363.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _48_363.FStar_Absyn_Syntax.p}))), (imp))
in (

let env' = (maybe_push_binding env b)
in (

let _48_370 = (aux env' bs)
in (match (_48_370) with
| (bs, env', g') -> begin
(let _147_241 = (let _147_240 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _147_240))
in (((b)::bs), (env'), (_147_241)))
end))))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _48_376 = (tc_vbinder env x)
in (match (_48_376) with
| (x, env', g) -> begin
(

let b = ((FStar_Util.Inr (x)), (imp))
in (

let _48_381 = (aux env' bs)
in (match (_48_381) with
| (bs, env', g') -> begin
(let _147_243 = (let _147_242 = (FStar_Tc_Rel.close_guard ((b)::[]) g')
in (FStar_Tc_Rel.conj_guard g _147_242))
in (((b)::bs), (env'), (_147_243)))
end)))
end))
end)
end))
in (aux env bs)))
and tc_args : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.args * FStar_Tc_Rel.guard_t) = (fun env args -> (FStar_List.fold_right (fun _48_386 _48_389 -> (match (((_48_386), (_48_389))) with
| ((arg, imp), (args, g)) -> begin
(match (arg) with
| FStar_Util.Inl (t) -> begin
(

let _48_396 = (tc_typ env t)
in (match (_48_396) with
| (t, _48_394, g') -> begin
(let _147_248 = (FStar_Tc_Rel.conj_guard g g')
in (((((FStar_Util.Inl (t)), (imp)))::args), (_147_248)))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _48_403 = (tc_ghost_exp env e)
in (match (_48_403) with
| (e, _48_401, g') -> begin
(let _147_249 = (FStar_Tc_Rel.conj_guard g g')
in (((((FStar_Util.Inr (e)), (imp)))::args), (_147_249)))
end))
end)
end)) args (([]), (FStar_Tc_Rel.trivial_guard))))
and tc_pats : FStar_Tc_Env.env  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list Prims.list  ->  (FStar_Absyn_Syntax.args Prims.list * FStar_Tc_Rel.guard_t) = (fun env pats -> (FStar_List.fold_right (fun p _48_409 -> (match (_48_409) with
| (pats, g) -> begin
(

let _48_412 = (tc_args env p)
in (match (_48_412) with
| (args, g') -> begin
(let _147_254 = (FStar_Tc_Rel.conj_guard g g')
in (((args)::pats), (_147_254)))
end))
end)) pats (([]), (FStar_Tc_Rel.trivial_guard))))
and tc_comp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp * FStar_Tc_Rel.guard_t) = (fun env c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _48_419 = (tc_typ_check env t FStar_Absyn_Syntax.ktype)
in (match (_48_419) with
| (t, g) -> begin
(let _147_257 = (FStar_Absyn_Syntax.mk_Total t)
in ((_147_257), (g)))
end))
end
| FStar_Absyn_Syntax.Comp (c) -> begin
(

let kc = (FStar_Tc_Env.lookup_effect_lid env c.FStar_Absyn_Syntax.effect_name)
in (

let head = (FStar_Absyn_Util.ftv c.FStar_Absyn_Syntax.effect_name kc)
in (

let tc = (let _147_260 = (let _147_259 = (let _147_258 = (FStar_Absyn_Syntax.targ c.FStar_Absyn_Syntax.result_typ)
in (_147_258)::c.FStar_Absyn_Syntax.effect_args)
in ((head), (_147_259)))
in (FStar_Absyn_Syntax.mk_Typ_app _147_260 None c.FStar_Absyn_Syntax.result_typ.FStar_Absyn_Syntax.pos))
in (

let _48_427 = (tc_typ_check env tc FStar_Absyn_Syntax.keffect)
in (match (_48_427) with
| (tc, f) -> begin
(

let _48_431 = (FStar_Absyn_Util.head_and_args tc)
in (match (_48_431) with
| (_48_429, args) -> begin
(

let _48_443 = (match (args) with
| ((FStar_Util.Inl (res), _48_436))::args -> begin
((res), (args))
end
| _48_440 -> begin
(failwith "Impossible")
end)
in (match (_48_443) with
| (res, args) -> begin
(

let _48_459 = (let _147_262 = (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_List.map (fun _48_3 -> (match (_48_3) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(

let _48_450 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_48_450) with
| (env, _48_449) -> begin
(

let _48_455 = (tc_ghost_exp env e)
in (match (_48_455) with
| (e, _48_453, g) -> begin
((FStar_Absyn_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_Tc_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _147_262 FStar_List.unzip))
in (match (_48_459) with
| (flags, guards) -> begin
(let _147_264 = (FStar_Absyn_Syntax.mk_Comp (

let _48_460 = c
in {FStar_Absyn_Syntax.effect_name = _48_460.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = res; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _48_460.FStar_Absyn_Syntax.flags}))
in (let _147_263 = (FStar_List.fold_left FStar_Tc_Rel.conj_guard f guards)
in ((_147_264), (_147_263))))
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

let _48_472 = a
in {FStar_Absyn_Syntax.v = _48_472.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _48_472.FStar_Absyn_Syntax.p})
in (

let t = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_btvar a))
in (

let _48_479 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_48_479) with
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

let _48_484 = i
in {FStar_Absyn_Syntax.v = _48_484.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _48_484.FStar_Absyn_Syntax.p})
in (let _147_287 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in ((_147_287), (qk), (FStar_Tc_Rel.trivial_guard))))))
end
| FStar_Absyn_Syntax.Typ_const (i) when ((FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.allTyp_lid) || (FStar_Ident.lid_equals i.FStar_Absyn_Syntax.v FStar_Absyn_Const.exTyp_lid)) -> begin
(

let k = (FStar_Tc_Util.new_kvar env)
in (

let qk = (FStar_Absyn_Util.allT_k k)
in (

let i = (

let _48_491 = i
in {FStar_Absyn_Syntax.v = _48_491.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = qk; FStar_Absyn_Syntax.p = _48_491.FStar_Absyn_Syntax.p})
in (let _147_288 = (FStar_Absyn_Syntax.mk_Typ_const i (Some (qk)) t.FStar_Absyn_Syntax.pos)
in ((_147_288), (qk), (FStar_Tc_Rel.trivial_guard))))))
end
| FStar_Absyn_Syntax.Typ_const (i) -> begin
(

let k = (match ((FStar_Tc_Env.try_lookup_effect_lid env i.FStar_Absyn_Syntax.v)) with
| Some (k) -> begin
k
end
| _48_499 -> begin
(FStar_Tc_Env.lookup_typ_lid env i.FStar_Absyn_Syntax.v)
end)
in (

let i = (

let _48_501 = i
in {FStar_Absyn_Syntax.v = _48_501.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _48_501.FStar_Absyn_Syntax.p})
in (

let t = (FStar_Absyn_Syntax.mk_Typ_const i (Some (k)) t.FStar_Absyn_Syntax.pos)
in (

let _48_508 = (FStar_Tc_Util.maybe_instantiate_typ env t k)
in (match (_48_508) with
| (t, k, imps) -> begin
(FStar_All.pipe_left (with_implicits imps) ((t), (k), (FStar_Tc_Rel.trivial_guard)))
end)))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, cod) -> begin
(

let _48_516 = (tc_binders env bs)
in (match (_48_516) with
| (bs, env, g) -> begin
(

let _48_519 = (tc_comp env cod)
in (match (_48_519) with
| (cod, f) -> begin
(

let t = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (cod))))
in (

let _48_604 = if (FStar_Absyn_Util.is_smt_lemma t) then begin
(match (cod.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp ({FStar_Absyn_Syntax.effect_name = _48_542; FStar_Absyn_Syntax.result_typ = _48_540; FStar_Absyn_Syntax.effect_args = ((FStar_Util.Inl (pre), _48_536))::((FStar_Util.Inl (post), _48_531))::((FStar_Util.Inr (pats), _48_526))::[]; FStar_Absyn_Syntax.flags = _48_522}) -> begin
(

let rec extract_pats = (fun pats -> (match ((let _147_293 = (FStar_Absyn_Util.compress_exp pats)
in _147_293.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (cons, _48_557); FStar_Absyn_Syntax.tk = _48_554; FStar_Absyn_Syntax.pos = _48_552; FStar_Absyn_Syntax.fvs = _48_550; FStar_Absyn_Syntax.uvs = _48_548}, (_48_572)::((FStar_Util.Inr (hd), _48_569))::((FStar_Util.Inr (tl), _48_564))::[]) when (FStar_Ident.lid_equals cons.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(

let _48_578 = (FStar_Absyn_Util.head_and_args_e hd)
in (match (_48_578) with
| (head, args) -> begin
(

let pat = (match (args) with
| ((_)::(arg)::[]) | ((arg)::[]) -> begin
(arg)::[]
end
| _48_585 -> begin
[]
end)
in (let _147_294 = (extract_pats tl)
in (FStar_List.append pat _147_294)))
end))
end
| _48_588 -> begin
[]
end))
in (

let pats = (let _147_295 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env pats)
in (extract_pats _147_295))
in (

let fvs = (FStar_Absyn_Util.freevars_args pats)
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _48_594 -> (match (_48_594) with
| (b, _48_593) -> begin
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
(let _147_298 = (let _147_297 = (FStar_Absyn_Print.binder_to_string b)
in (FStar_Util.format1 "Pattern misses at least one bound variables: %s" _147_297))
in (FStar_Tc_Errors.warn t.FStar_Absyn_Syntax.pos _147_298))
end))))
end
| _48_603 -> begin
(failwith "Impossible")
end)
end else begin
()
end
in (let _147_300 = (let _147_299 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_Tc_Rel.conj_guard g _147_299))
in ((t), (FStar_Absyn_Syntax.ktype), (_147_300)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(

let _48_613 = (tc_binders env bs)
in (match (_48_613) with
| (bs, env, g) -> begin
(

let _48_617 = (tc_typ env t)
in (match (_48_617) with
| (t, k, f) -> begin
(

let k = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k)) top.FStar_Absyn_Syntax.pos)
in (let _147_305 = (FStar_All.pipe_left (w k) (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t))))
in (let _147_304 = (let _147_303 = (FStar_Tc_Rel.close_guard bs f)
in (FStar_All.pipe_left (FStar_Tc_Rel.conj_guard g) _147_303))
in ((_147_305), (k), (_147_304)))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(

let _48_626 = (tc_vbinder env x)
in (match (_48_626) with
| (x, env, f1) -> begin
(

let _48_630 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_308 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _147_307 = (FStar_Absyn_Print.typ_to_string phi)
in (let _147_306 = (match ((FStar_Tc_Env.expected_typ env)) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end)
in (FStar_Util.print3 "(%s) Checking refinement formula %s; env expects type %s\n" _147_308 _147_307 _147_306))))
end else begin
()
end
in (

let _48_634 = (tc_typ_check env phi FStar_Absyn_Syntax.ktype)
in (match (_48_634) with
| (phi, f2) -> begin
(let _147_315 = (FStar_All.pipe_left (w FStar_Absyn_Syntax.ktype) (FStar_Absyn_Syntax.mk_Typ_refine ((x), (phi))))
in (let _147_314 = (let _147_313 = (let _147_312 = (let _147_311 = (FStar_Absyn_Syntax.v_binder x)
in (_147_311)::[])
in (FStar_Tc_Rel.close_guard _147_312 f2))
in (FStar_Tc_Rel.conj_guard f1 _147_313))
in ((_147_315), (FStar_Absyn_Syntax.ktype), (_147_314))))
end)))
end))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let _48_639 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_318 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _147_317 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (let _147_316 = (FStar_Absyn_Print.typ_to_string top)
in (FStar_Util.print3 "(%s) Checking type application (%s): %s\n" _147_318 _147_317 _147_316))))
end else begin
()
end
in (

let _48_644 = (tc_typ (no_inst env) head)
in (match (_48_644) with
| (head, k1', f1) -> begin
(

let args0 = args
in (

let k1 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.Beta)::[]) env k1')
in (

let _48_647 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_322 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _147_321 = (FStar_Absyn_Print.typ_to_string head)
in (let _147_320 = (FStar_Absyn_Print.kind_to_string k1')
in (let _147_319 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print4 "(%s) head %s has kind %s ... after norm %s\n" _147_322 _147_321 _147_320 _147_319)))))
end else begin
()
end
in (

let check_app = (fun _48_650 -> (match (()) with
| () -> begin
(match (k1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (_48_652) -> begin
(

let _48_656 = (tc_args env args)
in (match (_48_656) with
| (args, g) -> begin
(

let fvs = (FStar_Absyn_Util.freevars_kind k1)
in (

let binders = (FStar_Absyn_Util.binders_of_freevars fvs)
in (

let kres = (let _147_325 = (FStar_Tc_Rel.new_kvar k1.FStar_Absyn_Syntax.pos binders)
in (FStar_All.pipe_right _147_325 Prims.fst))
in (

let bs = (let _147_326 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _147_326))
in (

let kar = (FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (kres)) k1.FStar_Absyn_Syntax.pos)
in (

let _48_662 = (let _147_327 = (FStar_Tc_Rel.keq env None k1 kar)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _147_327))
in ((kres), (args), (g))))))))
end))
end
| FStar_Absyn_Syntax.Kind_arrow (formals, kres) -> begin
(

let rec check_args = (fun outargs subst g formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(let _147_338 = (FStar_Absyn_Util.subst_kind subst kres)
in ((_147_338), ((FStar_List.rev outargs)), (g)))
end
| ((((_, None))::_, ((_, Some (FStar_Absyn_Syntax.Implicit (_))))::_)) | ((((_, Some (FStar_Absyn_Syntax.Equality)))::_, ((_, Some (FStar_Absyn_Syntax.Implicit (_))))::_)) -> begin
(let _147_342 = (let _147_341 = (let _147_340 = (let _147_339 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _147_339))
in (("Argument is marked as instantiating an implicit parameter; although the expected parameter is explicit"), (_147_340)))
in FStar_Absyn_Syntax.Error (_147_341))
in (Prims.raise _147_342))
end
| ((((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_))))::rest, ((_, None))::_)) | ((((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_))))::rest, [])) -> begin
(

let formal = (FStar_List.hd formals)
in (

let _48_743 = (let _147_343 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_tvar env _147_343))
in (match (_48_743) with
| (t, u) -> begin
(

let targ = (let _147_345 = (FStar_All.pipe_left (fun _147_344 -> Some (_147_344)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inl (t)), (_147_345)))
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

let _48_776 = (let _147_346 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Tc_Util.new_implicit_evar env _147_346))
in (match (_48_776) with
| (e, u) -> begin
(

let varg = (let _147_348 = (FStar_All.pipe_left (fun _147_347 -> Some (_147_347)) (FStar_Absyn_Syntax.Implicit (false)))
in ((FStar_Util.Inr (e)), (_147_348)))
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

let _48_797 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_350 = (FStar_Absyn_Print.arg_to_string actual)
in (let _147_349 = (FStar_Absyn_Print.kind_to_string formal_k)
in (FStar_Util.print2 "Checking argument %s against expected kind %s\n" _147_350 _147_349)))
end else begin
()
end
in (

let _48_803 = (tc_typ_check (

let _48_799 = env
in {FStar_Tc_Env.solver = _48_799.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_799.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_799.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_799.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_799.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_799.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_799.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_799.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_799.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_799.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_799.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_799.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_799.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_799.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_799.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_799.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _48_799.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_799.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_799.FStar_Tc_Env.default_effects}) t formal_k)
in (match (_48_803) with
| (t, g') -> begin
(

let _48_804 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_351 = (FStar_Tc_Rel.guard_to_string env g')
in (FStar_Util.print1 ">>>Got guard %s\n" _147_351))
end else begin
()
end
in (

let actual = ((FStar_Util.Inl (t)), (imp))
in (

let g' = (let _147_353 = (let _147_352 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _147_352))
in (FStar_Tc_Rel.imp_guard _147_353 g'))
in (

let subst = (maybe_extend_subst subst formal actual)
in (let _147_354 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _147_354 formals actuals))))))
end))))
end
| ((FStar_Util.Inr (x), aqual), (FStar_Util.Inr (v), imp)) -> begin
(

let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let env' = (FStar_Tc_Env.set_expected_typ env tx)
in (

let env' = (

let _48_820 = env'
in {FStar_Tc_Env.solver = _48_820.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_820.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_820.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_820.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_820.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_820.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_820.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_820.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_820.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_820.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_820.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_820.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_820.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_820.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_820.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_820.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _48_820.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_820.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_820.FStar_Tc_Env.default_effects})
in (

let _48_823 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_356 = (FStar_Absyn_Print.arg_to_string actual)
in (let _147_355 = (FStar_Absyn_Print.typ_to_string tx)
in (FStar_Util.print2 "Checking argument %s against expected type %s\n" _147_356 _147_355)))
end else begin
()
end
in (

let _48_829 = (tc_ghost_exp env' v)
in (match (_48_829) with
| (v, _48_827, g') -> begin
(

let actual = ((FStar_Util.Inr (v)), (imp))
in (

let g' = (let _147_358 = (let _147_357 = (FStar_Tc_Util.short_circuit_typ (FStar_Util.Inl (head)) outargs)
in (FStar_All.pipe_left FStar_Tc_Rel.guard_of_guard_formula _147_357))
in (FStar_Tc_Rel.imp_guard _147_358 g'))
in (

let subst = (maybe_extend_subst subst formal actual)
in (let _147_359 = (FStar_Tc_Rel.conj_guard g g')
in (check_args ((actual)::outargs) subst _147_359 formals actuals)))))
end))))))
end
| ((FStar_Util.Inl (a), _48_836), (FStar_Util.Inr (v), imp)) -> begin
(match (a.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_type -> begin
(

let tv = (FStar_Absyn_Util.b2t v)
in (let _147_361 = (let _147_360 = (FStar_Absyn_Syntax.targ tv)
in (_147_360)::actuals)
in (check_args outargs subst g ((formal)::formals) _147_361)))
end
| _48_846 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Expected a type; got an expression"), (v.FStar_Absyn_Syntax.pos)))))
end)
end
| ((FStar_Util.Inr (_48_848), _48_851), (FStar_Util.Inl (_48_854), _48_857)) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Expected an expression; got a type"), ((FStar_Absyn_Util.range_of_arg actual))))))
end)
end
| (_48_861, []) -> begin
(let _147_363 = (let _147_362 = (FStar_Absyn_Syntax.mk_Kind_arrow ((formals), (kres)) kres.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.subst_kind subst _147_362))
in ((_147_363), ((FStar_List.rev outargs)), (g)))
end
| ([], _48_866) -> begin
(let _147_371 = (let _147_370 = (let _147_369 = (let _147_368 = (let _147_366 = (let _147_365 = (FStar_All.pipe_right outargs (FStar_List.filter (fun _48_4 -> (match (_48_4) with
| (_48_870, Some (FStar_Absyn_Syntax.Implicit (_48_872))) -> begin
false
end
| _48_877 -> begin
true
end))))
in (FStar_List.length _147_365))
in (FStar_All.pipe_right _147_366 FStar_Util.string_of_int))
in (let _147_367 = (FStar_All.pipe_right (FStar_List.length args0) FStar_Util.string_of_int)
in (FStar_Util.format2 "Too many arguments to type; expected %s arguments but got %s" _147_368 _147_367)))
in ((_147_369), (top.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_370))
in (Prims.raise _147_371))
end))
in (check_args [] [] f1 formals args))
end
| _48_879 -> begin
(let _147_374 = (let _147_373 = (let _147_372 = (FStar_Tc_Errors.expected_tcon_kind env top k1)
in ((_147_372), (top.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_373))
in (Prims.raise _147_374))
end)
end))
in (match ((let _147_378 = (let _147_375 = (FStar_Absyn_Util.compress_typ head)
in _147_375.FStar_Absyn_Syntax.n)
in (let _147_377 = (let _147_376 = (FStar_Absyn_Util.compress_kind k1)
in _147_376.FStar_Absyn_Syntax.n)
in ((_147_378), (_147_377))))) with
| (FStar_Absyn_Syntax.Typ_uvar (_48_881), FStar_Absyn_Syntax.Kind_arrow (formals, k)) when ((FStar_List.length args) = (FStar_List.length formals)) -> begin
(

let result_k = (

let s = (FStar_List.map2 FStar_Absyn_Util.subst_formal formals args)
in (FStar_Absyn_Util.subst_kind s k))
in (

let t = (FStar_Absyn_Syntax.mk_Typ_app ((head), (args)) (Some (result_k)) top.FStar_Absyn_Syntax.pos)
in ((t), (result_k), (FStar_Tc_Rel.trivial_guard))))
end
| _48_892 -> begin
(

let _48_896 = (check_app ())
in (match (_48_896) with
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

let _48_904 = (tc_kind env k1)
in (match (_48_904) with
| (k1, f1) -> begin
(

let _48_907 = (tc_typ_check env t1 k1)
in (match (_48_907) with
| (t1, f2) -> begin
(let _147_382 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_ascribed' ((t1), (k1))))
in (let _147_381 = (FStar_Tc_Rel.conj_guard f1 f2)
in ((_147_382), (k1), (_147_381))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (_48_909, k1) -> begin
(

let s = (FStar_Absyn_Util.compress_typ t)
in (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (u, k1) -> begin
(

let _48_918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _147_384 = (FStar_Absyn_Print.typ_to_string s)
in (let _147_383 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting un-instantiated uvar %s at kind %s\n" _147_384 _147_383)))
end else begin
()
end
in (let _147_387 = (FStar_All.pipe_left (w k1) (FStar_Absyn_Syntax.mk_Typ_uvar' ((u), (k1))))
in ((_147_387), (k1), (FStar_Tc_Rel.trivial_guard))))
end
| _48_921 -> begin
(

let _48_922 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) FStar_Options.High) then begin
(let _147_389 = (FStar_Absyn_Print.typ_to_string s)
in (let _147_388 = (FStar_Absyn_Print.kind_to_string k1)
in (FStar_Util.print2 "Admitting instantiated uvar %s at kind %s\n" _147_389 _147_388)))
end else begin
()
end
in ((s), (k1), (FStar_Tc_Rel.trivial_guard)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, b, r)) -> begin
(

let _48_933 = (tc_typ env t)
in (match (_48_933) with
| (t, k, f) -> begin
(let _147_390 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (((t), (b), (r)))))
in ((_147_390), (k), (f)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, l, r, p)) -> begin
(

let _48_944 = (tc_typ env t)
in (match (_48_944) with
| (t, k, f) -> begin
(let _147_391 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((t), (l), (r), (p)))))
in ((_147_391), (k), (f)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, l)) -> begin
(

let _48_953 = (tc_typ env t)
in (match (_48_953) with
| (t, k, f) -> begin
(let _147_392 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (l)))))
in ((_147_392), (k), (f)))
end))
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (qbody, pats)) -> begin
(

let _48_961 = (tc_typ_check env qbody FStar_Absyn_Syntax.ktype)
in (match (_48_961) with
| (quant, f) -> begin
(

let _48_964 = (tc_pats env pats)
in (match (_48_964) with
| (pats, g) -> begin
(

let g = (

let _48_965 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _48_965.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _48_965.FStar_Tc_Rel.implicits})
in (let _147_395 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((quant), (pats)))))
in (let _147_394 = (FStar_Tc_Util.force_tk quant)
in (let _147_393 = (FStar_Tc_Rel.conj_guard f g)
in ((_147_395), (_147_394), (_147_393))))))
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
| _48_972 -> begin
(let _147_397 = (let _147_396 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Unexpected type : %s\n" _147_396))
in (failwith _147_397))
end))))))
and tc_typ_check : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env t k -> (

let _48_979 = (tc_typ env t)
in (match (_48_979) with
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
| FStar_Absyn_Syntax.Exp_uvar (_48_988, t1) -> begin
(value_check_expected_typ env e (FStar_Util.Inl (t1)))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let t = (FStar_Tc_Env.lookup_bvar env x)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_bvar (

let _48_995 = x
in {FStar_Absyn_Syntax.v = _48_995.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _48_995.FStar_Absyn_Syntax.p}) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (

let _48_1001 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_48_1001) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _147_404 = (let _147_403 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _147_403))
in FStar_Util.Inr (_147_404))
end
in (let _147_405 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _147_405)))
end))))
end
| FStar_Absyn_Syntax.Exp_fvar (v, dc) -> begin
(

let t = (FStar_Tc_Env.lookup_lid env v.FStar_Absyn_Syntax.v)
in (

let e = (FStar_Absyn_Syntax.mk_Exp_fvar (((

let _48_1008 = v
in {FStar_Absyn_Syntax.v = _48_1008.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _48_1008.FStar_Absyn_Syntax.p})), (dc)) (Some (t)) e.FStar_Absyn_Syntax.pos)
in (

let _48_1014 = (FStar_Tc_Util.maybe_instantiate env e t)
in (match (_48_1014) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
FStar_Util.Inl (t)
end else begin
(let _147_407 = (let _147_406 = (FStar_Absyn_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _147_406))
in FStar_Util.Inr (_147_407))
end
in (

let is_data_ctor = (fun _48_5 -> (match (_48_5) with
| (Some (FStar_Absyn_Syntax.Data_ctor)) | (Some (FStar_Absyn_Syntax.Record_ctor (_))) -> begin
true
end
| _48_1024 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_Tc_Env.is_datacon env v.FStar_Absyn_Syntax.v)))) then begin
(let _147_413 = (let _147_412 = (let _147_411 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Absyn_Syntax.v.FStar_Ident.str)
in (let _147_410 = (FStar_Tc_Env.get_range env)
in ((_147_411), (_147_410))))
in FStar_Absyn_Syntax.Error (_147_412))
in (Prims.raise _147_413))
end else begin
(let _147_414 = (value_check_expected_typ env e tc)
in (FStar_All.pipe_left (with_implicits implicits) _147_414))
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

let fail = (fun msg t -> (let _147_419 = (let _147_418 = (let _147_417 = (FStar_Tc_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_147_417), (top.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_418))
in (Prims.raise _147_419)))
in (

let rec expected_function_typ = (fun env t0 -> (match (t0) with
| None -> begin
(

let _48_1045 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _48_1044 -> begin
(failwith "Impossible")
end)
in (

let _48_1050 = (tc_binders env bs)
in (match (_48_1050) with
| (bs, envbody, g) -> begin
((None), (bs), ([]), (None), (envbody), (g))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Absyn_Util.compress_typ t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _147_428 = (FStar_Absyn_Util.compress_typ t)
in _147_428.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(

let _48_1079 = (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
()
end
| _48_1078 -> begin
(failwith "Impossible")
end)
in (

let _48_1084 = (tc_binders env bs)
in (match (_48_1084) with
| (bs, envbody, g) -> begin
(

let _48_1088 = (FStar_Tc_Env.clear_expected_typ envbody)
in (match (_48_1088) with
| (envbody, _48_1087) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (g))
end))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(

let rec tc_binders = (fun _48_1098 bs_annot c bs -> (match (_48_1098) with
| (out, env, g, subst) -> begin
(match (((bs_annot), (bs))) with
| ([], []) -> begin
(let _147_437 = (FStar_Absyn_Util.subst_comp subst c)
in (((FStar_List.rev out)), (env), (g), (_147_437)))
end
| ((hdannot)::tl_annot, (hd)::tl) -> begin
(match (((hdannot), (hd))) with
| ((FStar_Util.Inl (_48_1113), _48_1116), (FStar_Util.Inr (_48_1119), _48_1122)) -> begin
(

let env = (maybe_push_binding env hdannot)
in (tc_binders (((hdannot)::out), (env), (g), (subst)) tl_annot c bs))
end
| ((FStar_Util.Inl (a), _48_1129), (FStar_Util.Inl (b), imp)) -> begin
(

let ka = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _48_1147 = (match (b.FStar_Absyn_Syntax.sort.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
((ka), (FStar_Tc_Rel.trivial_guard))
end
| _48_1139 -> begin
(

let _48_1142 = (tc_kind env b.FStar_Absyn_Syntax.sort)
in (match (_48_1142) with
| (k, g1) -> begin
(

let g2 = (FStar_Tc_Rel.keq env None ka k)
in (

let g = (let _147_438 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _147_438))
in ((k), (g))))
end))
end)
in (match (_48_1147) with
| (k, g) -> begin
(

let b = ((FStar_Util.Inl ((

let _48_1148 = b
in {FStar_Absyn_Syntax.v = _48_1148.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _48_1148.FStar_Absyn_Syntax.p}))), (imp))
in (

let env = (maybe_push_binding env b)
in (

let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders (((b)::out), (env), (g), (subst)) tl_annot c tl))))
end)))
end
| ((FStar_Util.Inr (x), _48_1156), (FStar_Util.Inr (y), imp)) -> begin
(

let tx = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _48_1178 = (match ((let _147_439 = (FStar_Absyn_Util.unmeta_typ y.FStar_Absyn_Syntax.sort)
in _147_439.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
((tx), (g))
end
| _48_1166 -> begin
(

let _48_1167 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_440 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _147_440))
end else begin
()
end
in (

let _48_1173 = (tc_typ env y.FStar_Absyn_Syntax.sort)
in (match (_48_1173) with
| (t, _48_1171, g1) -> begin
(

let g2 = (FStar_Tc_Rel.teq env tx t)
in (

let g = (let _147_441 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g _147_441))
in ((t), (g))))
end)))
end)
in (match (_48_1178) with
| (t, g) -> begin
(

let b = ((FStar_Util.Inr ((

let _48_1179 = y
in {FStar_Absyn_Syntax.v = _48_1179.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _48_1179.FStar_Absyn_Syntax.p}))), (imp))
in (

let env = (maybe_push_binding env b)
in (

let subst = (maybe_alpha_subst subst hdannot b)
in (tc_binders (((b)::out), (env), (g), (subst)) tl_annot c tl))))
end)))
end
| _48_1185 -> begin
(let _147_444 = (let _147_443 = (FStar_Absyn_Print.binder_to_string hdannot)
in (let _147_442 = (FStar_Absyn_Print.binder_to_string hd)
in (FStar_Util.format2 "Annotated %s; given %s" _147_443 _147_442)))
in (fail _147_444 t))
end)
end
| ([], _48_1188) -> begin
if (FStar_Absyn_Util.is_total_comp c) then begin
(match ((FStar_All.pipe_right (FStar_Absyn_Util.comp_result c) (whnf env))) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_fun (bs_annot, c'); FStar_Absyn_Syntax.tk = _48_1197; FStar_Absyn_Syntax.pos = _48_1195; FStar_Absyn_Syntax.fvs = _48_1193; FStar_Absyn_Syntax.uvs = _48_1191} -> begin
(tc_binders ((out), (env), (g), (subst)) bs_annot c' bs)
end
| t -> begin
(let _147_446 = (let _147_445 = (FStar_Absyn_Print.tag_of_typ t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _147_445))
in (fail _147_446 t))
end)
end else begin
(fail "Curried function, but not total" t)
end
end
| (_48_1205, []) -> begin
(

let c = (let _147_447 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs_annot), (c)) (Some (FStar_Absyn_Syntax.ktype)) c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.total_comp _147_447 c.FStar_Absyn_Syntax.pos))
in (let _147_448 = (FStar_Absyn_Util.subst_comp subst c)
in (((FStar_List.rev out)), (env), (g), (_147_448))))
end)
end))
in (

let mk_letrec_environment = (fun actuals env -> (match (env.FStar_Tc_Env.letrecs) with
| [] -> begin
((env), ([]))
end
| letrecs -> begin
(

let _48_1214 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_453 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print1 "Building let-rec environment... type of this abstraction is %s\n" _147_453))
end else begin
()
end
in (

let r = (FStar_Tc_Env.get_range env)
in (

let env = (

let _48_1217 = env
in {FStar_Tc_Env.solver = _48_1217.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_1217.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_1217.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_1217.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_1217.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_1217.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_1217.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_1217.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_1217.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_1217.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_1217.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_1217.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_1217.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = []; FStar_Tc_Env.top_level = _48_1217.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_1217.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_1217.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_1217.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_1217.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_1217.FStar_Tc_Env.default_effects})
in (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun b -> (match (b) with
| (FStar_Util.Inl (_48_1224), _48_1227) -> begin
[]
end
| (FStar_Util.Inr (x), _48_1232) -> begin
(match ((let _147_459 = (let _147_458 = (let _147_457 = (FStar_Absyn_Util.unrefine x.FStar_Absyn_Syntax.sort)
in (whnf env _147_457))
in (FStar_Absyn_Util.unrefine _147_458))
in _147_459.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_48_1235) -> begin
[]
end
| _48_1238 -> begin
(let _147_460 = (FStar_Absyn_Util.bvar_to_exp x)
in (_147_460)::[])
end)
end)))))
in (

let precedes = (FStar_Absyn_Util.ftv FStar_Absyn_Const.precedes_lid FStar_Absyn_Syntax.kun)
in (

let as_lex_list = (fun dec -> (

let _48_1245 = (FStar_Absyn_Util.head_and_args_e dec)
in (match (_48_1245) with
| (head, _48_1244) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _48_1248) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
dec
end
| _48_1252 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let prev_dec = (

let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _48_6 -> (match (_48_6) with
| FStar_Absyn_Syntax.DECREASES (_48_1256) -> begin
true
end
| _48_1259 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(

let _48_1263 = if ((FStar_List.length bs') <> (FStar_List.length actuals)) then begin
(let _147_469 = (let _147_468 = (let _147_467 = (let _147_465 = (FStar_Util.string_of_int (FStar_List.length bs'))
in (let _147_464 = (FStar_Util.string_of_int (FStar_List.length actuals))
in (FStar_Util.format2 "Decreases clause on a function with an unexpected number of arguments (expected %s; got %s)" _147_465 _147_464)))
in (let _147_466 = (FStar_Tc_Env.get_range env)
in ((_147_467), (_147_466))))
in FStar_Absyn_Syntax.Error (_147_468))
in (Prims.raise _147_469))
end else begin
()
end
in (

let dec = (as_lex_list dec)
in (

let subst = (FStar_List.map2 (fun b a -> (match (((b), (a))) with
| ((FStar_Util.Inl (formal), _48_1271), (FStar_Util.Inl (actual), _48_1276)) -> begin
(let _147_473 = (let _147_472 = (FStar_Absyn_Util.btvar_to_typ actual)
in ((formal.FStar_Absyn_Syntax.v), (_147_472)))
in FStar_Util.Inl (_147_473))
end
| ((FStar_Util.Inr (formal), _48_1282), (FStar_Util.Inr (actual), _48_1287)) -> begin
(let _147_475 = (let _147_474 = (FStar_Absyn_Util.bvar_to_exp actual)
in ((formal.FStar_Absyn_Syntax.v), (_147_474)))
in FStar_Util.Inr (_147_475))
end
| _48_1291 -> begin
(failwith "impossible")
end)) bs' actuals)
in (FStar_Absyn_Util.subst_exp subst dec))))
end
| _48_1294 -> begin
(

let actual_args = (FStar_All.pipe_right actuals filter_types_and_functions)
in (match (actual_args) with
| (i)::[] -> begin
i
end
| _48_1299 -> begin
(mk_lex_list actual_args)
end))
end))
in (

let letrecs = (FStar_All.pipe_right letrecs (FStar_List.map (fun _48_1303 -> (match (_48_1303) with
| (l, t0) -> begin
(

let t = (FStar_Absyn_Util.alpha_typ t0)
in (match ((let _147_477 = (FStar_Absyn_Util.compress_typ t)
in _147_477.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(match ((FStar_Util.prefix formals)) with
| (bs, (FStar_Util.Inr (x), imp)) -> begin
(

let y = (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.p x.FStar_Absyn_Syntax.sort)
in (

let ct = (FStar_Absyn_Util.comp_to_comp_typ c)
in (

let precedes = (match ((FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_List.tryFind (fun _48_7 -> (match (_48_7) with
| FStar_Absyn_Syntax.DECREASES (_48_1319) -> begin
true
end
| _48_1322 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.DECREASES (dec)) -> begin
(

let dec = (as_lex_list dec)
in (

let dec = (

let subst = (let _147_481 = (let _147_480 = (let _147_479 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_147_479)))
in FStar_Util.Inr (_147_480))
in (_147_481)::[])
in (FStar_Absyn_Util.subst_exp subst dec))
in (let _147_486 = (let _147_485 = (let _147_484 = (FStar_Absyn_Syntax.varg dec)
in (let _147_483 = (let _147_482 = (FStar_Absyn_Syntax.varg prev_dec)
in (_147_482)::[])
in (_147_484)::_147_483))
in ((precedes), (_147_485)))
in (FStar_Absyn_Syntax.mk_Typ_app _147_486 None r))))
end
| _48_1330 -> begin
(

let formal_args = (let _147_489 = (let _147_488 = (let _147_487 = (FStar_Absyn_Syntax.v_binder y)
in (_147_487)::[])
in (FStar_List.append bs _147_488))
in (FStar_All.pipe_right _147_489 filter_types_and_functions))
in (

let lhs = (match (formal_args) with
| (i)::[] -> begin
i
end
| _48_1335 -> begin
(mk_lex_list formal_args)
end)
in (let _147_494 = (let _147_493 = (let _147_492 = (FStar_Absyn_Syntax.varg lhs)
in (let _147_491 = (let _147_490 = (FStar_Absyn_Syntax.varg prev_dec)
in (_147_490)::[])
in (_147_492)::_147_491))
in ((precedes), (_147_493)))
in (FStar_Absyn_Syntax.mk_Typ_app _147_494 None r))))
end)
in (

let refined_domain = (FStar_Absyn_Syntax.mk_Typ_refine ((y), (precedes)) None r)
in (

let bs = (FStar_List.append bs ((((FStar_Util.Inr ((

let _48_1339 = x
in {FStar_Absyn_Syntax.v = _48_1339.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = refined_domain; FStar_Absyn_Syntax.p = _48_1339.FStar_Absyn_Syntax.p}))), (imp)))::[]))
in (

let t' = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None r)
in (

let _48_1343 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_497 = (FStar_Absyn_Print.lbname_to_string l)
in (let _147_496 = (FStar_Absyn_Print.typ_to_string t)
in (let _147_495 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _147_497 _147_496 _147_495))))
end else begin
()
end
in (

let _48_1350 = (let _147_499 = (let _147_498 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_498 Prims.fst))
in (tc_typ _147_499 t'))
in (match (_48_1350) with
| (t', _48_1347, _48_1349) -> begin
((l), (t'))
end)))))))))
end
| _48_1352 -> begin
(failwith "Impossible")
end)
end
| _48_1354 -> begin
(failwith "Impossible")
end))
end))))
in (let _147_505 = (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun env _48_1359 -> (match (_48_1359) with
| (x, t) -> begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end)) env))
in (let _147_504 = (FStar_All.pipe_right letrecs (FStar_List.collect (fun _48_8 -> (match (_48_8) with
| (FStar_Util.Inl (x), t) -> begin
(let _147_503 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_147_503)::[])
end
| _48_1366 -> begin
[]
end))))
in ((_147_505), (_147_504))))))))))))
end))
in (

let _48_1371 = (tc_binders (([]), (env), (FStar_Tc_Rel.trivial_guard), ([])) bs' c bs)
in (match (_48_1371) with
| (bs, envbody, g, c) -> begin
(

let _48_1374 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(mk_letrec_environment bs envbody)
end else begin
((envbody), ([]))
end
in (match (_48_1374) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_Tc_Env.set_expected_typ envbody (FStar_Absyn_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (g)))
end))
end))))
end
| FStar_Absyn_Syntax.Typ_refine (b, _48_1378) -> begin
(

let _48_1388 = (as_function_typ norm b.FStar_Absyn_Syntax.sort)
in (match (_48_1388) with
| (_48_1382, bs, bs', copt, env, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (g))
end))
end
| _48_1390 -> begin
if (not (norm)) then begin
(let _147_506 = (whnf env t)
in (as_function_typ true _147_506))
end else begin
(

let _48_1399 = (expected_function_typ env None)
in (match (_48_1399) with
| (_48_1392, bs, _48_1395, c_opt, envbody, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_Tc_Env.use_eq
in (

let _48_1403 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_48_1403) with
| (env, topt) -> begin
(

let _48_1410 = (expected_function_typ env topt)
in (match (_48_1410) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, g) -> begin
(

let _48_1416 = (tc_exp (

let _48_1411 = envbody
in {FStar_Tc_Env.solver = _48_1411.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_1411.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_1411.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_1411.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_1411.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_1411.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_1411.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_1411.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_1411.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_1411.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_1411.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_1411.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_1411.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_1411.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = false; FStar_Tc_Env.check_uvars = _48_1411.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _48_1411.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_1411.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_1411.FStar_Tc_Env.default_effects}) body)
in (match (_48_1416) with
| (body, cbody, guard_body) -> begin
(

let _48_1417 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _147_509 = (FStar_Absyn_Print.exp_to_string body)
in (let _147_508 = (FStar_Absyn_Print.lcomp_typ_to_string cbody)
in (let _147_507 = (FStar_Tc_Rel.guard_to_string env guard_body)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!body %s has type %s\nguard is %s\n" _147_509 _147_508 _147_507))))
end else begin
()
end
in (

let guard_body = (FStar_Tc_Rel.solve_deferred_constraints envbody guard_body)
in (

let _48_1420 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _147_510 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in body of abstraction\n" _147_510))
end else begin
()
end
in (

let _48_1427 = (let _147_512 = (let _147_511 = (cbody.FStar_Absyn_Syntax.comp ())
in ((body), (_147_511)))
in (check_expected_effect (

let _48_1422 = envbody
in {FStar_Tc_Env.solver = _48_1422.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_1422.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_1422.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_1422.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_1422.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_1422.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_1422.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_1422.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_1422.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_1422.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_1422.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_1422.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_1422.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_1422.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_1422.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_1422.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = use_eq; FStar_Tc_Env.is_iface = _48_1422.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_1422.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_1422.FStar_Tc_Env.default_effects}) c_opt _147_512))
in (match (_48_1427) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_Tc_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_Tc_Env.top_level || (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)))) then begin
(

let _48_1429 = (let _147_513 = (FStar_Tc_Rel.conj_guard g guard)
in (FStar_Tc_Util.discharge_guard envbody _147_513))
in (

let _48_1431 = FStar_Tc_Rel.trivial_guard
in {FStar_Tc_Rel.guard_f = _48_1431.FStar_Tc_Rel.guard_f; FStar_Tc_Rel.deferred = _48_1431.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = guard.FStar_Tc_Rel.implicits}))
end else begin
(

let guard = (FStar_Tc_Rel.close_guard (FStar_List.append bs letrec_binders) guard)
in (FStar_Tc_Rel.conj_guard g guard))
end
in (

let tfun_computed = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (cbody)) (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos)
in (

let e = (let _147_515 = (let _147_514 = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) (Some (tfun_computed)) top.FStar_Absyn_Syntax.pos)
in ((_147_514), (tfun_computed), (Some (FStar_Absyn_Const.effect_Tot_lid))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _147_515 None top.FStar_Absyn_Syntax.pos))
in (

let _48_1454 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_48_1443) -> begin
(let _147_518 = (let _147_517 = (let _147_516 = (FStar_Absyn_Syntax.mk_Exp_abs ((bs), (body)) (Some (t)) e.FStar_Absyn_Syntax.pos)
in ((_147_516), (t), (Some (FStar_Absyn_Const.effect_Tot_lid))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _147_517 None top.FStar_Absyn_Syntax.pos))
in ((_147_518), (t), (guard)))
end
| _48_1446 -> begin
(

let _48_1449 = if use_teq then begin
(let _147_519 = (FStar_Tc_Rel.teq env t tfun_computed)
in ((e), (_147_519)))
end else begin
(FStar_Tc_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_48_1449) with
| (e, guard') -> begin
(let _147_521 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (t), (Some (FStar_Absyn_Const.effect_Tot_lid))) None top.FStar_Absyn_Syntax.pos)
in (let _147_520 = (FStar_Tc_Rel.conj_guard guard guard')
in ((_147_521), (t), (_147_520))))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_48_1454) with
| (e, tfun, guard) -> begin
(

let _48_1455 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_524 = (FStar_Absyn_Print.typ_to_string tfun)
in (let _147_523 = (FStar_Absyn_Print.tag_of_typ tfun)
in (let _147_522 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_Util.print3 "!!!!!!!!!!!!!!!Annotating lambda with type %s (%s)\nGuard is %s\n" _147_524 _147_523 _147_522))))
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

let _48_1460 = (let _147_526 = (FStar_Tc_Util.lcomp_of_comp c)
in (FStar_Tc_Util.strengthen_precondition None env e _147_526 guard))
in (match (_48_1460) with
| (c, g) -> begin
((e), (c), (g))
end))))
end))))))
end)))))
end))
end))
end)))))
end
| _48_1462 -> begin
(let _147_528 = (let _147_527 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format1 "Unexpected value: %s" _147_527))
in (failwith _147_528))
end))))
and tc_exp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun env e -> (

let env = if (e.FStar_Absyn_Syntax.pos = FStar_Absyn_Syntax.dummyRange) then begin
env
end else begin
(FStar_Tc_Env.set_range env e.FStar_Absyn_Syntax.pos)
end
in (

let _48_1466 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_533 = (let _147_531 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_531))
in (let _147_532 = (FStar_Absyn_Print.tag_of_exp e)
in (FStar_Util.print2 "%s (%s)\n" _147_533 _147_532)))
end else begin
()
end
in (

let w = (fun lc -> (FStar_All.pipe_left (FStar_Absyn_Syntax.syn e.FStar_Absyn_Syntax.pos) (Some (lc.FStar_Absyn_Syntax.res_typ))))
in (

let top = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_48_1472) -> begin
(let _147_557 = (FStar_Absyn_Util.compress_exp e)
in (tc_exp env _147_557))
end
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_abs (_)) -> begin
(tc_value env e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e1, t1, _48_1492) -> begin
(

let _48_1497 = (tc_typ_check env t1 FStar_Absyn_Syntax.ktype)
in (match (_48_1497) with
| (t1, f) -> begin
(

let _48_1501 = (let _147_558 = (FStar_Tc_Env.set_expected_typ env t1)
in (tc_exp _147_558 e1))
in (match (_48_1501) with
| (e1, c, g) -> begin
(

let _48_1505 = (let _147_562 = (FStar_Tc_Env.set_range env t1.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _48_1502 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _147_562 e1 c f))
in (match (_48_1505) with
| (c, f) -> begin
(

let _48_1509 = (let _147_566 = (let _147_565 = (w c)
in (FStar_All.pipe_left _147_565 (FStar_Absyn_Syntax.mk_Exp_ascribed ((e1), (t1), (Some (c.FStar_Absyn_Syntax.eff_name))))))
in (comp_check_expected_typ env _147_566 c))
in (match (_48_1509) with
| (e, c, f2) -> begin
(let _147_568 = (let _147_567 = (FStar_Tc_Rel.conj_guard g f2)
in (FStar_Tc_Rel.conj_guard f _147_567))
in ((e), (c), (_147_568)))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Meta_smt_pat)) -> begin
(

let pats_t = (let _147_574 = (let _147_573 = (let _147_569 = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.mk_Kind_type FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.list_lid _147_569))
in (let _147_572 = (let _147_571 = (let _147_570 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.pattern_lid FStar_Absyn_Syntax.mk_Kind_type)
in (FStar_Absyn_Syntax.targ _147_570))
in (_147_571)::[])
in ((_147_573), (_147_572))))
in (FStar_Absyn_Syntax.mk_Typ_app _147_574 None FStar_Absyn_Syntax.dummyRange))
in (

let _48_1519 = (let _147_575 = (FStar_Tc_Env.set_expected_typ env pats_t)
in (tc_ghost_exp _147_575 e))
in (match (_48_1519) with
| (e, t, g) -> begin
(

let g = (

let _48_1520 = g
in {FStar_Tc_Rel.guard_f = FStar_Tc_Rel.Trivial; FStar_Tc_Rel.deferred = _48_1520.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _48_1520.FStar_Tc_Rel.implicits})
in (

let c = (let _147_576 = (FStar_Absyn_Util.gtotal_comp pats_t)
in (FStar_All.pipe_right _147_576 FStar_Tc_Util.lcomp_of_comp))
in ((e), (c), (g))))
end)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, FStar_Absyn_Syntax.Sequence)) -> begin
(match ((let _147_577 = (FStar_Absyn_Util.compress_exp e)
in _147_577.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let ((_48_1530, ({FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = _48_1535; FStar_Absyn_Syntax.lbeff = _48_1533; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _48_1546 = (let _147_578 = (FStar_Tc_Env.set_expected_typ env FStar_Tc_Recheck.t_unit)
in (tc_exp _147_578 e1))
in (match (_48_1546) with
| (e1, c1, g1) -> begin
(

let _48_1550 = (tc_exp env e2)
in (match (_48_1550) with
| (e2, c2, g2) -> begin
(

let c = (FStar_Tc_Util.bind env (Some (e1)) c1 ((None), (c2)))
in (let _147_591 = (let _147_589 = (let _147_588 = (let _147_587 = (let _147_586 = (w c)
in (let _147_585 = (let _147_584 = (let _147_583 = (let _147_582 = (let _147_581 = (FStar_Absyn_Syntax.mk_lb ((x), (c1.FStar_Absyn_Syntax.eff_name), (FStar_Tc_Recheck.t_unit), (e1)))
in (_147_581)::[])
in ((false), (_147_582)))
in ((_147_583), (e2)))
in (FStar_Absyn_Syntax.mk_Exp_let _147_584))
in (FStar_All.pipe_left _147_586 _147_585)))
in ((_147_587), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_147_588))
in (FStar_Absyn_Syntax.mk_Exp_meta _147_589))
in (let _147_590 = (FStar_Tc_Rel.conj_guard g1 g2)
in ((_147_591), (c), (_147_590)))))
end))
end))
end
| _48_1553 -> begin
(

let _48_1557 = (tc_exp env e)
in (match (_48_1557) with
| (e, c, g) -> begin
(let _147_592 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Sequence)))))
in ((_147_592), (c), (g)))
end))
end)
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, i)) -> begin
(

let _48_1566 = (tc_exp env e)
in (match (_48_1566) with
| (e, c, g) -> begin
(let _147_593 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (i)))))
in ((_147_593), (c), (g)))
end))
end
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _147_595 = (let _147_594 = (FStar_Tc_Env.clear_expected_typ env)
in (FStar_All.pipe_right _147_594 Prims.fst))
in (FStar_All.pipe_right _147_595 instantiate_both))
in (

let _48_1573 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_597 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _147_596 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _147_597 _147_596)))
end else begin
()
end
in (

let _48_1578 = (tc_exp (no_inst env) head)
in (match (_48_1578) with
| (head, chead, g_head) -> begin
(

let aux = (fun _48_1580 -> (match (()) with
| () -> begin
(

let n_args = (FStar_List.length args)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _48_1584) when (((FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) || (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_Or)) && (n_args = (Prims.parse_int "2"))) -> begin
(

let env = (FStar_Tc_Env.set_expected_typ env FStar_Absyn_Util.t_bool)
in (match (args) with
| ((FStar_Util.Inr (e1), _48_1596))::((FStar_Util.Inr (e2), _48_1591))::[] -> begin
(

let _48_1602 = (tc_exp env e1)
in (match (_48_1602) with
| (e1, c1, g1) -> begin
(

let _48_1606 = (tc_exp env e2)
in (match (_48_1606) with
| (e2, c2, g2) -> begin
(

let x = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Util.t_bool)
in (

let xexp = (FStar_Absyn_Util.bvar_to_exp x)
in (

let c2 = if (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.op_And) then begin
(let _147_603 = (let _147_600 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _147_600))
in (let _147_602 = (let _147_601 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _147_601 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _147_603 c2 _147_602)))
end else begin
(let _147_607 = (let _147_604 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _147_604))
in (let _147_606 = (let _147_605 = (FStar_Tc_Util.return_value env FStar_Absyn_Util.t_bool xexp)
in (FStar_All.pipe_right _147_605 FStar_Tc_Util.lcomp_of_comp))
in (FStar_Tc_Util.ite env _147_607 _147_606 c2)))
end
in (

let c = (let _147_610 = (let _147_609 = (FStar_All.pipe_left (fun _147_608 -> Some (_147_608)) (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (FStar_Absyn_Util.t_bool)))))
in ((_147_609), (c2)))
in (FStar_Tc_Util.bind env None c1 _147_610))
in (

let e = (let _147_615 = (let _147_614 = (let _147_613 = (FStar_Absyn_Syntax.varg e1)
in (let _147_612 = (let _147_611 = (FStar_Absyn_Syntax.varg e2)
in (_147_611)::[])
in (_147_613)::_147_612))
in ((head), (_147_614)))
in (FStar_Absyn_Syntax.mk_Exp_app _147_615 (Some (FStar_Absyn_Util.t_bool)) top.FStar_Absyn_Syntax.pos))
in (let _147_617 = (let _147_616 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard g_head _147_616))
in ((e), (c), (_147_617))))))))
end))
end))
end
| _48_1613 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Expected two boolean arguments"), (head.FStar_Absyn_Syntax.pos)))))
end))
end
| _48_1615 -> begin
(

let thead = chead.FStar_Absyn_Syntax.res_typ
in (

let _48_1617 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_619 = (FStar_Range.string_of_range head.FStar_Absyn_Syntax.pos)
in (let _147_618 = (FStar_Absyn_Print.typ_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _147_619 _147_618)))
end else begin
()
end
in (

let rec check_function_app = (fun norm tf -> (match ((let _147_624 = (FStar_Absyn_Util.unrefine tf)
in _147_624.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_Tc_Rel.trivial_guard))
end
| ((FStar_Util.Inl (t), _48_1650))::_48_1646 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Explicit type applications on a term with unknown type; add an annotation?"), (t.FStar_Absyn_Syntax.pos)))))
end
| ((FStar_Util.Inr (e), imp))::tl -> begin
(

let _48_1662 = (tc_exp env e)
in (match (_48_1662) with
| (e, c, g_e) -> begin
(

let _48_1666 = (tc_args env tl)
in (match (_48_1666) with
| (args, comps, g_rest) -> begin
(let _147_629 = (FStar_Tc_Rel.conj_guard g_e g_rest)
in (((((FStar_Util.Inr (e)), (imp)))::args), ((c)::comps), (_147_629)))
end))
end))
end))
in (

let _48_1670 = (tc_args env args)
in (match (_48_1670) with
| (args, comps, g_args) -> begin
(

let bs = (let _147_630 = (FStar_Tc_Util.tks_of_args args)
in (FStar_Absyn_Util.null_binders_of_tks _147_630))
in (

let cres = (let _147_631 = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ml_comp _147_631 top.FStar_Absyn_Syntax.pos))
in (

let _48_1673 = (let _147_633 = (let _147_632 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (cres)) (Some (FStar_Absyn_Syntax.ktype)) tf.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Rel.teq env tf _147_632))
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _147_633))
in (

let comp = (let _147_636 = (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun c out -> (FStar_Tc_Util.bind env None c ((None), (out)))) ((chead)::comps) _147_636))
in (let _147_638 = (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)) (Some (comp.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (let _147_637 = (FStar_Tc_Rel.conj_guard g_head g_args)
in ((_147_638), (comp), (_147_637))))))))
end)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let vars = (FStar_Tc_Env.binders env)
in (

let rec tc_args = (fun _48_1690 bs cres args -> (match (_48_1690) with
| (subst, outargs, arg_rets, comps, g, fvs) -> begin
(match (((bs), (args))) with
| (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (_48_1698))))::rest, ((_48_1706, None))::_48_1704) -> begin
(

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _48_1712 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (

let _48_1716 = (let _147_648 = (let _147_647 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _147_647))
in (FStar_Tc_Rel.new_tvar _147_648 vars k))
in (match (_48_1716) with
| (targ, u) -> begin
(

let _48_1717 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_650 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _147_649 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Instantiating %s to %s" _147_650 _147_649)))
end else begin
()
end
in (

let subst = (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (targ))))::subst
in (

let arg = (let _147_651 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inl (targ)), (_147_651)))
in (let _147_656 = (let _147_655 = (let _147_654 = (let _147_653 = (let _147_652 = (FStar_Tc_Util.as_uvar_t u)
in ((_147_652), (u.FStar_Absyn_Syntax.pos)))
in FStar_Util.Inl (_147_653))
in (add_implicit _147_654 g))
in ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (_147_655), (fvs)))
in (tc_args _147_656 rest cres args)))))
end))))
end
| (((FStar_Util.Inr (x), Some (FStar_Absyn_Syntax.Implicit (_48_1725))))::rest, ((_48_1733, None))::_48_1731) -> begin
(

let t = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _48_1739 = (fxv_check head env (FStar_Util.Inr (t)) fvs)
in (

let _48_1743 = (FStar_Tc_Util.new_implicit_evar env t)
in (match (_48_1743) with
| (varg, u) -> begin
(

let subst = (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (varg))))::subst
in (

let arg = (let _147_657 = (FStar_Absyn_Syntax.as_implicit true)
in ((FStar_Util.Inr (varg)), (_147_657)))
in (tc_args ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), ((add_implicit (FStar_Util.Inr (u)) g)), (fvs)) rest cres args)))
end))))
end
| (((FStar_Util.Inl (a), aqual))::rest, ((FStar_Util.Inl (t), aq))::rest') -> begin
(

let _48_1759 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_659 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (let _147_658 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "\tGot a type arg for %s = %s\n" _147_659 _147_658)))
end else begin
()
end
in (

let k = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _48_1762 = (fxv_check head env (FStar_Util.Inl (k)) fvs)
in (

let _48_1768 = (tc_typ_check (

let _48_1764 = env
in {FStar_Tc_Env.solver = _48_1764.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_1764.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_1764.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_1764.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_1764.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_1764.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_1764.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_1764.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_1764.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_1764.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_1764.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_1764.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_1764.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_1764.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_1764.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_1764.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _48_1764.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_1764.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_1764.FStar_Tc_Env.default_effects}) t k)
in (match (_48_1768) with
| (t, g') -> begin
(

let f = (let _147_660 = (FStar_Tc_Rel.guard_form g')
in (FStar_Tc_Util.label_guard FStar_Tc_Errors.ill_kinded_type t.FStar_Absyn_Syntax.pos _147_660))
in (

let g' = (

let _48_1770 = g'
in {FStar_Tc_Rel.guard_f = f; FStar_Tc_Rel.deferred = _48_1770.FStar_Tc_Rel.deferred; FStar_Tc_Rel.implicits = _48_1770.FStar_Tc_Rel.implicits})
in (

let arg = ((FStar_Util.Inl (t)), (aq))
in (

let subst = (let _147_661 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_661 arg))
in (let _147_663 = (let _147_662 = (FStar_Tc_Rel.conj_guard g g')
in ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (_147_662), (fvs)))
in (tc_args _147_663 rest cres rest'))))))
end)))))
end
| (((FStar_Util.Inr (x), aqual))::rest, ((FStar_Util.Inr (e), aq))::rest') -> begin
(

let _48_1788 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_665 = (FStar_Absyn_Print.subst_to_string subst)
in (let _147_664 = (FStar_Absyn_Print.typ_to_string x.FStar_Absyn_Syntax.sort)
in (FStar_Util.print2 "\tType of arg (before subst (%s)) = %s\n" _147_665 _147_664)))
end else begin
()
end
in (

let targ = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _48_1791 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_666 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _147_666))
end else begin
()
end
in (

let _48_1793 = (fxv_check head env (FStar_Util.Inr (targ)) fvs)
in (

let env = (FStar_Tc_Env.set_expected_typ env targ)
in (

let env = (

let _48_1796 = env
in {FStar_Tc_Env.solver = _48_1796.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_1796.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_1796.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_1796.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_1796.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_1796.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_1796.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_1796.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_1796.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_1796.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_1796.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_1796.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_1796.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_1796.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_1796.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_1796.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = (is_eq aqual); FStar_Tc_Env.is_iface = _48_1796.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_1796.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_1796.FStar_Tc_Env.default_effects})
in (

let _48_1799 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) && env.FStar_Tc_Env.use_eq) then begin
(let _147_668 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_667 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print2 "Checking arg %s at type %s with an equality constraint!\n" _147_668 _147_667)))
end else begin
()
end
in (

let _48_1801 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_671 = (FStar_Absyn_Print.tag_of_exp e)
in (let _147_670 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_669 = (FStar_Absyn_Print.typ_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _147_671 _147_670 _147_669))))
end else begin
()
end
in (

let _48_1806 = (tc_exp env e)
in (match (_48_1806) with
| (e, c, g_e) -> begin
(

let g = (FStar_Tc_Rel.conj_guard g g_e)
in (

let _48_1808 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_673 = (FStar_Tc_Rel.guard_to_string env g_e)
in (let _147_672 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print2 "Guard on this arg is %s;\naccumulated guard is %s\n" _147_673 _147_672)))
end else begin
()
end
in (

let arg = ((FStar_Util.Inr (e)), (aq))
in if (FStar_Absyn_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _147_674 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_674 arg))
in (tc_args ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (g), (fvs)) rest cres rest'))
end else begin
if (FStar_Tc_Util.is_pure_or_ghost_effect env c.FStar_Absyn_Syntax.eff_name) then begin
(

let subst = (let _147_675 = (FStar_List.hd bs)
in (maybe_extend_subst subst _147_675 arg))
in (

let _48_1815 = (((((Some (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (targ))))), (c)))::comps), (g))
in (match (_48_1815) with
| (comps, guard) -> begin
(tc_args ((subst), ((arg)::outargs), ((arg)::arg_rets), (comps), (guard), (fvs)) rest cres rest')
end)))
end else begin
if (let _147_676 = (FStar_List.hd bs)
in (FStar_Absyn_Syntax.is_null_binder _147_676)) then begin
(

let newx = (FStar_Absyn_Util.gen_bvar_p e.FStar_Absyn_Syntax.pos c.FStar_Absyn_Syntax.res_typ)
in (

let arg' = (let _147_677 = (FStar_Absyn_Util.bvar_to_exp newx)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _147_677))
in (

let binding = FStar_Tc_Env.Binding_var (((newx.FStar_Absyn_Syntax.v), (newx.FStar_Absyn_Syntax.sort)))
in (tc_args ((subst), ((arg)::outargs), ((arg')::arg_rets), ((((Some (binding)), (c)))::comps), (g), (fvs)) rest cres rest'))))
end else begin
(let _147_686 = (let _147_685 = (let _147_679 = (let _147_678 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _147_678))
in (_147_679)::arg_rets)
in (let _147_684 = (let _147_682 = (let _147_681 = (FStar_All.pipe_left (fun _147_680 -> Some (_147_680)) (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (targ)))))
in ((_147_681), (c)))
in (_147_682)::comps)
in (let _147_683 = (FStar_Util.set_add x fvs)
in ((subst), ((arg)::outargs), (_147_685), (_147_684), (g), (_147_683)))))
in (tc_args _147_686 rest cres rest'))
end
end
end)))
end))))))))))
end
| (((FStar_Util.Inr (_48_1822), _48_1825))::_48_1820, ((FStar_Util.Inl (_48_1831), _48_1834))::_48_1829) -> begin
(let _147_690 = (let _147_689 = (let _147_688 = (let _147_687 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _147_687))
in (("Expected an expression; got a type"), (_147_688)))
in FStar_Absyn_Syntax.Error (_147_689))
in (Prims.raise _147_690))
end
| (((FStar_Util.Inl (_48_1841), _48_1844))::_48_1839, ((FStar_Util.Inr (_48_1850), _48_1853))::_48_1848) -> begin
(let _147_694 = (let _147_693 = (let _147_692 = (let _147_691 = (FStar_List.hd args)
in (FStar_Absyn_Util.range_of_arg _147_691))
in (("Expected a type; got an expression"), (_147_692)))
in FStar_Absyn_Syntax.Error (_147_693))
in (Prims.raise _147_694))
end
| (_48_1858, []) -> begin
(

let _48_1861 = (fxv_check head env (FStar_Util.Inr (cres.FStar_Absyn_Syntax.res_typ)) fvs)
in (

let _48_1879 = (match (bs) with
| [] -> begin
(

let cres = (FStar_Tc_Util.subst_lcomp subst cres)
in (

let g = (FStar_Tc_Rel.conj_guard g_head g)
in (

let refine_with_equality = ((FStar_Absyn_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right comps (FStar_Util.for_some (fun _48_1869 -> (match (_48_1869) with
| (_48_1867, c) -> begin
(not ((FStar_Absyn_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _147_696 = (FStar_Absyn_Syntax.mk_Exp_app_flat ((head), ((FStar_List.rev arg_rets))) (Some (cres.FStar_Absyn_Syntax.res_typ)) top.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.maybe_assume_result_eq_pure_term env _147_696 cres))
end else begin
(

let _48_1871 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_699 = (FStar_Absyn_Print.exp_to_string head)
in (let _147_698 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (let _147_697 = (FStar_Tc_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _147_699 _147_698 _147_697))))
end else begin
()
end
in cres)
end
in (let _147_700 = (FStar_Tc_Util.refresh_comp_label env false cres)
in ((_147_700), (g)))))))
end
| _48_1875 -> begin
(

let g = (let _147_701 = (FStar_Tc_Rel.conj_guard g_head g)
in (FStar_All.pipe_right _147_701 (FStar_Tc_Rel.solve_deferred_constraints env)))
in (let _147_707 = (let _147_706 = (let _147_705 = (let _147_704 = (let _147_703 = (let _147_702 = (cres.FStar_Absyn_Syntax.comp ())
in ((bs), (_147_702)))
in (FStar_Absyn_Syntax.mk_Typ_fun _147_703 (Some (FStar_Absyn_Syntax.ktype)) top.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (FStar_Absyn_Util.subst_typ subst) _147_704))
in (FStar_Absyn_Syntax.mk_Total _147_705))
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _147_706))
in ((_147_707), (g))))
end)
in (match (_48_1879) with
| (cres, g) -> begin
(

let _48_1880 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_708 = (FStar_Absyn_Print.lcomp_typ_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _147_708))
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

let _48_1889 = (FStar_Tc_Util.strengthen_precondition None env app comp g)
in (match (_48_1889) with
| (comp, g) -> begin
(

let _48_1890 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_714 = (FStar_Tc_Normalize.exp_norm_to_string env app)
in (let _147_713 = (let _147_712 = (comp.FStar_Absyn_Syntax.comp ())
in (FStar_Absyn_Print.comp_typ_to_string _147_712))
in (FStar_Util.print2 "\t Type of app term %s is %s\n" _147_714 _147_713)))
end else begin
()
end
in ((app), (comp), (g)))
end))))))
end)))
end
| ([], (arg)::_48_1894) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _147_719 = (FStar_Absyn_Util.compress_typ tres)
in (FStar_All.pipe_right _147_719 FStar_Absyn_Util.unrefine))
in (match (tres.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, cres') -> begin
(

let _48_1906 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_720 = (FStar_Range.string_of_range tres.FStar_Absyn_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _147_720))
end else begin
()
end
in (let _147_721 = (FStar_Tc_Util.lcomp_of_comp cres')
in (tc_args ((subst), (outargs), (arg_rets), ((((None), (cres)))::comps), (g), (fvs)) bs _147_721 args)))
end
| _48_1909 when (not (norm)) -> begin
(let _147_722 = (whnf env tres)
in (aux true _147_722))
end
| _48_1911 -> begin
(let _147_728 = (let _147_727 = (let _147_726 = (let _147_724 = (FStar_Tc_Normalize.typ_norm_to_string env tf)
in (let _147_723 = (FStar_Absyn_Print.exp_to_string top)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s" _147_724 _147_723)))
in (let _147_725 = (FStar_Absyn_Syntax.argpos arg)
in ((_147_726), (_147_725))))
in FStar_Absyn_Syntax.Error (_147_727))
in (Prims.raise _147_728))
end)))
in (aux false cres.FStar_Absyn_Syntax.res_typ))
end)
end))
in (let _147_729 = (FStar_Tc_Util.lcomp_of_comp c)
in (tc_args (([]), ([]), ([]), ([]), (FStar_Tc_Rel.trivial_guard), (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)) bs _147_729 args))))
end
| _48_1913 -> begin
if (not (norm)) then begin
(let _147_730 = (whnf env tf)
in (check_function_app true _147_730))
end else begin
(let _147_733 = (let _147_732 = (let _147_731 = (FStar_Tc_Errors.expected_function_typ env tf)
in ((_147_731), (head.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_732))
in (Prims.raise _147_733))
end
end))
in (let _147_734 = (FStar_Absyn_Util.unrefine thead)
in (check_function_app false _147_734)))))
end))
end))
in (

let _48_1917 = (aux ())
in (match (_48_1917) with
| (e, c, g) -> begin
(

let _48_1918 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _147_735 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length g.FStar_Tc_Rel.implicits))
in (FStar_Util.print1 "Introduced %s implicits in application\n" _147_735))
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

let _48_1925 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_740 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _147_739 = (FStar_Absyn_Print.typ_to_string c.FStar_Absyn_Syntax.res_typ)
in (let _147_738 = (let _147_737 = (FStar_Tc_Env.expected_typ env0)
in (FStar_All.pipe_right _147_737 (fun x -> (match (x) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.typ_to_string t)
end))))
in (FStar_Util.print3 "(%s) About to check %s against expected typ %s\n" _147_740 _147_739 _147_738))))
end else begin
()
end
in (

let _48_1930 = (comp_check_expected_typ env0 e c)
in (match (_48_1930) with
| (e, c, g') -> begin
(let _147_741 = (FStar_Tc_Rel.conj_guard g g')
in ((e), (c), (_147_741)))
end)))))
end)))
end)))))
end
| FStar_Absyn_Syntax.Exp_match (e1, eqns) -> begin
(

let _48_1937 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_48_1937) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _48_1942 = (tc_exp env1 e1)
in (match (_48_1942) with
| (e1, c1, g1) -> begin
(

let _48_1949 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let res_t = (FStar_Tc_Util.new_tvar env FStar_Absyn_Syntax.ktype)
in (let _147_742 = (FStar_Tc_Env.set_expected_typ env res_t)
in ((_147_742), (res_t))))
end)
in (match (_48_1949) with
| (env_branches, res_t) -> begin
(

let guard_x = (let _147_744 = (FStar_All.pipe_left (fun _147_743 -> Some (_147_743)) e1.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.new_bvd _147_744))
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x c1.FStar_Absyn_Syntax.res_typ env_branches)))
in (

let _48_1966 = (

let _48_1963 = (FStar_List.fold_right (fun _48_1957 _48_1960 -> (match (((_48_1957), (_48_1960))) with
| ((_48_1953, f, c, g), (caccum, gaccum)) -> begin
(let _147_747 = (FStar_Tc_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_147_747)))
end)) t_eqns (([]), (FStar_Tc_Rel.trivial_guard)))
in (match (_48_1963) with
| (cases, g) -> begin
(let _147_748 = (FStar_Tc_Util.bind_cases env res_t cases)
in ((_147_748), (g)))
end))
in (match (_48_1966) with
| (c_branches, g_branches) -> begin
(

let _48_1967 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_752 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _147_751 = (FStar_Absyn_Print.lcomp_typ_to_string c1)
in (let _147_750 = (FStar_Absyn_Print.lcomp_typ_to_string c_branches)
in (let _147_749 = (FStar_Tc_Rel.guard_to_string env g_branches)
in (FStar_Util.print4 "(%s) comp\n\tscrutinee: %s\n\tbranches: %s\nguard = %s\n" _147_752 _147_751 _147_750 _147_749)))))
end else begin
()
end
in (

let cres = (let _147_755 = (let _147_754 = (FStar_All.pipe_left (fun _147_753 -> Some (_147_753)) (FStar_Tc_Env.Binding_var (((guard_x), (c1.FStar_Absyn_Syntax.res_typ)))))
in ((_147_754), (c_branches)))
in (FStar_Tc_Util.bind env (Some (e1)) c1 _147_755))
in (

let e = (let _147_762 = (w cres)
in (let _147_761 = (let _147_760 = (let _147_759 = (FStar_List.map (fun _48_1977 -> (match (_48_1977) with
| (f, _48_1972, _48_1974, _48_1976) -> begin
f
end)) t_eqns)
in ((e1), (_147_759)))
in (FStar_Absyn_Syntax.mk_Exp_match _147_760))
in (FStar_All.pipe_left _147_762 _147_761)))
in (let _147_764 = (FStar_Absyn_Syntax.mk_Exp_ascribed ((e), (cres.FStar_Absyn_Syntax.res_typ), (Some (cres.FStar_Absyn_Syntax.eff_name))) None e.FStar_Absyn_Syntax.pos)
in (let _147_763 = (FStar_Tc_Rel.conj_guard g1 g_branches)
in ((_147_764), (cres), (_147_763)))))))
end))))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _48_1982; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let env = (instantiate_both env)
in (

let env0 = env
in (

let topt = (FStar_Tc_Env.expected_typ env)
in (

let top_level = (match (x) with
| FStar_Util.Inr (_48_1995) -> begin
true
end
| _48_1998 -> begin
false
end)
in (

let _48_2003 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_48_2003) with
| (env1, _48_2002) -> begin
(

let _48_2016 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
((FStar_Tc_Rel.trivial_guard), (env1))
end
| _48_2006 -> begin
if (top_level && (not (env.FStar_Tc_Env.generalize))) then begin
(let _147_765 = (FStar_Tc_Env.set_expected_typ env1 t)
in ((FStar_Tc_Rel.trivial_guard), (_147_765)))
end else begin
(

let _48_2009 = (tc_typ_check env1 t FStar_Absyn_Syntax.ktype)
in (match (_48_2009) with
| (t, f) -> begin
(

let _48_2010 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _147_767 = (FStar_Range.string_of_range top.FStar_Absyn_Syntax.pos)
in (let _147_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _147_767 _147_766)))
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
in (match (_48_2016) with
| (f, env1) -> begin
(

let _48_2022 = (tc_exp (

let _48_2017 = env1
in {FStar_Tc_Env.solver = _48_2017.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_2017.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_2017.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_2017.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_2017.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_2017.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_2017.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_2017.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_2017.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_2017.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_2017.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_2017.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_2017.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_2017.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = top_level; FStar_Tc_Env.check_uvars = _48_2017.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_2017.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_2017.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_2017.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_2017.FStar_Tc_Env.default_effects}) e1)
in (match (_48_2022) with
| (e1, c1, g1) -> begin
(

let _48_2026 = (let _147_771 = (FStar_Tc_Env.set_range env t.FStar_Absyn_Syntax.pos)
in (FStar_Tc_Util.strengthen_precondition (Some ((fun _48_2023 -> (match (()) with
| () -> begin
FStar_Tc_Errors.ill_kinded_type
end)))) _147_771 e1 c1 f))
in (match (_48_2026) with
| (c1, guard_f) -> begin
(match (x) with
| FStar_Util.Inr (_48_2028) -> begin
(

let _48_2042 = if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(

let _48_2032 = (let _147_772 = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (FStar_Tc_Util.check_top_level env _147_772 c1))
in (match (_48_2032) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _48_2033 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _147_773 = (FStar_Tc_Env.get_range env)
in (FStar_Tc_Errors.warn _147_773 FStar_Tc_Errors.top_level_effect))
end else begin
()
end
in (let _147_774 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e2), (FStar_Absyn_Syntax.Masked_effect)))))
in ((_147_774), (c1))))
end
end))
end else begin
(

let g = (FStar_Tc_Rel.conj_guard g1 guard_f)
in (

let _48_2036 = (FStar_Tc_Util.discharge_guard env g)
in (

let _48_2038 = (FStar_Tc_Util.check_unresolved_implicits g)
in (let _147_775 = (c1.FStar_Absyn_Syntax.comp ())
in ((e2), (_147_775))))))
end
in (match (_48_2042) with
| (e2, c1) -> begin
(

let _48_2047 = if env.FStar_Tc_Env.generalize then begin
(let _147_776 = (FStar_Tc_Util.generalize false env1 ((((x), (e1), (c1)))::[]))
in (FStar_All.pipe_left FStar_List.hd _147_776))
end else begin
((x), (e1), (c1))
end
in (match (_48_2047) with
| (_48_2044, e1, c1) -> begin
(

let cres = (let _147_777 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _147_777))
in (

let cres = if (FStar_Absyn_Util.is_total_comp c1) then begin
cres
end else begin
(let _147_778 = (FStar_Tc_Util.lcomp_of_comp c1)
in (FStar_Tc_Util.bind env None _147_778 ((None), (cres))))
end
in (

let _48_2050 = (FStar_ST.op_Colon_Equals e2.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _147_787 = (let _147_786 = (w cres)
in (let _147_785 = (let _147_784 = (let _147_783 = (let _147_782 = (let _147_781 = (FStar_Absyn_Syntax.mk_lb ((x), ((FStar_Absyn_Util.comp_effect_name c1)), ((FStar_Absyn_Util.comp_result c1)), (e1)))
in (_147_781)::[])
in ((false), (_147_782)))
in ((_147_783), (e2)))
in (FStar_Absyn_Syntax.mk_Exp_let _147_784))
in (FStar_All.pipe_left _147_786 _147_785)))
in ((_147_787), (cres), (FStar_Tc_Rel.trivial_guard))))))
end))
end))
end
| FStar_Util.Inl (bvd) -> begin
(

let b = (binding_of_lb x c1.FStar_Absyn_Syntax.res_typ)
in (

let _48_2058 = (let _147_788 = (FStar_Tc_Env.push_local_binding env b)
in (tc_exp _147_788 e2))
in (match (_48_2058) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_Tc_Util.bind env (Some (e1)) c1 ((Some (b)), (c2)))
in (

let e = (let _147_796 = (w cres)
in (let _147_795 = (let _147_794 = (let _147_793 = (let _147_792 = (let _147_791 = (FStar_Absyn_Syntax.mk_lb ((x), (c1.FStar_Absyn_Syntax.eff_name), (c1.FStar_Absyn_Syntax.res_typ), (e1)))
in (_147_791)::[])
in ((false), (_147_792)))
in ((_147_793), (e2)))
in (FStar_Absyn_Syntax.mk_Exp_let _147_794))
in (FStar_All.pipe_left _147_796 _147_795)))
in (

let g2 = (let _147_805 = (let _147_798 = (let _147_797 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s bvd c1.FStar_Absyn_Syntax.res_typ))
in (_147_797)::[])
in (FStar_Tc_Rel.close_guard _147_798))
in (let _147_804 = (let _147_803 = (let _147_802 = (let _147_801 = (let _147_800 = (FStar_Absyn_Util.bvd_to_exp bvd c1.FStar_Absyn_Syntax.res_typ)
in (FStar_Absyn_Util.mk_eq c1.FStar_Absyn_Syntax.res_typ c1.FStar_Absyn_Syntax.res_typ _147_800 e1))
in (FStar_All.pipe_left (fun _147_799 -> FStar_Tc_Rel.NonTrivial (_147_799)) _147_801))
in (FStar_Tc_Rel.guard_of_guard_formula _147_802))
in (FStar_Tc_Rel.imp_guard _147_803 g2))
in (FStar_All.pipe_left _147_805 _147_804)))
in (

let guard = (let _147_806 = (FStar_Tc_Rel.conj_guard g1 g2)
in (FStar_Tc_Rel.conj_guard guard_f _147_806))
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

let _48_2067 = (let _147_807 = (FStar_Tc_Rel.teq env tres t)
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _147_807))
in ((e), (cres), (guard))))
end else begin
((e), (cres), (guard))
end))
end
| _48_2070 -> begin
((e), (cres), (guard))
end)))))
end)))
end)
end))
end))
end))
end))))))
end
| FStar_Absyn_Syntax.Exp_let ((false, _48_2073), _48_2076) -> begin
(failwith "impossible")
end
| FStar_Absyn_Syntax.Exp_let ((true, lbs), e1) -> begin
(

let env = (instantiate_both env)
in (

let _48_2088 = (FStar_Tc_Env.clear_expected_typ env)
in (match (_48_2088) with
| (env0, topt) -> begin
(

let is_inner_let = (FStar_All.pipe_right lbs (FStar_Util.for_some (fun _48_9 -> (match (_48_9) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_48_2097); FStar_Absyn_Syntax.lbtyp = _48_2095; FStar_Absyn_Syntax.lbeff = _48_2093; FStar_Absyn_Syntax.lbdef = _48_2091} -> begin
true
end
| _48_2101 -> begin
false
end))))
in (

let _48_2126 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _48_2105 _48_2111 -> (match (((_48_2105), (_48_2111))) with
| ((xts, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _48_2108; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let _48_2116 = (FStar_Tc_Util.extract_lb_annotation env t e)
in (match (_48_2116) with
| (_48_2113, t, check_t) -> begin
(

let e = (FStar_Absyn_Util.unascribe e)
in (

let t = if (not (check_t)) then begin
t
end else begin
(let _147_811 = (tc_typ_check_trivial (

let _48_2118 = env0
in {FStar_Tc_Env.solver = _48_2118.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_2118.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_2118.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_2118.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_2118.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_2118.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_2118.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_2118.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_2118.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_2118.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_2118.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_2118.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_2118.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_2118.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_2118.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = true; FStar_Tc_Env.use_eq = _48_2118.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_2118.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_2118.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_2118.FStar_Tc_Env.default_effects}) t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _147_811 (norm_t env)))
end
in (

let env = if ((FStar_Absyn_Util.is_pure_or_ghost_function t) && (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str)) then begin
(

let _48_2121 = env
in {FStar_Tc_Env.solver = _48_2121.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_2121.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_2121.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_2121.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_2121.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_2121.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_2121.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_2121.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_2121.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_2121.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_2121.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_2121.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_2121.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = (((x), (t)))::env.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_2121.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_2121.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_2121.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_2121.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_2121.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_2121.FStar_Tc_Env.default_effects})
end else begin
(FStar_Tc_Env.push_local_binding env (binding_of_lb x t))
end
in (((((x), (t), (e)))::xts), (env)))))
end))
end)) (([]), (env))))
in (match (_48_2126) with
| (lbs, env') -> begin
(

let _48_2141 = (let _147_817 = (let _147_816 = (FStar_All.pipe_right lbs FStar_List.rev)
in (FStar_All.pipe_right _147_816 (FStar_List.map (fun _48_2130 -> (match (_48_2130) with
| (x, t, e) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t)
in (

let _48_2132 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_815 = (FStar_Absyn_Print.lbname_to_string x)
in (let _147_814 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_813 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print3 "Checking %s = %s against type %s\n" _147_815 _147_814 _147_813))))
end else begin
()
end
in (

let env' = (FStar_Tc_Env.set_expected_typ env' t)
in (

let _48_2138 = (tc_total_exp env' e)
in (match (_48_2138) with
| (e, t, g) -> begin
((((x), (t), (e))), (g))
end)))))
end)))))
in (FStar_All.pipe_right _147_817 FStar_List.unzip))
in (match (_48_2141) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_Tc_Rel.conj_guard gs FStar_Tc_Rel.trivial_guard)
in (

let _48_2160 = if ((not (env.FStar_Tc_Env.generalize)) || is_inner_let) then begin
(let _147_819 = (FStar_List.map (fun _48_2146 -> (match (_48_2146) with
| (x, t, e) -> begin
(FStar_Absyn_Syntax.mk_lb ((x), (FStar_Absyn_Const.effect_Tot_lid), (t), (e)))
end)) lbs)
in ((_147_819), (g_lbs)))
end else begin
(

let _48_2147 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (

let ecs = (let _147_822 = (FStar_All.pipe_right lbs (FStar_List.map (fun _48_2152 -> (match (_48_2152) with
| (x, t, e) -> begin
(let _147_821 = (FStar_All.pipe_left (FStar_Absyn_Util.total_comp t) (FStar_Absyn_Util.range_of_lb ((x), (t), (e))))
in ((x), (e), (_147_821)))
end))))
in (FStar_Tc_Util.generalize true env _147_822))
in (let _147_824 = (FStar_List.map (fun _48_2157 -> (match (_48_2157) with
| (x, e, c) -> begin
(FStar_Absyn_Syntax.mk_lb ((x), (FStar_Absyn_Const.effect_Tot_lid), ((FStar_Absyn_Util.comp_result c)), (e)))
end)) ecs)
in ((_147_824), (FStar_Tc_Rel.trivial_guard)))))
end
in (match (_48_2160) with
| (lbs, g_lbs) -> begin
if (not (is_inner_let)) then begin
(

let cres = (let _147_825 = (FStar_Absyn_Util.total_comp FStar_Tc_Recheck.t_unit top.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Tc_Util.lcomp_of_comp _147_825))
in (

let _48_2162 = (FStar_Tc_Util.discharge_guard env g_lbs)
in (

let _48_2164 = (FStar_ST.op_Colon_Equals e1.FStar_Absyn_Syntax.tk (Some (FStar_Tc_Recheck.t_unit)))
in (let _147_829 = (let _147_828 = (w cres)
in (FStar_All.pipe_left _147_828 (FStar_Absyn_Syntax.mk_Exp_let ((((true), (lbs))), (e1)))))
in ((_147_829), (cres), (FStar_Tc_Rel.trivial_guard))))))
end else begin
(

let _48_2180 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun _48_2168 _48_2175 -> (match (((_48_2168), (_48_2175))) with
| ((bindings, env), {FStar_Absyn_Syntax.lbname = x; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _48_2172; FStar_Absyn_Syntax.lbdef = _48_2170}) -> begin
(

let b = (binding_of_lb x t)
in (

let env = (FStar_Tc_Env.push_local_binding env b)
in (((b)::bindings), (env))))
end)) (([]), (env))))
in (match (_48_2180) with
| (bindings, env) -> begin
(

let _48_2184 = (tc_exp env e1)
in (match (_48_2184) with
| (e1, cres, g1) -> begin
(

let guard = (FStar_Tc_Rel.conj_guard g_lbs g1)
in (

let cres = (FStar_Tc_Util.close_comp env bindings cres)
in (

let tres = (norm_t env cres.FStar_Absyn_Syntax.res_typ)
in (

let cres = (

let _48_2188 = cres
in {FStar_Absyn_Syntax.eff_name = _48_2188.FStar_Absyn_Syntax.eff_name; FStar_Absyn_Syntax.res_typ = tres; FStar_Absyn_Syntax.cflags = _48_2188.FStar_Absyn_Syntax.cflags; FStar_Absyn_Syntax.comp = _48_2188.FStar_Absyn_Syntax.comp})
in (

let e = (let _147_834 = (w cres)
in (FStar_All.pipe_left _147_834 (FStar_Absyn_Syntax.mk_Exp_let ((((true), (lbs))), (e1)))))
in (match (topt) with
| Some (_48_2193) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let fvs = (FStar_All.pipe_left FStar_Absyn_Util.freevars_typ tres)
in (match ((FStar_All.pipe_right lbs (FStar_List.tryFind (fun _48_10 -> (match (_48_10) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_48_2205); FStar_Absyn_Syntax.lbtyp = _48_2203; FStar_Absyn_Syntax.lbeff = _48_2201; FStar_Absyn_Syntax.lbdef = _48_2199} -> begin
false
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = _48_2213; FStar_Absyn_Syntax.lbeff = _48_2211; FStar_Absyn_Syntax.lbdef = _48_2209} -> begin
(FStar_Util.set_mem (FStar_Absyn_Util.bvd_to_bvar_s x FStar_Absyn_Syntax.tun) fvs.FStar_Absyn_Syntax.fxvs)
end))))) with
| Some ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (y); FStar_Absyn_Syntax.lbtyp = _48_2222; FStar_Absyn_Syntax.lbeff = _48_2220; FStar_Absyn_Syntax.lbdef = _48_2218}) -> begin
(

let t' = (FStar_Tc_Util.new_tvar env0 FStar_Absyn_Syntax.ktype)
in (

let _48_2228 = (let _147_836 = (FStar_Tc_Rel.teq env tres t')
in (FStar_All.pipe_left (FStar_Tc_Rel.try_discharge_guard env) _147_836))
in ((e), (cres), (guard))))
end
| _48_2231 -> begin
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
and tc_eqn : FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ  ->  FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp)  ->  ((FStar_Absyn_Syntax.pat * FStar_Absyn_Syntax.exp Prims.option * FStar_Absyn_Syntax.exp) * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.lcomp * FStar_Tc_Rel.guard_t) = (fun scrutinee_x pat_t env _48_2238 -> (match (_48_2238) with
| (pattern, when_clause, branch) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _48_2246 = (FStar_Tc_Util.pat_as_exps allow_implicits env p0)
in (match (_48_2246) with
| (bindings, exps, p) -> begin
(

let pat_env = (FStar_List.fold_left FStar_Tc_Env.push_local_binding env bindings)
in (

let _48_2255 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _48_11 -> (match (_48_11) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _147_849 = (FStar_Absyn_Print.strBvd x)
in (let _147_848 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.print2 "Before tc ... pattern var %s  : %s\n" _147_849 _147_848)))
end
| _48_2254 -> begin
()
end))))
end else begin
()
end
in (

let _48_2260 = (FStar_Tc_Env.clear_expected_typ pat_env)
in (match (_48_2260) with
| (env1, _48_2259) -> begin
(

let env1 = (

let _48_2261 = env1
in {FStar_Tc_Env.solver = _48_2261.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_2261.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_2261.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_2261.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_2261.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_2261.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_2261.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_2261.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = true; FStar_Tc_Env.instantiate_targs = _48_2261.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_2261.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_2261.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_2261.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_2261.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_2261.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_2261.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_2261.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_2261.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_2261.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_2261.FStar_Tc_Env.default_effects})
in (

let expected_pat_t = (let _147_850 = (FStar_Tc_Rel.unrefine env pat_t)
in (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env _147_850))
in (

let exps = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _48_2266 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_853 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_852 = (FStar_Absyn_Print.typ_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _147_853 _147_852)))
end else begin
()
end
in (

let _48_2271 = (tc_exp env1 e)
in (match (_48_2271) with
| (e, lc, g) -> begin
(

let _48_2272 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_855 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (let _147_854 = (FStar_Tc_Normalize.typ_norm_to_string env lc.FStar_Absyn_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _147_855 _147_854)))
end else begin
()
end
in (

let g' = (FStar_Tc_Rel.teq env lc.FStar_Absyn_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_Tc_Rel.conj_guard g g')
in (

let _48_2276 = (let _147_856 = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_left Prims.ignore _147_856))
in (

let e' = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (

let _48_2279 = if (let _147_859 = (let _147_858 = (FStar_Absyn_Util.uvars_in_exp e')
in (let _147_857 = (FStar_Absyn_Util.uvars_in_typ expected_pat_t)
in (FStar_Absyn_Util.uvars_included_in _147_858 _147_857)))
in (FStar_All.pipe_left Prims.op_Negation _147_859)) then begin
(let _147_864 = (let _147_863 = (let _147_862 = (let _147_861 = (FStar_Absyn_Print.exp_to_string e')
in (let _147_860 = (FStar_Absyn_Print.typ_to_string expected_pat_t)
in (FStar_Util.format2 "Implicit pattern variables in %s could not be resolved against expected type %s; please bind them explicitly" _147_861 _147_860)))
in ((_147_862), (p.FStar_Absyn_Syntax.p)))
in FStar_Absyn_Syntax.Error (_147_863))
in (Prims.raise _147_864))
end else begin
()
end
in e))))))
end))))))
in (

let p = (FStar_Tc_Util.decorate_pattern env p exps)
in (

let _48_2290 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(FStar_All.pipe_right bindings (FStar_List.iter (fun _48_12 -> (match (_48_12) with
| FStar_Tc_Env.Binding_var (x, t) -> begin
(let _147_867 = (FStar_Absyn_Print.strBvd x)
in (let _147_866 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.print2 "Pattern var %s  : %s\n" _147_867 _147_866)))
end
| _48_2289 -> begin
()
end))))
end else begin
()
end
in ((p), (bindings), (pat_env), (exps), (FStar_Tc_Rel.trivial_guard)))))))
end))))
end)))
in (

let _48_2297 = (tc_pat true pat_t pattern)
in (match (_48_2297) with
| (pattern, bindings, pat_env, disj_exps, g_pat) -> begin
(

let _48_2307 = (match (when_clause) with
| None -> begin
((None), (FStar_Tc_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str) then begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("When clauses are not yet supported in --verify mode; they soon will be"), (e.FStar_Absyn_Syntax.pos)))))
end else begin
(

let _48_2304 = (let _147_868 = (FStar_Tc_Env.set_expected_typ pat_env FStar_Tc_Recheck.t_bool)
in (tc_exp _147_868 e))
in (match (_48_2304) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_48_2307) with
| (when_clause, g_when) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_870 = (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool w FStar_Absyn_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _147_869 -> Some (_147_869)) _147_870))
end)
in (

let _48_2315 = (tc_exp pat_env branch)
in (match (_48_2315) with
| (branch, c, g_branch) -> begin
(

let scrutinee = (FStar_Absyn_Util.bvd_to_exp scrutinee_x pat_t)
in (

let _48_2320 = (let _147_871 = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var (((scrutinee_x), (pat_t)))))
in (FStar_All.pipe_right _147_871 FStar_Tc_Env.clear_expected_typ))
in (match (_48_2320) with
| (scrutinee_env, _48_2319) -> begin
(

let c = (

let eqs = (FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Absyn_Util.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) -> begin
fopt
end
| _48_2334 -> begin
(

let clause = (let _147_875 = (FStar_Tc_Recheck.recompute_typ scrutinee)
in (let _147_874 = (FStar_Tc_Recheck.recompute_typ e)
in (FStar_Absyn_Util.mk_eq _147_875 _147_874 scrutinee e)))
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _147_877 = (FStar_Absyn_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _147_876 -> Some (_147_876)) _147_877))
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
(let _147_880 = (let _147_879 = (FStar_Absyn_Util.mk_conj f w)
in (FStar_All.pipe_left (fun _147_878 -> FStar_Tc_Rel.NonTrivial (_147_878)) _147_879))
in (FStar_Tc_Util.weaken_precondition env c _147_880))
end
| (None, Some (w)) -> begin
(FStar_Tc_Util.weaken_precondition env c (FStar_Tc_Rel.NonTrivial (w)))
end)
in (FStar_Tc_Util.close_comp env bindings c)))
in (

let discriminate = (fun scrutinee f -> (

let disc = (let _147_886 = (let _147_885 = (FStar_Absyn_Util.mk_discriminator f.FStar_Absyn_Syntax.v)
in (FStar_Absyn_Util.fvar None _147_885))
in (FStar_All.pipe_left _147_886 (FStar_Ident.range_of_lid f.FStar_Absyn_Syntax.v)))
in (

let disc = (let _147_889 = (let _147_888 = (let _147_887 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg scrutinee)
in (_147_887)::[])
in ((disc), (_147_888)))
in (FStar_Absyn_Syntax.mk_Exp_app _147_889 None scrutinee.FStar_Absyn_Syntax.pos))
in (FStar_Absyn_Util.mk_eq FStar_Absyn_Util.t_bool FStar_Absyn_Util.t_bool disc FStar_Absyn_Const.exp_true_bool))))
in (

let rec mk_guard = (fun scrutinee pat_exp -> (

let pat_exp = (FStar_Absyn_Util.compress_exp pat_exp)
in (match (pat_exp.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_uvar (_)) | (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) | (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_constant (FStar_Const.Const_unit)) -> begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| FStar_Absyn_Syntax.Exp_constant (_48_2392) -> begin
(let _147_898 = (let _147_897 = (let _147_896 = (FStar_Absyn_Syntax.varg scrutinee)
in (let _147_895 = (let _147_894 = (FStar_Absyn_Syntax.varg pat_exp)
in (_147_894)::[])
in (_147_896)::_147_895))
in ((FStar_Absyn_Util.teq), (_147_897)))
in (FStar_Absyn_Syntax.mk_Typ_app _147_898 None scrutinee.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_fvar (f, _48_2396) -> begin
(discriminate scrutinee f)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (f, _48_2409); FStar_Absyn_Syntax.tk = _48_2406; FStar_Absyn_Syntax.pos = _48_2404; FStar_Absyn_Syntax.fvs = _48_2402; FStar_Absyn_Syntax.uvs = _48_2400}, args) -> begin
(

let head = (discriminate scrutinee f)
in (

let sub_term_guards = (let _147_907 = (FStar_All.pipe_right args (FStar_List.mapi (fun i arg -> (match ((Prims.fst arg)) with
| FStar_Util.Inl (_48_2420) -> begin
[]
end
| FStar_Util.Inr (ei) -> begin
(

let projector = (FStar_Tc_Env.lookup_projector env f.FStar_Absyn_Syntax.v i)
in if (let _147_901 = (FStar_Tc_Env.is_projector env projector)
in (FStar_All.pipe_left Prims.op_Negation _147_901)) then begin
[]
end else begin
(

let sub_term = (let _147_905 = (let _147_904 = (FStar_Absyn_Util.fvar None projector f.FStar_Absyn_Syntax.p)
in (let _147_903 = (let _147_902 = (FStar_Absyn_Syntax.varg scrutinee)
in (_147_902)::[])
in ((_147_904), (_147_903))))
in (FStar_Absyn_Syntax.mk_Exp_app _147_905 None f.FStar_Absyn_Syntax.p))
in (let _147_906 = (mk_guard sub_term ei)
in (_147_906)::[]))
end)
end))))
in (FStar_All.pipe_right _147_907 FStar_List.flatten))
in (FStar_Absyn_Util.mk_conj_l ((head)::sub_term_guards))))
end
| _48_2428 -> begin
(let _147_910 = (let _147_909 = (FStar_Range.string_of_range pat_exp.FStar_Absyn_Syntax.pos)
in (let _147_908 = (FStar_Absyn_Print.exp_to_string pat_exp)
in (FStar_Util.format2 "tc_eqn: Impossible (%s) %s" _147_909 _147_908)))
in (failwith _147_910))
end)))
in (

let mk_guard = (fun s tsc pat -> if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
(FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end else begin
(

let t = (mk_guard s pat)
in (

let _48_2437 = (tc_typ_check scrutinee_env t FStar_Absyn_Syntax.mk_Kind_type)
in (match (_48_2437) with
| (t, _48_2436) -> begin
t
end)))
end)
in (

let path_guard = (let _147_919 = (FStar_All.pipe_right disj_exps (FStar_List.map (fun e -> (let _147_918 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env e)
in (mk_guard scrutinee pat_t _147_918)))))
in (FStar_All.pipe_right _147_919 FStar_Absyn_Util.mk_disj_l))
in (

let path_guard = (match (when_condition) with
| None -> begin
path_guard
end
| Some (w) -> begin
(FStar_Absyn_Util.mk_conj path_guard w)
end)
in (

let guard = (let _147_920 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _147_920))
in (

let _48_2445 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _147_921 = (FStar_Tc_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _147_921))
end else begin
()
end
in (let _147_923 = (let _147_922 = (FStar_Tc_Rel.conj_guard g_when g_branch)
in (FStar_Tc_Rel.conj_guard g_pat _147_922))
in ((((pattern), (when_clause), (branch))), (path_guard), (c), (_147_923)))))))))))
end)))
end)))
end))
end)))
end))
and tc_kind_trivial : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let _48_2451 = (tc_kind env k)
in (match (_48_2451) with
| (k, g) -> begin
(

let _48_2452 = (FStar_Tc_Util.discharge_guard env g)
in k)
end)))
and tc_typ_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.knd) = (fun env t -> (

let _48_2459 = (tc_typ env t)
in (match (_48_2459) with
| (t, k, g) -> begin
(

let _48_2460 = (FStar_Tc_Util.discharge_guard env g)
in ((t), (k)))
end)))
and tc_typ_check_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun env t k -> (

let _48_2467 = (tc_typ_check env t k)
in (match (_48_2467) with
| (t, f) -> begin
(

let _48_2468 = (FStar_Tc_Util.discharge_guard env f)
in t)
end)))
and tc_total_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (

let _48_2475 = (tc_exp env e)
in (match (_48_2475) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
((e), (c.FStar_Absyn_Syntax.res_typ), (g))
end else begin
(

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (

let c = (let _147_933 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _147_933 (norm_c env)))
in (match ((let _147_935 = (let _147_934 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.total_comp (FStar_Absyn_Util.comp_result c) _147_934))
in (FStar_Tc_Rel.sub_comp env c _147_935))) with
| Some (g') -> begin
(let _147_936 = (FStar_Tc_Rel.conj_guard g g')
in ((e), ((FStar_Absyn_Util.comp_result c)), (_147_936)))
end
| _48_2481 -> begin
(let _147_939 = (let _147_938 = (let _147_937 = (FStar_Tc_Errors.expected_pure_expression e c)
in ((_147_937), (e.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_938))
in (Prims.raise _147_939))
end)))
end
end)))
and tc_ghost_exp : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.typ * FStar_Tc_Rel.guard_t) = (fun env e -> (

let _48_2487 = (tc_exp env e)
in (match (_48_2487) with
| (e, c, g) -> begin
if (FStar_Absyn_Util.is_total_lcomp c) then begin
((e), (c.FStar_Absyn_Syntax.res_typ), (g))
end else begin
(

let c = (let _147_942 = (c.FStar_Absyn_Syntax.comp ())
in (FStar_All.pipe_right _147_942 (norm_c env)))
in (

let expected_c = (FStar_Absyn_Util.gtotal_comp (FStar_Absyn_Util.comp_result c))
in (

let g = (FStar_Tc_Rel.solve_deferred_constraints env g)
in (match ((FStar_Tc_Rel.sub_comp (

let _48_2491 = env
in {FStar_Tc_Env.solver = _48_2491.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_2491.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_2491.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_2491.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_2491.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_2491.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_2491.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_2491.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_2491.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_2491.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_2491.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_2491.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_2491.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_2491.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_2491.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_2491.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = false; FStar_Tc_Env.is_iface = _48_2491.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_2491.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_2491.FStar_Tc_Env.default_effects}) c expected_c)) with
| Some (g') -> begin
(let _147_943 = (FStar_Tc_Rel.conj_guard g g')
in ((e), ((FStar_Absyn_Util.comp_result c)), (_147_943)))
end
| _48_2496 -> begin
(let _147_946 = (let _147_945 = (let _147_944 = (FStar_Tc_Errors.expected_ghost_expression e c)
in ((_147_944), (e.FStar_Absyn_Syntax.pos)))
in FStar_Absyn_Syntax.Error (_147_945))
in (Prims.raise _147_946))
end))))
end
end)))


let tc_tparams : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.binders * FStar_Tc_Env.env) = (fun env tps -> (

let _48_2502 = (tc_binders env tps)
in (match (_48_2502) with
| (tps, env, g) -> begin
(

let _48_2503 = (FStar_Tc_Util.force_trivial env g)
in ((tps), (env)))
end)))


let a_kwp_a : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env m s -> (match (s.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (((FStar_Util.Inl (a), _48_2522))::((FStar_Util.Inl (wp), _48_2517))::((FStar_Util.Inl (_48_2509), _48_2512))::[], _48_2526) -> begin
((a), (wp.FStar_Absyn_Syntax.sort))
end
| _48_2530 -> begin
(let _147_959 = (let _147_958 = (let _147_957 = (FStar_Tc_Errors.unexpected_signature_for_monad env m s)
in ((_147_957), ((FStar_Ident.range_of_lid m))))
in FStar_Absyn_Syntax.Error (_147_958))
in (Prims.raise _147_959))
end))


let rec tc_eff_decl : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.eff_decl  ->  FStar_Absyn_Syntax.eff_decl = (fun env m -> (

let _48_2536 = (tc_binders env m.FStar_Absyn_Syntax.binders)
in (match (_48_2536) with
| (binders, env, g) -> begin
(

let _48_2537 = (FStar_Tc_Util.discharge_guard env g)
in (

let mk = (tc_kind_trivial env m.FStar_Absyn_Syntax.signature)
in (

let _48_2542 = (a_kwp_a env m.FStar_Absyn_Syntax.mname mk)
in (match (_48_2542) with
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

let a_kwp_b = (let _147_972 = (let _147_971 = (let _147_970 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_147_970)::[])
in ((_147_971), (kwp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_972 a_typ.FStar_Absyn_Syntax.pos))
in (

let a_kwlp_b = a_kwp_b
in (

let w = (fun k -> (k (FStar_Ident.range_of_lid m.FStar_Absyn_Syntax.mname)))
in (

let ret = (

let expected_k = (let _147_986 = (let _147_985 = (let _147_984 = (let _147_983 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_982 = (let _147_981 = (FStar_Absyn_Syntax.null_v_binder a_typ)
in (_147_981)::[])
in (_147_983)::_147_982))
in ((_147_984), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_985))
in (FStar_All.pipe_left w _147_986))
in (let _147_987 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ret expected_k)
in (FStar_All.pipe_right _147_987 (norm_t env))))
in (

let bind_wp = (

let expected_k = (let _147_1002 = (let _147_1001 = (let _147_1000 = (let _147_999 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_998 = (let _147_997 = (FStar_Absyn_Syntax.t_binder b)
in (let _147_996 = (let _147_995 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _147_994 = (let _147_993 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _147_992 = (let _147_991 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (let _147_990 = (let _147_989 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_147_989)::[])
in (_147_991)::_147_990))
in (_147_993)::_147_992))
in (_147_995)::_147_994))
in (_147_997)::_147_996))
in (_147_999)::_147_998))
in ((_147_1000), (kwp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1001))
in (FStar_All.pipe_left w _147_1002))
in (let _147_1003 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wp expected_k)
in (FStar_All.pipe_right _147_1003 (norm_t env))))
in (

let bind_wlp = (

let expected_k = (let _147_1014 = (let _147_1013 = (let _147_1012 = (let _147_1011 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1010 = (let _147_1009 = (FStar_Absyn_Syntax.t_binder b)
in (let _147_1008 = (let _147_1007 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _147_1006 = (let _147_1005 = (FStar_Absyn_Syntax.null_t_binder a_kwlp_b)
in (_147_1005)::[])
in (_147_1007)::_147_1006))
in (_147_1009)::_147_1008))
in (_147_1011)::_147_1010))
in ((_147_1012), (kwlp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1013))
in (FStar_All.pipe_left w _147_1014))
in (let _147_1015 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.bind_wlp expected_k)
in (FStar_All.pipe_right _147_1015 (norm_t env))))
in (

let if_then_else = (

let expected_k = (let _147_1026 = (let _147_1025 = (let _147_1024 = (let _147_1023 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1022 = (let _147_1021 = (FStar_Absyn_Syntax.t_binder b)
in (let _147_1020 = (let _147_1019 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _147_1018 = (let _147_1017 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_147_1017)::[])
in (_147_1019)::_147_1018))
in (_147_1021)::_147_1020))
in (_147_1023)::_147_1022))
in ((_147_1024), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1025))
in (FStar_All.pipe_left w _147_1026))
in (let _147_1027 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.if_then_else expected_k)
in (FStar_All.pipe_right _147_1027 (norm_t env))))
in (

let ite_wp = (

let expected_k = (let _147_1036 = (let _147_1035 = (let _147_1034 = (let _147_1033 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1032 = (let _147_1031 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (let _147_1030 = (let _147_1029 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_147_1029)::[])
in (_147_1031)::_147_1030))
in (_147_1033)::_147_1032))
in ((_147_1034), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1035))
in (FStar_All.pipe_left w _147_1036))
in (let _147_1037 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wp expected_k)
in (FStar_All.pipe_right _147_1037 (norm_t env))))
in (

let ite_wlp = (

let expected_k = (let _147_1044 = (let _147_1043 = (let _147_1042 = (let _147_1041 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1040 = (let _147_1039 = (FStar_Absyn_Syntax.null_t_binder kwlp_a)
in (_147_1039)::[])
in (_147_1041)::_147_1040))
in ((_147_1042), (kwlp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1043))
in (FStar_All.pipe_left w _147_1044))
in (let _147_1045 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.ite_wlp expected_k)
in (FStar_All.pipe_right _147_1045 (norm_t env))))
in (

let wp_binop = (

let expected_k = (let _147_1057 = (let _147_1056 = (let _147_1055 = (let _147_1054 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1053 = (let _147_1052 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (let _147_1051 = (let _147_1050 = (let _147_1047 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Syntax.null_t_binder _147_1047))
in (let _147_1049 = (let _147_1048 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_147_1048)::[])
in (_147_1050)::_147_1049))
in (_147_1052)::_147_1051))
in (_147_1054)::_147_1053))
in ((_147_1055), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1056))
in (FStar_All.pipe_left w _147_1057))
in (let _147_1058 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_binop expected_k)
in (FStar_All.pipe_right _147_1058 (norm_t env))))
in (

let wp_as_type = (

let expected_k = (let _147_1065 = (let _147_1064 = (let _147_1063 = (let _147_1062 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1061 = (let _147_1060 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_147_1060)::[])
in (_147_1062)::_147_1061))
in ((_147_1063), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1064))
in (FStar_All.pipe_left w _147_1065))
in (let _147_1066 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.wp_as_type expected_k)
in (FStar_All.pipe_right _147_1066 (norm_t env))))
in (

let close_wp = (

let expected_k = (let _147_1075 = (let _147_1074 = (let _147_1073 = (let _147_1072 = (FStar_Absyn_Syntax.t_binder b)
in (let _147_1071 = (let _147_1070 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1069 = (let _147_1068 = (FStar_Absyn_Syntax.null_t_binder a_kwp_b)
in (_147_1068)::[])
in (_147_1070)::_147_1069))
in (_147_1072)::_147_1071))
in ((_147_1073), (kwp_b)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1074))
in (FStar_All.pipe_left w _147_1075))
in (let _147_1076 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp expected_k)
in (FStar_All.pipe_right _147_1076 (norm_t env))))
in (

let close_wp_t = (

let expected_k = (let _147_1089 = (let _147_1088 = (let _147_1087 = (let _147_1086 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1085 = (let _147_1084 = (let _147_1083 = (let _147_1082 = (let _147_1081 = (let _147_1080 = (let _147_1079 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (_147_1079)::[])
in ((_147_1080), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1081))
in (FStar_All.pipe_left w _147_1082))
in (FStar_Absyn_Syntax.null_t_binder _147_1083))
in (_147_1084)::[])
in (_147_1086)::_147_1085))
in ((_147_1087), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1088))
in (FStar_All.pipe_left w _147_1089))
in (let _147_1090 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.close_wp_t expected_k)
in (FStar_All.pipe_right _147_1090 (norm_t env))))
in (

let _48_2576 = (

let expected_k = (let _147_1099 = (let _147_1098 = (let _147_1097 = (let _147_1096 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1095 = (let _147_1094 = (FStar_Absyn_Syntax.null_t_binder FStar_Absyn_Syntax.ktype)
in (let _147_1093 = (let _147_1092 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_147_1092)::[])
in (_147_1094)::_147_1093))
in (_147_1096)::_147_1095))
in ((_147_1097), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1098))
in (FStar_All.pipe_left w _147_1099))
in (let _147_1103 = (let _147_1100 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assert_p expected_k)
in (FStar_All.pipe_right _147_1100 (norm_t env)))
in (let _147_1102 = (let _147_1101 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.assume_p expected_k)
in (FStar_All.pipe_right _147_1101 (norm_t env)))
in ((_147_1103), (_147_1102)))))
in (match (_48_2576) with
| (assert_p, assume_p) -> begin
(

let null_wp = (

let expected_k = (let _147_1108 = (let _147_1107 = (let _147_1106 = (let _147_1105 = (FStar_Absyn_Syntax.t_binder a)
in (_147_1105)::[])
in ((_147_1106), (kwp_a)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1107))
in (FStar_All.pipe_left w _147_1108))
in (let _147_1109 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.null_wp expected_k)
in (FStar_All.pipe_right _147_1109 (norm_t env))))
in (

let trivial_wp = (

let expected_k = (let _147_1116 = (let _147_1115 = (let _147_1114 = (let _147_1113 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1112 = (let _147_1111 = (FStar_Absyn_Syntax.null_t_binder kwp_a)
in (_147_1111)::[])
in (_147_1113)::_147_1112))
in ((_147_1114), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1115))
in (FStar_All.pipe_left w _147_1116))
in (let _147_1117 = (tc_typ_check_trivial env m.FStar_Absyn_Syntax.trivial expected_k)
in (FStar_All.pipe_right _147_1117 (norm_t env))))
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
(Prims.raise (FStar_Absyn_Syntax.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Absyn_Syntax.SetOptions (o) -> begin
(

let _48_2597 = (set_options FStar_Options.Set o)
in ((se), (env)))
end
| FStar_Absyn_Syntax.ResetOptions (sopt) -> begin
(

let _48_2601 = (let _147_1125 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _147_1125 Prims.ignore))
in (

let _48_2606 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _48_2608 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
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

let _48_2623 = (let _147_1126 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.source)
in (a_kwp_a env sub.FStar_Absyn_Syntax.source _147_1126))
in (match (_48_2623) with
| (a, kwp_a_src) -> begin
(

let _48_2626 = (let _147_1127 = (FStar_Tc_Env.lookup_effect_lid env sub.FStar_Absyn_Syntax.target)
in (a_kwp_a env sub.FStar_Absyn_Syntax.target _147_1127))
in (match (_48_2626) with
| (b, kwp_b_tgt) -> begin
(

let kwp_a_tgt = (let _147_1131 = (let _147_1130 = (let _147_1129 = (let _147_1128 = (FStar_Absyn_Util.btvar_to_typ a)
in ((b.FStar_Absyn_Syntax.v), (_147_1128)))
in FStar_Util.Inl (_147_1129))
in (_147_1130)::[])
in (FStar_Absyn_Util.subst_kind _147_1131 kwp_b_tgt))
in (

let expected_k = (let _147_1137 = (let _147_1136 = (let _147_1135 = (let _147_1134 = (FStar_Absyn_Syntax.t_binder a)
in (let _147_1133 = (let _147_1132 = (FStar_Absyn_Syntax.null_t_binder kwp_a_src)
in (_147_1132)::[])
in (_147_1134)::_147_1133))
in ((_147_1135), (kwp_a_tgt)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _147_1136))
in (FStar_All.pipe_right r _147_1137))
in (

let lift = (tc_typ_check_trivial env sub.FStar_Absyn_Syntax.lift expected_k)
in (

let sub = (

let _48_2630 = sub
in {FStar_Absyn_Syntax.source = _48_2630.FStar_Absyn_Syntax.source; FStar_Absyn_Syntax.target = _48_2630.FStar_Absyn_Syntax.target; FStar_Absyn_Syntax.lift = lift})
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

let _48_2647 = (tc_tparams env tps)
in (match (_48_2647) with
| (tps, env) -> begin
(

let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
FStar_Absyn_Syntax.ktype
end
| _48_2650 -> begin
(tc_kind_trivial env k)
end)
in (

let _48_2652 = if (FStar_Tc_Env.debug env FStar_Options.Extreme) then begin
(let _147_1140 = (FStar_Absyn_Print.sli lid)
in (let _147_1139 = (let _147_1138 = (FStar_Absyn_Util.close_kind tps k)
in (FStar_Absyn_Print.kind_to_string _147_1138))
in (FStar_Util.print2 "Checked %s at kind %s\n" _147_1140 _147_1139)))
end else begin
()
end
in (

let k = (norm_k env k)
in (

let se = FStar_Absyn_Syntax.Sig_tycon (((lid), (tps), (k), (_mutuals), (_data), (tags), (r)))
in (

let _48_2670 = (match ((FStar_Absyn_Util.compress_kind k)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_uvar (_48_2665); FStar_Absyn_Syntax.tk = _48_2663; FStar_Absyn_Syntax.pos = _48_2661; FStar_Absyn_Syntax.fvs = _48_2659; FStar_Absyn_Syntax.uvs = _48_2657} -> begin
(let _147_1141 = (FStar_Tc_Rel.keq env None k FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env) _147_1141))
end
| _48_2669 -> begin
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

let _48_2683 = (tc_tparams env tps)
in (match (_48_2683) with
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

let _48_2698 = (tc_tparams env tps)
in (match (_48_2698) with
| (tps, env) -> begin
(

let _48_2701 = (tc_comp env c)
in (match (_48_2701) with
| (c, g) -> begin
(

let tags = (FStar_All.pipe_right tags (FStar_List.map (fun _48_13 -> (match (_48_13) with
| FStar_Absyn_Syntax.DefaultEffect (None) -> begin
(

let c' = (FStar_Tc_Normalize.weak_norm_comp env c)
in (let _147_1144 = (FStar_All.pipe_right c'.FStar_Absyn_Syntax.effect_name (fun _147_1143 -> Some (_147_1143)))
in FStar_Absyn_Syntax.DefaultEffect (_147_1144)))
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

let _48_2721 = (tc_tparams env tps)
in (match (_48_2721) with
| (tps, env') -> begin
(

let _48_2727 = (let _147_1148 = (tc_typ_trivial env' t)
in (FStar_All.pipe_right _147_1148 (fun _48_2724 -> (match (_48_2724) with
| (t, k) -> begin
(let _147_1147 = (norm_t env' t)
in (let _147_1146 = (norm_k env' k)
in ((_147_1147), (_147_1146))))
end))))
in (match (_48_2727) with
| (t, k1) -> begin
(

let k2 = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
k1
end
| _48_2730 -> begin
(

let k2 = (let _147_1149 = (tc_kind_trivial env' k)
in (FStar_All.pipe_right _147_1149 (norm_k env)))
in (

let _48_2732 = (let _147_1150 = (FStar_Tc_Rel.keq env' (Some (t)) k1 k2)
in (FStar_All.pipe_left (FStar_Tc_Util.force_trivial env') _147_1150))
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

let _48_2752 = (tc_binders env tps)
in (match (_48_2752) with
| (tps, env, g) -> begin
(

let tycon = ((tname), (tps), (k))
in (

let _48_2754 = (FStar_Tc_Util.discharge_guard env g)
in (

let t = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (

let t = (norm_t env t)
in (

let _48_2766 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
((formals), ((FStar_Absyn_Util.comp_result cod)))
end
| _48_2763 -> begin
(([]), (t))
end)
in (match (_48_2766) with
| (formals, result_t) -> begin
(

let cardinality_and_positivity_check = (fun formal -> (

let check_positivity = (fun formals -> (FStar_All.pipe_right formals (FStar_List.iter (fun _48_2774 -> (match (_48_2774) with
| (a, _48_2773) -> begin
(match (a) with
| FStar_Util.Inl (_48_2776) -> begin
()
end
| FStar_Util.Inr (y) -> begin
(

let t = y.FStar_Absyn_Syntax.sort
in (FStar_Absyn_Visit.collect_from_typ (fun b t -> (match ((let _147_1158 = (FStar_Absyn_Util.compress_typ t)
in _147_1158.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (f) -> begin
(match ((FStar_List.tryFind (FStar_Ident.lid_equals f.FStar_Absyn_Syntax.v) mutuals)) with
| None -> begin
()
end
| Some (tname) -> begin
(let _147_1162 = (let _147_1161 = (let _147_1160 = (let _147_1159 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_fails_the_positivity_check env _147_1159 tname))
in ((_147_1160), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_147_1161))
in (Prims.raise _147_1162))
end)
end
| _48_2789 -> begin
()
end)) () t))
end)
end)))))
in (match ((Prims.fst formal)) with
| FStar_Util.Inl (a) -> begin
(

let _48_2792 = if (FStar_Options.warn_cardinality ()) then begin
(let _147_1163 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in (FStar_Tc_Errors.warn r _147_1163))
end else begin
if (FStar_Options.check_cardinality ()) then begin
(let _147_1166 = (let _147_1165 = (let _147_1164 = (FStar_Tc_Errors.cardinality_constraint_violated lid a)
in ((_147_1164), (r)))
in FStar_Absyn_Syntax.Error (_147_1165))
in (Prims.raise _147_1166))
end else begin
()
end
end
in (

let k = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env a.FStar_Absyn_Syntax.sort)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (_48_2796) -> begin
(

let _48_2801 = (FStar_Absyn_Util.kind_formals k)
in (match (_48_2801) with
| (formals, _48_2800) -> begin
(check_positivity formals)
end))
end
| _48_2803 -> begin
()
end)))
end
| FStar_Util.Inr (x) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.DeltaHard)::[]) env x.FStar_Absyn_Syntax.sort)
in if ((FStar_Absyn_Util.is_function_typ t) && (FStar_Absyn_Util.is_pure_or_ghost_function t)) then begin
(

let _48_2810 = (let _147_1167 = (FStar_Absyn_Util.function_formals t)
in (FStar_All.pipe_right _147_1167 FStar_Util.must))
in (match (_48_2810) with
| (formals, _48_2809) -> begin
(check_positivity formals)
end))
end else begin
()
end)
end)))
in (

let _48_2811 = (FStar_All.pipe_right formals (FStar_List.iter cardinality_and_positivity_check))
in (

let _48_2865 = (match ((FStar_Absyn_Util.destruct result_t tname)) with
| Some (args) -> begin
if (not ((((FStar_List.length args) >= (FStar_List.length tps)) && (let _147_1171 = (let _147_1170 = (FStar_Util.first_N (FStar_List.length tps) args)
in (FStar_All.pipe_right _147_1170 Prims.fst))
in (FStar_List.forall2 (fun _48_2818 _48_2822 -> (match (((_48_2818), (_48_2822))) with
| ((a, _48_2817), (b, _48_2821)) -> begin
(match (((a), (b))) with
| (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (aa); FStar_Absyn_Syntax.tk = _48_2830; FStar_Absyn_Syntax.pos = _48_2828; FStar_Absyn_Syntax.fvs = _48_2826; FStar_Absyn_Syntax.uvs = _48_2824}), FStar_Util.Inl (bb)) -> begin
(FStar_Absyn_Util.bvar_eq aa bb)
end
| (FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (xx); FStar_Absyn_Syntax.tk = _48_2845; FStar_Absyn_Syntax.pos = _48_2843; FStar_Absyn_Syntax.fvs = _48_2841; FStar_Absyn_Syntax.uvs = _48_2839}), FStar_Util.Inr (yy)) -> begin
(FStar_Absyn_Util.bvar_eq xx yy)
end
| _48_2854 -> begin
false
end)
end)) _147_1171 tps))))) then begin
(

let expected_t = (match (tps) with
| [] -> begin
(FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
end
| _48_2857 -> begin
(

let _48_2861 = (FStar_Absyn_Util.args_of_binders tps)
in (match (_48_2861) with
| (_48_2859, expected_args) -> begin
(let _147_1172 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _147_1172 expected_args))
end))
end)
in (let _147_1176 = (let _147_1175 = (let _147_1174 = (let _147_1173 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _147_1173 result_t expected_t))
in ((_147_1174), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_147_1175))
in (Prims.raise _147_1176)))
end else begin
()
end
end
| _48_2864 -> begin
(let _147_1181 = (let _147_1180 = (let _147_1179 = (let _147_1178 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) lid (FStar_Ident.range_of_lid lid))
in (let _147_1177 = (FStar_Absyn_Util.ftv tname FStar_Absyn_Syntax.kun)
in (FStar_Tc_Errors.constructor_builds_the_wrong_type env _147_1178 result_t _147_1177)))
in ((_147_1179), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_147_1180))
in (Prims.raise _147_1181))
end)
in (

let se = FStar_Absyn_Syntax.Sig_datacon (((lid), (t), (tycon), (quals), (mutuals), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in (

let _48_2869 = if (log env) then begin
(let _147_1183 = (let _147_1182 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "data %s : %s\n" lid.FStar_Ident.str _147_1182))
in (FStar_All.pipe_left FStar_Util.print_string _147_1183))
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

let t = (let _147_1184 = (tc_typ_check_trivial env t FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _147_1184 (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.SNComp)::[]) env)))
in (

let _48_2879 = (FStar_Tc_Util.check_uvars r t)
in (

let se = FStar_Absyn_Syntax.Sig_val_decl (((lid), (t), (quals), (r)))
in (

let env = (FStar_Tc_Env.push_sigelt env se)
in (

let _48_2883 = if (log env) then begin
(let _147_1186 = (let _147_1185 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "val %s : %s\n" lid.FStar_Ident.str _147_1185))
in (FStar_All.pipe_left FStar_Util.print_string _147_1186))
end else begin
()
end
in ((se), (env))))))))
end
| FStar_Absyn_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let env = (FStar_Tc_Env.set_range env r)
in (

let phi = (let _147_1187 = (tc_typ_check_trivial env phi FStar_Absyn_Syntax.ktype)
in (FStar_All.pipe_right _147_1187 (norm_t env)))
in (

let _48_2893 = (FStar_Tc_Util.check_uvars r phi)
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

let _48_2946 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _48_2906 lb -> (match (_48_2906) with
| (gen, lbs) -> begin
(

let _48_2943 = (match (lb) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_48_2915); FStar_Absyn_Syntax.lbtyp = _48_2913; FStar_Absyn_Syntax.lbeff = _48_2911; FStar_Absyn_Syntax.lbdef = _48_2909} -> begin
(failwith "impossible")
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _48_2920; FStar_Absyn_Syntax.lbdef = e} -> begin
(

let _48_2940 = (match ((FStar_Tc_Env.try_lookup_val_decl env l)) with
| None -> begin
((gen), (lb))
end
| Some (t', _48_2928) -> begin
(

let _48_2931 = if (FStar_Tc_Env.debug env FStar_Options.Medium) then begin
(let _147_1190 = (FStar_Absyn_Print.typ_to_string t')
in (FStar_Util.print2 "Using annotation %s for let binding %s\n" _147_1190 l.FStar_Ident.str))
end else begin
()
end
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_unknown -> begin
(let _147_1191 = (FStar_Absyn_Syntax.mk_lb ((FStar_Util.Inr (l)), (FStar_Absyn_Const.effect_ALL_lid), (t'), (e)))
in ((false), (_147_1191)))
end
| _48_2935 -> begin
(

let _48_2936 = if (not (deserialized)) then begin
(let _147_1193 = (let _147_1192 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "%s: Warning: Annotation from val declaration overrides inline type annotation\n" _147_1192))
in (FStar_All.pipe_left FStar_Util.print_string _147_1193))
end else begin
()
end
in (let _147_1194 = (FStar_Absyn_Syntax.mk_lb ((FStar_Util.Inr (l)), (FStar_Absyn_Const.effect_ALL_lid), (t'), (e)))
in ((false), (_147_1194))))
end))
end)
in (match (_48_2940) with
| (gen, lb) -> begin
((gen), (lb))
end))
end)
in (match (_48_2943) with
| (gen, lb) -> begin
((gen), ((lb)::lbs))
end))
end)) ((true), ([]))))
in (match (_48_2946) with
| (generalize, lbs') -> begin
(

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _147_1199 = (let _147_1198 = (let _147_1197 = (syn' env FStar_Tc_Recheck.t_unit)
in (FStar_All.pipe_left _147_1197 (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit)))
in (((((Prims.fst lbs)), (lbs'))), (_147_1198)))
in (FStar_Absyn_Syntax.mk_Exp_let _147_1199 None r))
in (

let _48_2981 = (match ((tc_exp (

let _48_2949 = env
in {FStar_Tc_Env.solver = _48_2949.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_2949.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_2949.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_2949.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_2949.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_2949.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_2949.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_2949.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_2949.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_2949.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_2949.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_2949.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = generalize; FStar_Tc_Env.letrecs = _48_2949.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_2949.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_2949.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_2949.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = _48_2949.FStar_Tc_Env.is_iface; FStar_Tc_Env.admit = _48_2949.FStar_Tc_Env.admit; FStar_Tc_Env.default_effects = _48_2949.FStar_Tc_Env.default_effects}) e)) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_let (lbs, e); FStar_Absyn_Syntax.tk = _48_2958; FStar_Absyn_Syntax.pos = _48_2956; FStar_Absyn_Syntax.fvs = _48_2954; FStar_Absyn_Syntax.uvs = _48_2952}, _48_2965, g) when (FStar_Tc_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (_48_2969, FStar_Absyn_Syntax.Masked_effect)) -> begin
(FStar_Absyn_Syntax.HasMaskedEffect)::quals
end
| _48_2975 -> begin
quals
end)
in ((FStar_Absyn_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _48_2978 -> begin
(failwith "impossible")
end)
in (match (_48_2981) with
| (se, lbs) -> begin
(

let _48_2987 = if (log env) then begin
(let _147_1205 = (let _147_1204 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _147_1201 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (FStar_Tc_Env.try_lookup_val_decl env _147_1201))) with
| None -> begin
true
end
| _48_2985 -> begin
false
end)
in if should_log then begin
(let _147_1203 = (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname)
in (let _147_1202 = (FStar_Tc_Normalize.typ_norm_to_string env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _147_1203 _147_1202)))
end else begin
""
end))))
in (FStar_All.pipe_right _147_1204 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _147_1205))
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

let _48_2999 = (tc_exp env e)
in (match (_48_2999) with
| (e, c, g1) -> begin
(

let g1 = (FStar_Tc_Rel.solve_deferred_constraints env g1)
in (

let _48_3005 = (let _147_1209 = (let _147_1206 = (FStar_Absyn_Util.ml_comp FStar_Tc_Recheck.t_unit r)
in Some (_147_1206))
in (let _147_1208 = (let _147_1207 = (c.FStar_Absyn_Syntax.comp ())
in ((e), (_147_1207)))
in (check_expected_effect env _147_1209 _147_1208)))
in (match (_48_3005) with
| (e, _48_3003, g) -> begin
(

let _48_3006 = (let _147_1210 = (FStar_Tc_Rel.conj_guard g1 g)
in (FStar_Tc_Util.discharge_guard env _147_1210))
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

let _48_3025 = (FStar_All.pipe_right ses (FStar_List.partition (fun _48_14 -> (match (_48_14) with
| FStar_Absyn_Syntax.Sig_tycon (_48_3019) -> begin
true
end
| _48_3022 -> begin
false
end))))
in (match (_48_3025) with
| (tycons, rest) -> begin
(

let _48_3034 = (FStar_All.pipe_right rest (FStar_List.partition (fun _48_15 -> (match (_48_15) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_48_3028) -> begin
true
end
| _48_3031 -> begin
false
end))))
in (match (_48_3034) with
| (abbrevs, rest) -> begin
(

let recs = (FStar_All.pipe_right abbrevs (FStar_List.map (fun _48_16 -> (match (_48_16) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, t, [], r) -> begin
(

let k = (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_unknown -> begin
(let _147_1214 = (FStar_Tc_Rel.new_kvar r tps)
in (FStar_All.pipe_right _147_1214 Prims.fst))
end
| _48_3046 -> begin
k
end)
in ((FStar_Absyn_Syntax.Sig_tycon (((lid), (tps), (k), ([]), ([]), ([]), (r)))), (t)))
end
| _48_3049 -> begin
(failwith "impossible")
end))))
in (

let _48_3053 = (FStar_List.split recs)
in (match (_48_3053) with
| (recs, abbrev_defs) -> begin
(

let msg = if (FStar_Options.log_queries ()) then begin
(let _147_1215 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.format1 "Recursive bindings: %s" _147_1215))
end else begin
""
end
in (

let _48_3055 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
in (

let _48_3060 = (tc_decls env tycons deserialized)
in (match (_48_3060) with
| (tycons, _48_3059) -> begin
(

let _48_3064 = (tc_decls env recs deserialized)
in (match (_48_3064) with
| (recs, _48_3063) -> begin
(

let env1 = (FStar_Tc_Env.push_sigelt env (FStar_Absyn_Syntax.Sig_bundle ((((FStar_List.append tycons recs)), (quals), (lids), (r)))))
in (

let _48_3069 = (tc_decls env1 rest deserialized)
in (match (_48_3069) with
| (rest, _48_3068) -> begin
(

let abbrevs = (FStar_List.map2 (fun se t -> (match (se) with
| FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, [], [], [], r) -> begin
(

let tt = (let _147_1218 = (FStar_Absyn_Syntax.mk_Typ_ascribed ((t), (k)) t.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Util.close_with_lam tps _147_1218))
in (

let _48_3085 = (tc_typ_trivial env1 tt)
in (match (_48_3085) with
| (tt, _48_3084) -> begin
(

let _48_3094 = (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
((bs), (t))
end
| _48_3091 -> begin
(([]), (tt))
end)
in (match (_48_3094) with
| (tps, t) -> begin
(let _147_1220 = (let _147_1219 = (FStar_Absyn_Util.compress_kind k)
in ((lid), (tps), (_147_1219), (t), ([]), (r)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_147_1220))
end))
end)))
end
| _48_3096 -> begin
(let _147_1222 = (let _147_1221 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 "(%s) Impossible" _147_1221))
in (failwith _147_1222))
end)) recs abbrev_defs)
in (

let _48_3098 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop msg)
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

let _48_3115 = (FStar_Util.time_diff start stop)
in (match (_48_3115) with
| (diff, _48_3114) -> begin
(

let _48_3116 = (let _147_1232 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (FStar_Util.print2 "Time %ss : %s\n" (FStar_Util.string_of_float diff) _147_1232))
in res)
end))))))
in (

let _48_3131 = (FStar_All.pipe_right ses (FStar_List.fold_left (fun _48_3120 se -> (match (_48_3120) with
| (ses, env) -> begin
(

let _48_3122 = if (FStar_Tc_Env.debug env FStar_Options.Low) then begin
(let _147_1236 = (let _147_1235 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_Util.format1 "Checking sigelt\t%s\n" _147_1235))
in (FStar_Util.print_string _147_1236))
end else begin
()
end
in (

let _48_3126 = if (FStar_Options.timing ()) then begin
(time_tc_decl env se deserialized)
end else begin
(tc_decl env se deserialized)
end
in (match (_48_3126) with
| (se, env) -> begin
(

let _48_3127 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env se)
in (((se)::ses), (env)))
end)))
end)) (([]), (env))))
in (match (_48_3131) with
| (ses, env) -> begin
(((FStar_List.rev ses)), (env))
end))))


let rec for_export : FStar_Tc_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_Absyn_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _48_17 -> (match (_48_17) with
| FStar_Absyn_Syntax.Abstract -> begin
true
end
| _48_3140 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Absyn_Syntax.Projector (l, _)) | (FStar_Absyn_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _48_3150 -> begin
false
end))
in (match (se) with
| FStar_Absyn_Syntax.Sig_pragma (_48_3152) -> begin
(([]), (hidden))
end
| FStar_Absyn_Syntax.Sig_datacon (_48_3155) -> begin
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
| FStar_Absyn_Syntax.Sig_bundle (ses, quals, _48_3175, _48_3177) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _48_3183 -> (match (_48_3183) with
| (out, hidden) -> begin
(match (se) with
| FStar_Absyn_Syntax.Sig_tycon (l, bs, t, _48_3188, _48_3190, quals, r) -> begin
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
| FStar_Absyn_Syntax.Sig_assume (_48_3208, _48_3210, quals, _48_3213) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _48_18 -> (match (_48_18) with
| (FStar_Absyn_Syntax.Assumption) | (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _48_3231 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Absyn_Syntax.Sig_main (_48_3233) -> begin
(([]), (hidden))
end
| (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Absyn_Syntax.Sig_let ((false, (lb)::[]), _48_3249, _48_3251, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _147_1254 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _147_1253 = (let _147_1252 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in ((_147_1252), (lb.FStar_Absyn_Syntax.lbtyp), ((FStar_Absyn_Syntax.Assumption)::quals), (r)))
in FStar_Absyn_Syntax.Sig_val_decl (_147_1253)))))
in ((_147_1254), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let get_exports : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env modul -> (

let _48_3276 = (FStar_All.pipe_right modul.FStar_Absyn_Syntax.declarations (FStar_List.fold_left (fun _48_3268 se -> (match (_48_3268) with
| (exports, hidden) -> begin
(

let _48_3272 = (for_export env hidden se)
in (match (_48_3272) with
| (exports', hidden) -> begin
(((exports')::exports), (hidden))
end))
end)) (([]), ([]))))
in (match (_48_3276) with
| (exports, _48_3275) -> begin
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

let _48_3281 = env
in (let _147_1265 = (not ((FStar_Options.should_verify modul.FStar_Absyn_Syntax.name.FStar_Ident.str)))
in {FStar_Tc_Env.solver = _48_3281.FStar_Tc_Env.solver; FStar_Tc_Env.range = _48_3281.FStar_Tc_Env.range; FStar_Tc_Env.curmodule = _48_3281.FStar_Tc_Env.curmodule; FStar_Tc_Env.gamma = _48_3281.FStar_Tc_Env.gamma; FStar_Tc_Env.modules = _48_3281.FStar_Tc_Env.modules; FStar_Tc_Env.expected_typ = _48_3281.FStar_Tc_Env.expected_typ; FStar_Tc_Env.level = _48_3281.FStar_Tc_Env.level; FStar_Tc_Env.sigtab = _48_3281.FStar_Tc_Env.sigtab; FStar_Tc_Env.is_pattern = _48_3281.FStar_Tc_Env.is_pattern; FStar_Tc_Env.instantiate_targs = _48_3281.FStar_Tc_Env.instantiate_targs; FStar_Tc_Env.instantiate_vargs = _48_3281.FStar_Tc_Env.instantiate_vargs; FStar_Tc_Env.effects = _48_3281.FStar_Tc_Env.effects; FStar_Tc_Env.generalize = _48_3281.FStar_Tc_Env.generalize; FStar_Tc_Env.letrecs = _48_3281.FStar_Tc_Env.letrecs; FStar_Tc_Env.top_level = _48_3281.FStar_Tc_Env.top_level; FStar_Tc_Env.check_uvars = _48_3281.FStar_Tc_Env.check_uvars; FStar_Tc_Env.use_eq = _48_3281.FStar_Tc_Env.use_eq; FStar_Tc_Env.is_iface = modul.FStar_Absyn_Syntax.is_interface; FStar_Tc_Env.admit = _147_1265; FStar_Tc_Env.default_effects = _48_3281.FStar_Tc_Env.default_effects}))
in (

let _48_3284 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.push msg)
end else begin
()
end
in (

let env = (FStar_Tc_Env.set_current_module env modul.FStar_Absyn_Syntax.name)
in (

let _48_3289 = (tc_decls env modul.FStar_Absyn_Syntax.declarations modul.FStar_Absyn_Syntax.is_deserialized)
in (match (_48_3289) with
| (ses, env) -> begin
(((

let _48_3290 = modul
in {FStar_Absyn_Syntax.name = _48_3290.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = ses; FStar_Absyn_Syntax.exports = _48_3290.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _48_3290.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _48_3290.FStar_Absyn_Syntax.is_deserialized})), (env))
end))))))))


let tc_more_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul decls -> (

let _48_3297 = (tc_decls env decls false)
in (match (_48_3297) with
| (ses, env) -> begin
(

let modul = (

let _48_3298 = modul
in {FStar_Absyn_Syntax.name = _48_3298.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = (FStar_List.append modul.FStar_Absyn_Syntax.declarations ses); FStar_Absyn_Syntax.exports = _48_3298.FStar_Absyn_Syntax.exports; FStar_Absyn_Syntax.is_interface = _48_3298.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = _48_3298.FStar_Absyn_Syntax.is_deserialized})
in ((modul), (env)))
end)))


let finish_partial_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (

let exports = (get_exports env modul)
in (

let modul = (

let _48_3304 = modul
in {FStar_Absyn_Syntax.name = _48_3304.FStar_Absyn_Syntax.name; FStar_Absyn_Syntax.declarations = _48_3304.FStar_Absyn_Syntax.declarations; FStar_Absyn_Syntax.exports = exports; FStar_Absyn_Syntax.is_interface = modul.FStar_Absyn_Syntax.is_interface; FStar_Absyn_Syntax.is_deserialized = modul.FStar_Absyn_Syntax.is_deserialized})
in (

let env = (FStar_Tc_Env.finish_module env modul)
in (

let _48_3314 = if (not ((FStar_Ident.lid_equals modul.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid))) then begin
(

let _48_3308 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.pop (Prims.strcat "Ending modul " modul.FStar_Absyn_Syntax.name.FStar_Ident.str))
in (

let _48_3310 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_modul env modul)
in (

let _48_3312 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _147_1276 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _147_1276 Prims.ignore)))))
end else begin
()
end
in ((modul), (env)))))))


let tc_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul * FStar_Tc_Env.env) = (fun env modul -> (

let _48_3320 = (tc_partial_modul env modul)
in (match (_48_3320) with
| (modul, env) -> begin
(finish_partial_modul env modul)
end)))


let add_modul_to_tcenv : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  FStar_Tc_Env.env = (fun en m -> (

let do_sigelt = (fun en elt -> (

let env = (FStar_Tc_Env.push_sigelt en elt)
in (

let _48_3327 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.encode_sig env elt)
in env)))
in (

let en = (FStar_Tc_Env.set_current_module en m.FStar_Absyn_Syntax.name)
in (let _147_1289 = (FStar_List.fold_left do_sigelt en m.FStar_Absyn_Syntax.exports)
in (FStar_Tc_Env.finish_module _147_1289 m)))))


let check_module : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Tc_Env.env) = (fun env m -> (

let _48_3332 = if (FStar_Options.debug_any ()) then begin
(let _147_1294 = (FStar_Absyn_Print.sli m.FStar_Absyn_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _147_1294))
end else begin
()
end
in (

let _48_3336 = (tc_modul env m)
in (match (_48_3336) with
| (m, env) -> begin
(

let _48_3337 = if (FStar_Options.dump_module m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _147_1295 = (FStar_Absyn_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _147_1295))
end else begin
()
end
in (((m)::[]), (env)))
end))))




