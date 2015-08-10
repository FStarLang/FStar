
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun ( env ) ( t1 ) ( t2 ) ( x ) -> (let _104_10 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _104_9 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (Support.Microsoft.FStar.Util.format2 "Subtyping check failed; expected type %s; got type %s" _104_10 _104_9))))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun ( r ) ( msg ) -> (let _104_16 = (let _104_15 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Diagnostic): %s\n" _104_15 msg))
in (Support.Microsoft.FStar.Util.print_string _104_16)))

let warn = (fun ( r ) ( msg ) -> (let _104_22 = (let _104_21 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Warning): %s\n" _104_21 msg))
in (Support.Microsoft.FStar.Util.print_string _104_22)))

let num_errs = (Support.Microsoft.FStar.Util.mk_ref 0)

let verification_errs = (Support.Microsoft.FStar.Util.mk_ref [])

let add_errors = (fun ( env ) ( errs ) -> (let errs = (Support.All.pipe_right errs (Support.List.map (fun ( _33_14 ) -> (match (_33_14) with
| (msg, r) -> begin
(let r = (match ((r = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
(Microsoft_FStar_Tc_Env.get_range env)
end
| false -> begin
r
end)
in (r, msg))
end))))
in (let n_errs = (Support.List.length errs)
in (Support.Microsoft.FStar.Util.atomically (fun ( _33_18 ) -> (match (()) with
| () -> begin
(let _33_19 = (let _104_30 = (let _104_29 = (Support.ST.read verification_errs)
in (Support.List.append errs _104_29))
in (Support.ST.op_Colon_Equals verification_errs _104_30))
in (let _104_31 = ((Support.ST.read num_errs) + n_errs)
in (Support.ST.op_Colon_Equals num_errs _104_31)))
end))))))

let report_all = (fun ( _33_21 ) -> (match (()) with
| () -> begin
(let all_errs = (Support.Microsoft.FStar.Util.atomically (fun ( _33_22 ) -> (match (()) with
| () -> begin
(let x = (Support.ST.read verification_errs)
in (let _33_24 = (Support.ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (Support.List.sortWith (fun ( _33_30 ) ( _33_34 ) -> (match ((_33_30, _33_34)) with
| ((r1, _33_29), (r2, _33_33)) -> begin
(Support.Microsoft.FStar.Range.compare r1 r2)
end)) all_errs)
in (let _33_39 = (Support.All.pipe_right all_errs (Support.List.iter (fun ( _33_38 ) -> (match (_33_38) with
| (r, msg) -> begin
(let _104_38 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.fprint2 "%s: %s\n" _104_38 msg))
end))))
in (Support.List.length all_errs))))
end))

let report = (fun ( r ) ( msg ) -> (let _33_43 = (Support.Microsoft.FStar.Util.incr num_errs)
in (let _104_44 = (let _104_43 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _104_43 msg))
in (Support.Microsoft.FStar.Util.print_string _104_44))))

let get_err_count = (fun ( _33_45 ) -> (match (()) with
| () -> begin
(Support.ST.read num_errs)
end))

let unexpected_signature_for_monad = (fun ( env ) ( m ) ( k ) -> (let _104_53 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.Microsoft_FStar_Absyn_Syntax.str _104_53)))

let expected_a_term_of_type_t_got_a_function = (fun ( env ) ( msg ) ( t ) ( e ) -> (let _104_63 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_62 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _104_63 _104_62 msg))))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun ( env ) ( t1 ) ( e ) ( t2 ) -> (let _104_74 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _104_73 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _104_72 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _104_74 _104_73 _104_72)))))

let expected_function_with_parameter_of_type = (fun ( env ) ( t1 ) ( t2 ) -> (let _104_86 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _104_85 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _104_86 _104_85))))

let expected_pattern_of_type = (fun ( env ) ( t1 ) ( e ) ( t2 ) -> (let _104_97 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _104_96 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _104_95 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _104_97 _104_96 _104_95)))))

let basic_type_error = (fun ( env ) ( eopt ) ( t1 ) ( t2 ) -> (match (eopt) with
| None -> begin
(let _104_107 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _104_106 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _104_107 _104_106)))
end
| Some (e) -> begin
(let _104_110 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _104_109 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _104_108 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _104_110 _104_109 _104_108))))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun ( env ) ( k1 ) ( k2 ) -> (let _104_118 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _104_117 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _104_118 _104_117))))

let constructor_builds_the_wrong_type = (fun ( env ) ( d ) ( t ) ( t' ) -> (let _104_129 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _104_128 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_127 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t')
in (Support.Microsoft.FStar.Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _104_129 _104_128 _104_127)))))

let constructor_fails_the_positivity_check = (fun ( env ) ( d ) ( l ) -> (let _104_134 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _104_133 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _104_134 _104_133))))

let inline_type_annotation_and_val_decl = (fun ( l ) -> (let _104_137 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _104_137)))

let inferred_type_causes_variable_to_escape = (fun ( env ) ( t ) ( x ) -> (let _104_142 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_141 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (Support.Microsoft.FStar.Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _104_142 _104_141))))

let expected_typ_of_kind = (fun ( env ) ( k1 ) ( t ) ( k2 ) -> (let _104_153 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _104_152 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_151 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _104_153 _104_152 _104_151)))))

let expected_tcon_kind = (fun ( env ) ( t ) ( k ) -> (let _104_161 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_160 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _104_161 _104_160))))

let expected_dcon_kind = (fun ( env ) ( t ) ( k ) -> (let _104_169 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_168 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _104_169 _104_168))))

let expected_function_typ = (fun ( env ) ( t ) -> (let _104_174 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _104_174)))

let expected_poly_typ = (fun ( env ) ( f ) ( t ) ( targ ) -> (let _104_185 = (Microsoft_FStar_Absyn_Print.exp_to_string f)
in (let _104_184 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _104_183 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env targ)
in (Support.Microsoft.FStar.Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _104_185 _104_184 _104_183)))))

let nonlinear_pattern_variable = (fun ( x ) -> (let m = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end)
in (Support.Microsoft.FStar.Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun ( v1 ) ( v2 ) -> (let vars = (fun ( v ) -> (let _104_192 = (Support.All.pipe_right v (Support.List.map (fun ( _33_1 ) -> (match (_33_1) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end))))
in (Support.All.pipe_right _104_192 (Support.String.concat ", "))))
in (let _104_194 = (vars v1)
in (let _104_193 = (vars v2)
in (Support.Microsoft.FStar.Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _104_194 _104_193)))))

let name_and_result = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _104_196 = (Microsoft_FStar_Absyn_Print.sli ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (_104_196, ct.Microsoft_FStar_Absyn_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun ( env ) ( e ) ( c ) ( c' ) -> (let _33_127 = (name_and_result c)
in (match (_33_127) with
| (f1, r1) -> begin
(let _33_130 = (name_and_result c')
in (match (_33_130) with
| (f2, r2) -> begin
(let _104_202 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _104_201 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r2)
in (Support.Microsoft.FStar.Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _104_202 f1 _104_201 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun ( env ) ( f ) -> (let _104_207 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
in (Support.Microsoft.FStar.Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _104_207)))

let expected_pure_expression = (fun ( e ) ( c ) -> (let _104_212 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _104_211 = (let _104_210 = (name_and_result c)
in (Support.All.pipe_left Support.Prims.fst _104_210))
in (Support.Microsoft.FStar.Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _104_212 _104_211))))

let expected_ghost_expression = (fun ( e ) ( c ) -> (let _104_217 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _104_216 = (let _104_215 = (name_and_result c)
in (Support.All.pipe_left Support.Prims.fst _104_215))
in (Support.Microsoft.FStar.Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _104_217 _104_216))))

let expected_effect_1_got_effect_2 = (fun ( c1 ) ( c2 ) -> (let _104_223 = (Microsoft_FStar_Absyn_Print.sli c1)
in (let _104_222 = (Microsoft_FStar_Absyn_Print.sli c2)
in (Support.Microsoft.FStar.Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _104_223 _104_222))))

let failed_to_prove_specification_of = (fun ( l ) ( lbls ) -> (let _104_229 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _104_228 = (Support.All.pipe_right lbls (Support.String.concat ", "))
in (Support.Microsoft.FStar.Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _104_229 _104_228))))

let failed_to_prove_specification = (fun ( lbls ) -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _33_144 -> begin
(let _104_232 = (Support.All.pipe_right lbls (Support.String.concat "\n\t"))
in (Support.Microsoft.FStar.Util.format1 "The following problems were found:\n\t%s" _104_232))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"




