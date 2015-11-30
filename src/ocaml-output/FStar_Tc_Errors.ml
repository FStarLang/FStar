
open Prims
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun env t1 t2 x -> (let _99_10 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _99_9 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _99_10 _99_9))))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun r msg -> (let _99_16 = (let _99_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _99_15 msg))
in (FStar_Util.print_string _99_16)))

let warn = (fun r msg -> (let _99_22 = (let _99_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _99_21 msg))
in (FStar_Util.print_string _99_22)))

let num_errs = (FStar_Util.mk_ref 0)

let verification_errs = (FStar_Util.mk_ref [])

let add_errors = (fun env errs -> (let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _34_14 -> (match (_34_14) with
| (msg, r) -> begin
(let r = if (r = FStar_Absyn_Syntax.dummyRange) then begin
(FStar_Tc_Env.get_range env)
end else begin
r
end
in (r, msg))
end))))
in (let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _34_18 -> (match (()) with
| () -> begin
(let _34_19 = (let _99_30 = (let _99_29 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _99_29))
in (FStar_ST.op_Colon_Equals verification_errs _99_30))
in (let _99_31 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _99_31)))
end))))))

let report_all = (fun _34_21 -> (match (()) with
| () -> begin
(let all_errs = (FStar_Util.atomically (fun _34_22 -> (match (()) with
| () -> begin
(let x = (FStar_ST.read verification_errs)
in (let _34_24 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (FStar_List.sortWith (fun _34_30 _34_34 -> (match ((_34_30, _34_34)) with
| ((r1, _34_29), (r2, _34_33)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (let _34_39 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _34_38 -> (match (_34_38) with
| (r, msg) -> begin
(let _99_38 = (FStar_Range.string_of_range r)
in (FStar_Util.fprint2 "%s: %s\n" _99_38 msg))
end))))
in (FStar_List.length all_errs))))
end))

let report = (fun r msg -> (let _34_43 = (FStar_Util.incr num_errs)
in (let _99_44 = (let _99_43 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _99_43 msg))
in (FStar_Util.print_string _99_44))))

let get_err_count = (fun _34_45 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

let unexpected_signature_for_monad = (fun env m k -> (let _99_53 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.FStar_Absyn_Syntax.str _99_53)))

let expected_a_term_of_type_t_got_a_function = (fun env msg t e -> (let _99_63 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_62 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _99_63 _99_62 msg))))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun env t1 e t2 -> (let _99_74 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _99_73 = (FStar_Absyn_Print.exp_to_string e)
in (let _99_72 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _99_74 _99_73 _99_72)))))

let expected_function_with_parameter_of_type = (fun env t1 t2 -> (let _99_86 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _99_85 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _99_86 _99_85))))

let expected_pattern_of_type = (fun env t1 e t2 -> (let _99_97 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _99_96 = (FStar_Absyn_Print.exp_to_string e)
in (let _99_95 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _99_97 _99_96 _99_95)))))

let basic_type_error = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _99_107 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _99_106 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _99_107 _99_106)))
end
| Some (e) -> begin
(let _99_110 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _99_109 = (FStar_Absyn_Print.exp_to_string e)
in (let _99_108 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _99_110 _99_109 _99_108))))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun env k1 k2 -> (let _99_118 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _99_117 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _99_118 _99_117))))

let constructor_builds_the_wrong_type = (fun env d t t' -> (let _99_129 = (FStar_Absyn_Print.exp_to_string d)
in (let _99_128 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_127 = (FStar_Tc_Normalize.typ_norm_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _99_129 _99_128 _99_127)))))

let constructor_fails_the_positivity_check = (fun env d l -> (let _99_134 = (FStar_Absyn_Print.exp_to_string d)
in (let _99_133 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _99_134 _99_133))))

let inline_type_annotation_and_val_decl = (fun l -> (let _99_137 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _99_137)))

let inferred_type_causes_variable_to_escape = (fun env t x -> (let _99_142 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_141 = (FStar_Absyn_Print.strBvd x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _99_142 _99_141))))

let expected_typ_of_kind = (fun env k1 t k2 -> (let _99_153 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _99_152 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_151 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _99_153 _99_152 _99_151)))))

let expected_tcon_kind = (fun env t k -> (let _99_161 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_160 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _99_161 _99_160))))

let expected_dcon_kind = (fun env t k -> (let _99_169 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_168 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _99_169 _99_168))))

let expected_function_typ = (fun env t -> (let _99_174 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _99_174)))

let expected_poly_typ = (fun env f t targ -> (let _99_185 = (FStar_Absyn_Print.exp_to_string f)
in (let _99_184 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _99_183 = (FStar_Tc_Normalize.typ_norm_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _99_185 _99_184 _99_183)))))

let nonlinear_pattern_variable = (fun x -> (let m = (match (x) with
| FStar_Util.Inl (x) -> begin
(FStar_Absyn_Print.strBvd x)
end
| FStar_Util.Inr (a) -> begin
(FStar_Absyn_Print.strBvd a)
end)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun v1 v2 -> (let vars = (fun v -> (let _99_192 = (FStar_All.pipe_right v (FStar_List.map (fun _34_1 -> (match (_34_1) with
| FStar_Util.Inl (a) -> begin
(FStar_Absyn_Print.strBvd a)
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Print.strBvd x)
end))))
in (FStar_All.pipe_right _99_192 (FStar_String.concat ", "))))
in (let _99_194 = (vars v1)
in (let _99_193 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _99_194 _99_193)))))

let name_and_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _99_196 = (FStar_Absyn_Print.sli ct.FStar_Absyn_Syntax.effect_name)
in (_99_196, ct.FStar_Absyn_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (let _34_127 = (name_and_result c)
in (match (_34_127) with
| (f1, r1) -> begin
(let _34_130 = (name_and_result c')
in (match (_34_130) with
| (f2, r2) -> begin
(let _99_202 = (FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _99_201 = (FStar_Tc_Normalize.typ_norm_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _99_202 f1 _99_201 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun env f -> (let _99_207 = (FStar_Tc_Normalize.formula_norm_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _99_207)))

let expected_pure_expression = (fun e c -> (let _99_212 = (FStar_Absyn_Print.exp_to_string e)
in (let _99_211 = (let _99_210 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _99_210))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _99_212 _99_211))))

let expected_ghost_expression = (fun e c -> (let _99_217 = (FStar_Absyn_Print.exp_to_string e)
in (let _99_216 = (let _99_215 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _99_215))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _99_217 _99_216))))

let expected_effect_1_got_effect_2 = (fun c1 c2 -> (let _99_223 = (FStar_Absyn_Print.sli c1)
in (let _99_222 = (FStar_Absyn_Print.sli c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _99_223 _99_222))))

let failed_to_prove_specification_of = (fun l lbls -> (let _99_229 = (FStar_Absyn_Print.lbname_to_string l)
in (let _99_228 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _99_229 _99_228))))

let failed_to_prove_specification = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _34_144 -> begin
(let _99_232 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _99_232))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"

let cardinality_constraint_violated = (fun l a -> (let _99_236 = (FStar_Absyn_Print.sli l)
in (let _99_235 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _99_236 _99_235))))




