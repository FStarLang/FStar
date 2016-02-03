
open Prims
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun env t1 t2 x -> (let _175_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _175_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _175_10 _175_9))))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun r msg -> (let _175_16 = (let _175_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _175_15 msg))
in (FStar_Util.print_string _175_16)))

let warn = (fun r msg -> (let _175_22 = (let _175_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _175_21 msg))
in (FStar_Util.print_string _175_22)))

let num_errs = (FStar_Util.mk_ref 0)

let verification_errs = (FStar_Util.mk_ref [])

let add_errors = (fun env errs -> (let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _84_13 -> (match (_84_13) with
| (msg, r) -> begin
(let r = if (r = FStar_Range.dummyRange) then begin
(FStar_TypeChecker_Env.get_range env)
end else begin
r
end
in (r, msg))
end))))
in (let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _84_17 -> (match (()) with
| () -> begin
(let _84_18 = (let _175_30 = (let _175_29 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _175_29))
in (FStar_ST.op_Colon_Equals verification_errs _175_30))
in (let _175_31 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _175_31)))
end))))))

let report_all = (fun _84_20 -> (match (()) with
| () -> begin
(let all_errs = (FStar_Util.atomically (fun _84_21 -> (match (()) with
| () -> begin
(let x = (FStar_ST.read verification_errs)
in (let _84_23 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (FStar_List.sortWith (fun _84_29 _84_33 -> (match ((_84_29, _84_33)) with
| ((r1, _84_28), (r2, _84_32)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (let _84_38 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _84_37 -> (match (_84_37) with
| (r, msg) -> begin
(let _175_38 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _175_38 msg))
end))))
in (FStar_List.length all_errs))))
end))

let report = (fun r msg -> (let _84_42 = (FStar_Util.incr num_errs)
in (let _175_44 = (let _175_43 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _175_43 msg))
in (FStar_Util.print_string _175_44))))

let get_err_count = (fun _84_44 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

let unexpected_signature_for_monad = (fun env m k -> (let _175_53 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => WP a => Effect);\ngot %s" m.FStar_Ident.str _175_53)))

let expected_a_term_of_type_t_got_a_function = (fun env msg t e -> (let _175_63 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_62 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _175_63 _175_62 msg))))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun env t1 e t2 -> (let _175_74 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _175_73 = (FStar_Syntax_Print.term_to_string e)
in (let _175_72 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _175_74 _175_73 _175_72)))))

let expected_function_with_parameter_of_type = (fun env t1 t2 -> (let _175_86 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _175_85 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _175_86 _175_85))))

let expected_pattern_of_type = (fun env t1 e t2 -> (let _175_97 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _175_96 = (FStar_Syntax_Print.term_to_string e)
in (let _175_95 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _175_97 _175_96 _175_95)))))

let basic_type_error = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _175_107 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _175_106 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _175_107 _175_106)))
end
| Some (e) -> begin
(let _175_110 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _175_109 = (FStar_Syntax_Print.term_to_string e)
in (let _175_108 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _175_110 _175_109 _175_108))))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun env k1 k2 -> (let _175_118 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _175_117 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _175_118 _175_117))))

let constructor_builds_the_wrong_type = (fun env d t t' -> (let _175_129 = (FStar_Syntax_Print.term_to_string d)
in (let _175_128 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_127 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _175_129 _175_128 _175_127)))))

let constructor_fails_the_positivity_check = (fun env d l -> (let _175_134 = (FStar_Syntax_Print.term_to_string d)
in (let _175_133 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _175_134 _175_133))))

let inline_type_annotation_and_val_decl = (fun l -> (let _175_137 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _175_137)))

let inferred_type_causes_variable_to_escape = (fun env t x -> (let _175_145 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_144 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _175_145 _175_144))))

let expected_typ_of_kind = (fun env k1 t k2 -> (let _175_156 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _175_155 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_154 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _175_156 _175_155 _175_154)))))

let expected_tcon_kind = (fun env t k -> (let _175_164 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_163 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _175_164 _175_163))))

let expected_dcon_kind = (fun env t k -> (let _175_172 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_171 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _175_172 _175_171))))

let expected_function_typ = (fun env t -> (let _175_177 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _175_177)))

let expected_poly_typ = (fun env f t targ -> (let _175_188 = (FStar_Syntax_Print.term_to_string f)
in (let _175_187 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _175_186 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _175_188 _175_187 _175_186)))))

let nonlinear_pattern_variable = (fun x -> (let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun v1 v2 -> (let vars = (fun v -> (let _175_197 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _175_197 (FStar_String.concat ", "))))
in (let _175_199 = (vars v1)
in (let _175_198 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _175_199 _175_198)))))

let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
("GTot", t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _175_201 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in (_175_201, ct.FStar_Syntax_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (let _84_119 = (name_and_result c)
in (match (_84_119) with
| (f1, r1) -> begin
(let _84_122 = (name_and_result c')
in (match (_84_122) with
| (f2, r2) -> begin
(let _175_207 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _175_206 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _175_207 f1 _175_206 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun env f -> (let _175_212 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _175_212)))

let expected_pure_expression = (fun e c -> (let _175_217 = (FStar_Syntax_Print.term_to_string e)
in (let _175_216 = (let _175_215 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _175_215))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _175_217 _175_216))))

let expected_ghost_expression = (fun e c -> (let _175_222 = (FStar_Syntax_Print.term_to_string e)
in (let _175_221 = (let _175_220 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _175_220))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _175_222 _175_221))))

let expected_effect_1_got_effect_2 = (fun c1 c2 -> (let _175_228 = (FStar_Syntax_Print.lid_to_string c1)
in (let _175_227 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _175_228 _175_227))))

let failed_to_prove_specification_of = (fun l lbls -> (let _175_234 = (FStar_Syntax_Print.lbname_to_string l)
in (let _175_233 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _175_234 _175_233))))

let failed_to_prove_specification = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _84_136 -> begin
(let _175_237 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _175_237))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"

let cardinality_constraint_violated = (fun l a -> (let _175_241 = (FStar_Syntax_Print.lid_to_string l)
in (let _175_240 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _175_241 _175_240))))




