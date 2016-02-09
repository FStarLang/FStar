
open Prims
let exhaustiveness_check : Prims.string = "Patterns are incomplete"

let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _190_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _190_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _190_10 _190_9))))

let ill_kinded_type : Prims.string = "Ill-kinded type"

let totality_check : Prims.string = "This term may not terminate"

let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _190_16 = (let _190_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _190_15 msg))
in (FStar_Util.print_string _190_16)))

let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _190_22 = (let _190_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _190_21 msg))
in (FStar_Util.print_string _190_22)))

let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _88_13 -> (match (_88_13) with
| (msg, r) -> begin
(let r = if (r = FStar_Range.dummyRange) then begin
(FStar_TypeChecker_Env.get_range env)
end else begin
r
end
in (r, msg))
end))))
in (let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _88_17 -> (match (()) with
| () -> begin
(let _88_18 = (let _190_30 = (let _190_29 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _190_29))
in (FStar_ST.op_Colon_Equals verification_errs _190_30))
in (let _190_31 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _190_31)))
end))))))

let report_all : Prims.unit  ->  Prims.int = (fun _88_20 -> (match (()) with
| () -> begin
(let all_errs = (FStar_Util.atomically (fun _88_21 -> (match (()) with
| () -> begin
(let x = (FStar_ST.read verification_errs)
in (let _88_23 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (FStar_List.sortWith (fun _88_29 _88_33 -> (match ((_88_29, _88_33)) with
| ((r1, _88_28), (r2, _88_32)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (let _88_38 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _88_37 -> (match (_88_37) with
| (r, msg) -> begin
(let _190_38 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _190_38 msg))
end))))
in (FStar_List.length all_errs))))
end))

let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _88_42 = (FStar_Util.incr num_errs)
in (let _190_44 = (let _190_43 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _190_43 msg))
in (FStar_Util.print_string _190_44))))

let get_err_count : Prims.unit  ->  Prims.int = (fun _88_44 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _190_53 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => WP a => Effect);\ngot %s" m.FStar_Ident.str _190_53)))

let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _190_63 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_62 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _190_63 _190_62 msg))))

let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _190_74 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _190_73 = (FStar_Syntax_Print.term_to_string e)
in (let _190_72 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _190_74 _190_73 _190_72)))))

let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _190_86 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _190_85 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _190_86 _190_85))))

let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _190_97 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _190_96 = (FStar_Syntax_Print.term_to_string e)
in (let _190_95 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _190_97 _190_96 _190_95)))))

let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _190_107 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _190_106 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _190_107 _190_106)))
end
| Some (e) -> begin
(let _190_110 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _190_109 = (FStar_Syntax_Print.term_to_string e)
in (let _190_108 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _190_110 _190_109 _190_108))))
end))

let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"

let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _190_118 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _190_117 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _190_118 _190_117))))

let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _190_129 = (FStar_Syntax_Print.term_to_string d)
in (let _190_128 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_127 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _190_129 _190_128 _190_127)))))

let constructor_fails_the_positivity_check = (fun env d l -> (let _190_134 = (FStar_Syntax_Print.term_to_string d)
in (let _190_133 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _190_134 _190_133))))

let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _190_137 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _190_137)))

let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _190_145 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_144 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _190_145 _190_144))))

let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _190_156 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _190_155 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_154 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _190_156 _190_155 _190_154)))))

let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _190_164 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_163 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _190_164 _190_163))))

let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _190_172 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_171 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _190_172 _190_171))))

let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _190_177 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _190_177)))

let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _190_188 = (FStar_Syntax_Print.term_to_string f)
in (let _190_187 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _190_186 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _190_188 _190_187 _190_186)))))

let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (let vars = (fun v -> (let _190_197 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _190_197 (FStar_String.concat ", "))))
in (let _190_199 = (vars v1)
in (let _190_198 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _190_199 _190_198)))))

let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
("GTot", t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _190_201 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in (_190_201, ct.FStar_Syntax_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (let _88_119 = (name_and_result c)
in (match (_88_119) with
| (f1, r1) -> begin
(let _88_122 = (name_and_result c')
in (match (_88_122) with
| (f2, r2) -> begin
(let _190_207 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _190_206 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _190_207 f1 _190_206 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _190_212 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _190_212)))

let expected_pure_expression = (fun e c -> (let _190_217 = (FStar_Syntax_Print.term_to_string e)
in (let _190_216 = (let _190_215 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _190_215))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _190_217 _190_216))))

let expected_ghost_expression = (fun e c -> (let _190_222 = (FStar_Syntax_Print.term_to_string e)
in (let _190_221 = (let _190_220 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _190_220))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _190_222 _190_221))))

let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _190_228 = (FStar_Syntax_Print.lid_to_string c1)
in (let _190_227 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _190_228 _190_227))))

let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _190_234 = (FStar_Syntax_Print.lbname_to_string l)
in (let _190_233 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _190_234 _190_233))))

let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _88_136 -> begin
(let _190_237 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _190_237))
end))

let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"

let cardinality_constraint_violated = (fun l a -> (let _190_241 = (FStar_Syntax_Print.lid_to_string l)
in (let _190_240 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _190_241 _190_240))))




