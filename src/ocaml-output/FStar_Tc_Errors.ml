
open Prims
let exhaustiveness_check : Prims.string = "Patterns are incomplete"

let subtyping_failed : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _152_10 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _152_9 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _152_10 _152_9))))

let ill_kinded_type : Prims.string = "Ill-kinded type"

let totality_check : Prims.string = "This term may not terminate"

let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _152_16 = (let _152_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _152_15 msg))
in (FStar_Util.print_string _152_16)))

let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _152_22 = (let _152_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _152_21 msg))
in (FStar_Util.print_string _152_22)))

let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

let add_errors : FStar_Tc_Env.env  ->  (Prims.string * Prims.int64) Prims.list  ->  Prims.unit = (fun env errs -> (let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _49_14 -> (match (_49_14) with
| (msg, r) -> begin
(let r = if (r = FStar_Absyn_Syntax.dummyRange) then begin
(FStar_Tc_Env.get_range env)
end else begin
r
end
in (r, msg))
end))))
in (let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _49_18 -> (match (()) with
| () -> begin
(let _49_19 = (let _152_30 = (let _152_29 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _152_29))
in (FStar_ST.op_Colon_Equals verification_errs _152_30))
in (let _152_31 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _152_31)))
end))))))

let report_all : Prims.unit  ->  Prims.int = (fun _49_21 -> (match (()) with
| () -> begin
(let all_errs = (FStar_Util.atomically (fun _49_22 -> (match (()) with
| () -> begin
(let x = (FStar_ST.read verification_errs)
in (let _49_24 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (FStar_List.sortWith (fun _49_30 _49_34 -> (match ((_49_30, _49_34)) with
| ((r1, _49_29), (r2, _49_33)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (let _49_39 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _49_38 -> (match (_49_38) with
| (r, msg) -> begin
(let _152_38 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _152_38 msg))
end))))
in (FStar_List.length all_errs))))
end))

let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _49_43 = (FStar_Util.incr num_errs)
in (let _152_44 = (let _152_43 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _152_43 msg))
in (FStar_Util.print_string _152_44))))

let get_err_count : Prims.unit  ->  Prims.int = (fun _49_45 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

let unexpected_signature_for_monad : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env m k -> (let _152_53 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.FStar_Ident.str _152_53)))

let expected_a_term_of_type_t_got_a_function : FStar_Tc_Env.env  ->  Prims.string  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun env msg t e -> (let _152_63 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_62 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _152_63 _152_62 msg))))

let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _152_74 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _152_73 = (FStar_Absyn_Print.exp_to_string e)
in (let _152_72 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _152_74 _152_73 _152_72)))))

let expected_function_with_parameter_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _152_86 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _152_85 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _152_86 _152_85))))

let expected_pattern_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _152_97 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _152_96 = (FStar_Absyn_Print.exp_to_string e)
in (let _152_95 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _152_97 _152_96 _152_95)))))

let basic_type_error : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _152_107 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _152_106 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _152_107 _152_106)))
end
| Some (e) -> begin
(let _152_110 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _152_109 = (FStar_Absyn_Print.exp_to_string e)
in (let _152_108 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _152_110 _152_109 _152_108))))
end))

let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"

let incompatible_kinds : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 k2 -> (let _152_118 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _152_117 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _152_118 _152_117))))

let constructor_builds_the_wrong_type : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env d t t' -> (let _152_129 = (FStar_Absyn_Print.exp_to_string d)
in (let _152_128 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_127 = (FStar_Tc_Normalize.typ_norm_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _152_129 _152_128 _152_127)))))

let constructor_fails_the_positivity_check = (fun env d l -> (let _152_134 = (FStar_Absyn_Print.exp_to_string d)
in (let _152_133 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _152_134 _152_133))))

let inline_type_annotation_and_val_decl : FStar_Ident.lident  ->  Prims.string = (fun l -> (let _152_137 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _152_137)))

let inferred_type_causes_variable_to_escape = (fun env t x -> (let _152_142 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_141 = (FStar_Absyn_Print.strBvd x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _152_142 _152_141))))

let expected_typ_of_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 t k2 -> (let _152_153 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _152_152 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_151 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _152_153 _152_152 _152_151)))))

let expected_tcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _152_161 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_160 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _152_161 _152_160))))

let expected_dcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _152_169 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_168 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _152_169 _152_168))))

let expected_function_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t -> (let _152_174 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _152_174)))

let expected_poly_typ : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f t targ -> (let _152_185 = (FStar_Absyn_Print.exp_to_string f)
in (let _152_184 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _152_183 = (FStar_Tc_Normalize.typ_norm_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _152_185 _152_184 _152_183)))))

let nonlinear_pattern_variable = (fun x -> (let m = (match (x) with
| FStar_Util.Inl (x) -> begin
(FStar_Absyn_Print.strBvd x)
end
| FStar_Util.Inr (a) -> begin
(FStar_Absyn_Print.strBvd a)
end)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun v1 v2 -> (let vars = (fun v -> (let _152_192 = (FStar_All.pipe_right v (FStar_List.map (fun _49_1 -> (match (_49_1) with
| FStar_Util.Inl (a) -> begin
(FStar_Absyn_Print.strBvd a)
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Print.strBvd x)
end))))
in (FStar_All.pipe_right _152_192 (FStar_String.concat ", "))))
in (let _152_194 = (vars v1)
in (let _152_193 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _152_194 _152_193)))))

let name_and_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _152_196 = (FStar_Absyn_Print.sli ct.FStar_Absyn_Syntax.effect_name)
in (_152_196, ct.FStar_Absyn_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (let _49_127 = (name_and_result c)
in (match (_49_127) with
| (f1, r1) -> begin
(let _49_130 = (name_and_result c')
in (match (_49_130) with
| (f2, r2) -> begin
(let _152_202 = (FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _152_201 = (FStar_Tc_Normalize.typ_norm_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _152_202 f1 _152_201 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f -> (let _152_207 = (FStar_Tc_Normalize.formula_norm_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _152_207)))

let expected_pure_expression = (fun e c -> (let _152_212 = (FStar_Absyn_Print.exp_to_string e)
in (let _152_211 = (let _152_210 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _152_210))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _152_212 _152_211))))

let expected_ghost_expression = (fun e c -> (let _152_217 = (FStar_Absyn_Print.exp_to_string e)
in (let _152_216 = (let _152_215 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _152_215))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _152_217 _152_216))))

let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _152_223 = (FStar_Absyn_Print.sli c1)
in (let _152_222 = (FStar_Absyn_Print.sli c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _152_223 _152_222))))

let failed_to_prove_specification_of : FStar_Absyn_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _152_229 = (FStar_Absyn_Print.lbname_to_string l)
in (let _152_228 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _152_229 _152_228))))

let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _49_144 -> begin
(let _152_232 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _152_232))
end))

let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"

let cardinality_constraint_violated = (fun l a -> (let _152_236 = (FStar_Absyn_Print.sli l)
in (let _152_235 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _152_236 _152_235))))




