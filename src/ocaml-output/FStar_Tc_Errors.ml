
open Prims
# 31 "FStar.Tc.Errors.fst"
let exhaustiveness_check : Prims.string = "Patterns are incomplete"

# 32 "FStar.Tc.Errors.fst"
let subtyping_failed : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _119_10 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _119_9 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _119_10 _119_9))))

# 35 "FStar.Tc.Errors.fst"
let ill_kinded_type : Prims.string = "Ill-kinded type"

# 36 "FStar.Tc.Errors.fst"
let totality_check : Prims.string = "This term may not terminate"

# 38 "FStar.Tc.Errors.fst"
let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _119_16 = (let _119_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _119_15 msg))
in (FStar_Util.print_string _119_16)))

# 41 "FStar.Tc.Errors.fst"
let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _119_22 = (let _119_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _119_21 msg))
in (FStar_Util.print_string _119_22)))

# 44 "FStar.Tc.Errors.fst"
let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 45 "FStar.Tc.Errors.fst"
let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 46 "FStar.Tc.Errors.fst"
let add_errors : FStar_Tc_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (
# 47 "FStar.Tc.Errors.fst"
let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _40_14 -> (match (_40_14) with
| (msg, r) -> begin
(
# 47 "FStar.Tc.Errors.fst"
let r = if (r = FStar_Absyn_Syntax.dummyRange) then begin
(FStar_Tc_Env.get_range env)
end else begin
r
end
in (r, msg))
end))))
in (
# 48 "FStar.Tc.Errors.fst"
let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _40_18 -> (match (()) with
| () -> begin
(
# 50 "FStar.Tc.Errors.fst"
let _40_19 = (let _119_30 = (let _119_29 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _119_29))
in (FStar_ST.op_Colon_Equals verification_errs _119_30))
in (let _119_31 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _119_31)))
end))))))

# 52 "FStar.Tc.Errors.fst"
let report_all : Prims.unit  ->  Prims.int = (fun _40_21 -> (match (()) with
| () -> begin
(
# 53 "FStar.Tc.Errors.fst"
let all_errs = (FStar_Util.atomically (fun _40_22 -> (match (()) with
| () -> begin
(
# 53 "FStar.Tc.Errors.fst"
let x = (FStar_ST.read verification_errs)
in (
# 53 "FStar.Tc.Errors.fst"
let _40_24 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (
# 54 "FStar.Tc.Errors.fst"
let all_errs = (FStar_List.sortWith (fun _40_30 _40_34 -> (match ((_40_30, _40_34)) with
| ((r1, _40_29), (r2, _40_33)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (
# 55 "FStar.Tc.Errors.fst"
let _40_39 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _40_38 -> (match (_40_38) with
| (r, msg) -> begin
(let _119_38 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _119_38 msg))
end))))
in (FStar_List.length all_errs))))
end))

# 59 "FStar.Tc.Errors.fst"
let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (
# 60 "FStar.Tc.Errors.fst"
let _40_43 = (FStar_Util.incr num_errs)
in (let _119_44 = (let _119_43 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _119_43 msg))
in (FStar_Util.print_string _119_44))))

# 62 "FStar.Tc.Errors.fst"
let get_err_count : Prims.unit  ->  Prims.int = (fun _40_45 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

# 64 "FStar.Tc.Errors.fst"
let unexpected_signature_for_monad : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env m k -> (let _119_53 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.FStar_Ident.str _119_53)))

# 68 "FStar.Tc.Errors.fst"
let expected_a_term_of_type_t_got_a_function : FStar_Tc_Env.env  ->  Prims.string  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun env msg t e -> (let _119_63 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_62 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _119_63 _119_62 msg))))

# 72 "FStar.Tc.Errors.fst"
let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

# 75 "FStar.Tc.Errors.fst"
let expected_expression_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _119_74 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _119_73 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_72 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _119_74 _119_73 _119_72)))))

# 79 "FStar.Tc.Errors.fst"
let expected_function_with_parameter_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _119_86 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _119_85 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _119_86 _119_85))))

# 83 "FStar.Tc.Errors.fst"
let expected_pattern_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _119_97 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _119_96 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_95 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _119_97 _119_96 _119_95)))))

# 87 "FStar.Tc.Errors.fst"
let basic_type_error : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _119_107 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _119_106 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _119_107 _119_106)))
end
| Some (e) -> begin
(let _119_110 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _119_109 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_108 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _119_110 _119_109 _119_108))))
end))

# 94 "FStar.Tc.Errors.fst"
let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"

# 97 "FStar.Tc.Errors.fst"
let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"

# 100 "FStar.Tc.Errors.fst"
let incompatible_kinds : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 k2 -> (let _119_118 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _119_117 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _119_118 _119_117))))

# 104 "FStar.Tc.Errors.fst"
let constructor_builds_the_wrong_type : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env d t t' -> (let _119_129 = (FStar_Absyn_Print.exp_to_string d)
in (let _119_128 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_127 = (FStar_Tc_Normalize.typ_norm_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _119_129 _119_128 _119_127)))))

# 108 "FStar.Tc.Errors.fst"
let constructor_fails_the_positivity_check = (fun env d l -> (let _119_134 = (FStar_Absyn_Print.exp_to_string d)
in (let _119_133 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _119_134 _119_133))))

# 112 "FStar.Tc.Errors.fst"
let inline_type_annotation_and_val_decl : FStar_Ident.lident  ->  Prims.string = (fun l -> (let _119_137 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _119_137)))

# 116 "FStar.Tc.Errors.fst"
let inferred_type_causes_variable_to_escape = (fun env t x -> (let _119_142 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_141 = (FStar_Absyn_Print.strBvd x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _119_142 _119_141))))

# 120 "FStar.Tc.Errors.fst"
let expected_typ_of_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 t k2 -> (let _119_153 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _119_152 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_151 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _119_153 _119_152 _119_151)))))

# 124 "FStar.Tc.Errors.fst"
let expected_tcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _119_161 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_160 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _119_161 _119_160))))

# 128 "FStar.Tc.Errors.fst"
let expected_dcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _119_169 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_168 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _119_169 _119_168))))

# 132 "FStar.Tc.Errors.fst"
let expected_function_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t -> (let _119_174 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _119_174)))

# 136 "FStar.Tc.Errors.fst"
let expected_poly_typ : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f t targ -> (let _119_185 = (FStar_Absyn_Print.exp_to_string f)
in (let _119_184 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _119_183 = (FStar_Tc_Normalize.typ_norm_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _119_185 _119_184 _119_183)))))

# 140 "FStar.Tc.Errors.fst"
let nonlinear_pattern_variable = (fun x -> (
# 141 "FStar.Tc.Errors.fst"
let m = (match (x) with
| FStar_Util.Inl (x) -> begin
(FStar_Absyn_Print.strBvd x)
end
| FStar_Util.Inr (a) -> begin
(FStar_Absyn_Print.strBvd a)
end)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))

# 146 "FStar.Tc.Errors.fst"
let disjunctive_pattern_vars = (fun v1 v2 -> (
# 147 "FStar.Tc.Errors.fst"
let vars = (fun v -> (let _119_192 = (FStar_All.pipe_right v (FStar_List.map (fun _40_1 -> (match (_40_1) with
| FStar_Util.Inl (a) -> begin
(FStar_Absyn_Print.strBvd a)
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Print.strBvd x)
end))))
in (FStar_All.pipe_right _119_192 (FStar_String.concat ", "))))
in (let _119_194 = (vars v1)
in (let _119_193 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _119_194 _119_193)))))

# 155 "FStar.Tc.Errors.fst"
let name_and_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _119_196 = (FStar_Absyn_Print.sli ct.FStar_Absyn_Syntax.effect_name)
in (_119_196, ct.FStar_Absyn_Syntax.result_typ))
end))

# 159 "FStar.Tc.Errors.fst"
let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (
# 160 "FStar.Tc.Errors.fst"
let _40_127 = (name_and_result c)
in (match (_40_127) with
| (f1, r1) -> begin
(
# 161 "FStar.Tc.Errors.fst"
let _40_130 = (name_and_result c')
in (match (_40_130) with
| (f2, r2) -> begin
(let _119_202 = (FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _119_201 = (FStar_Tc_Normalize.typ_norm_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _119_202 f1 _119_201 f2)))
end))
end)))

# 166 "FStar.Tc.Errors.fst"
let unexpected_non_trivial_precondition_on_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f -> (let _119_207 = (FStar_Tc_Normalize.formula_norm_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _119_207)))

# 169 "FStar.Tc.Errors.fst"
let expected_pure_expression = (fun e c -> (let _119_212 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_211 = (let _119_210 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _119_210))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _119_212 _119_211))))

# 172 "FStar.Tc.Errors.fst"
let expected_ghost_expression = (fun e c -> (let _119_217 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_216 = (let _119_215 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _119_215))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _119_217 _119_216))))

# 175 "FStar.Tc.Errors.fst"
let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _119_223 = (FStar_Absyn_Print.sli c1)
in (let _119_222 = (FStar_Absyn_Print.sli c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _119_223 _119_222))))

# 178 "FStar.Tc.Errors.fst"
let failed_to_prove_specification_of : FStar_Absyn_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _119_229 = (FStar_Absyn_Print.lbname_to_string l)
in (let _119_228 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _119_229 _119_228))))

# 181 "FStar.Tc.Errors.fst"
let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _40_144 -> begin
(let _119_232 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _119_232))
end))

# 186 "FStar.Tc.Errors.fst"
let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"

# 188 "FStar.Tc.Errors.fst"
let cardinality_constraint_violated = (fun l a -> (let _119_236 = (FStar_Absyn_Print.sli l)
in (let _119_235 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _119_236 _119_235))))




