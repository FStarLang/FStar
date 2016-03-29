
open Prims
# 28 "FStar.Tc.Errors.fst"
let exhaustiveness_check : Prims.string = "Patterns are incomplete"

# 31 "FStar.Tc.Errors.fst"
let subtyping_failed : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _112_10 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _112_9 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _112_10 _112_9))))

# 34 "FStar.Tc.Errors.fst"
let ill_kinded_type : Prims.string = "Ill-kinded type"

# 35 "FStar.Tc.Errors.fst"
let totality_check : Prims.string = "This term may not terminate"

# 36 "FStar.Tc.Errors.fst"
let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _112_17 = (let _112_16 = (let _112_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _112_15 msg))
in (_112_16)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s" _112_17)))

# 39 "FStar.Tc.Errors.fst"
let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _112_24 = (let _112_23 = (let _112_22 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _112_22 msg))
in (_112_23)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s" _112_24)))

# 42 "FStar.Tc.Errors.fst"
let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 44 "FStar.Tc.Errors.fst"
let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 45 "FStar.Tc.Errors.fst"
let add_errors : FStar_Tc_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (
# 47 "FStar.Tc.Errors.fst"
let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _33_14 -> (match (_33_14) with
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
in (FStar_Util.atomically (fun _33_18 -> (match (()) with
| () -> begin
(
# 50 "FStar.Tc.Errors.fst"
let _33_19 = (let _112_32 = (let _112_31 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _112_31))
in (FStar_ST.op_Colon_Equals verification_errs _112_32))
in (let _112_33 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _112_33)))
end))))))

# 51 "FStar.Tc.Errors.fst"
let report_all : Prims.unit  ->  Prims.int = (fun _33_21 -> (match (()) with
| () -> begin
(
# 53 "FStar.Tc.Errors.fst"
let all_errs = (FStar_Util.atomically (fun _33_22 -> (match (()) with
| () -> begin
(
# 53 "FStar.Tc.Errors.fst"
let x = (FStar_ST.read verification_errs)
in (
# 53 "FStar.Tc.Errors.fst"
let _33_24 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (
# 54 "FStar.Tc.Errors.fst"
let all_errs = (FStar_List.sortWith (fun _33_30 _33_34 -> (match ((_33_30, _33_34)) with
| ((r1, _33_29), (r2, _33_33)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (
# 55 "FStar.Tc.Errors.fst"
let _33_39 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _33_38 -> (match (_33_38) with
| (r, msg) -> begin
(let _112_40 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _112_40 msg))
end))))
in (FStar_List.length all_errs))))
end))

# 56 "FStar.Tc.Errors.fst"
let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (
# 60 "FStar.Tc.Errors.fst"
let _33_43 = (FStar_Util.incr num_errs)
in (let _112_47 = (let _112_46 = (let _112_45 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _112_45 msg))
in (_112_46)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s" _112_47))))

# 61 "FStar.Tc.Errors.fst"
let get_err_count : Prims.unit  ->  Prims.int = (fun _33_45 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

# 62 "FStar.Tc.Errors.fst"
let unexpected_signature_for_monad : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env m k -> (let _112_56 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.FStar_Ident.str _112_56)))

# 66 "FStar.Tc.Errors.fst"
let expected_a_term_of_type_t_got_a_function : FStar_Tc_Env.env  ->  Prims.string  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun env msg t e -> (let _112_66 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_65 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _112_66 _112_65 msg))))

# 70 "FStar.Tc.Errors.fst"
let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

# 73 "FStar.Tc.Errors.fst"
let expected_expression_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _112_77 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _112_76 = (FStar_Absyn_Print.exp_to_string e)
in (let _112_75 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _112_77 _112_76 _112_75)))))

# 77 "FStar.Tc.Errors.fst"
let expected_function_with_parameter_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _112_89 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _112_88 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _112_89 _112_88))))

# 81 "FStar.Tc.Errors.fst"
let expected_pattern_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _112_100 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _112_99 = (FStar_Absyn_Print.exp_to_string e)
in (let _112_98 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _112_100 _112_99 _112_98)))))

# 85 "FStar.Tc.Errors.fst"
let basic_type_error : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _112_110 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _112_109 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _112_110 _112_109)))
end
| Some (e) -> begin
(let _112_113 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _112_112 = (FStar_Absyn_Print.exp_to_string e)
in (let _112_111 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _112_113 _112_112 _112_111))))
end))

# 92 "FStar.Tc.Errors.fst"
let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"

# 95 "FStar.Tc.Errors.fst"
let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"

# 98 "FStar.Tc.Errors.fst"
let incompatible_kinds : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 k2 -> (let _112_121 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _112_120 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _112_121 _112_120))))

# 102 "FStar.Tc.Errors.fst"
let constructor_builds_the_wrong_type : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env d t t' -> (let _112_132 = (FStar_Absyn_Print.exp_to_string d)
in (let _112_131 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_130 = (FStar_Tc_Normalize.typ_norm_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _112_132 _112_131 _112_130)))))

# 106 "FStar.Tc.Errors.fst"
let constructor_fails_the_positivity_check = (fun env d l -> (let _112_137 = (FStar_Absyn_Print.exp_to_string d)
in (let _112_136 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _112_137 _112_136))))

# 110 "FStar.Tc.Errors.fst"
let inline_type_annotation_and_val_decl : FStar_Ident.lident  ->  Prims.string = (fun l -> (let _112_140 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _112_140)))

# 113 "FStar.Tc.Errors.fst"
let inferred_type_causes_variable_to_escape = (fun env t x -> (let _112_145 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_144 = (FStar_Absyn_Print.strBvd x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _112_145 _112_144))))

# 118 "FStar.Tc.Errors.fst"
let expected_typ_of_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 t k2 -> (let _112_156 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _112_155 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_154 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _112_156 _112_155 _112_154)))))

# 122 "FStar.Tc.Errors.fst"
let expected_tcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _112_164 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_163 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _112_164 _112_163))))

# 126 "FStar.Tc.Errors.fst"
let expected_dcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _112_172 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_171 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _112_172 _112_171))))

# 130 "FStar.Tc.Errors.fst"
let expected_function_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t -> (let _112_177 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _112_177)))

# 134 "FStar.Tc.Errors.fst"
let expected_poly_typ : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f t targ -> (let _112_188 = (FStar_Absyn_Print.exp_to_string f)
in (let _112_187 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _112_186 = (FStar_Tc_Normalize.typ_norm_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _112_188 _112_187 _112_186)))))

# 138 "FStar.Tc.Errors.fst"
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

# 144 "FStar.Tc.Errors.fst"
let disjunctive_pattern_vars = (fun v1 v2 -> (
# 147 "FStar.Tc.Errors.fst"
let vars = (fun v -> (let _112_195 = (FStar_All.pipe_right v (FStar_List.map (fun _33_1 -> (match (_33_1) with
| FStar_Util.Inl (a) -> begin
(FStar_Absyn_Print.strBvd a)
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Print.strBvd x)
end))))
in (FStar_All.pipe_right _112_195 (FStar_String.concat ", "))))
in (let _112_197 = (vars v1)
in (let _112_196 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _112_197 _112_196)))))

# 153 "FStar.Tc.Errors.fst"
let name_and_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _112_199 = (FStar_Absyn_Print.sli ct.FStar_Absyn_Syntax.effect_name)
in (_112_199, ct.FStar_Absyn_Syntax.result_typ))
end))

# 157 "FStar.Tc.Errors.fst"
let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (
# 160 "FStar.Tc.Errors.fst"
let _33_127 = (name_and_result c)
in (match (_33_127) with
| (f1, r1) -> begin
(
# 161 "FStar.Tc.Errors.fst"
let _33_130 = (name_and_result c')
in (match (_33_130) with
| (f2, r2) -> begin
(let _112_205 = (FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _112_204 = (FStar_Tc_Normalize.typ_norm_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _112_205 f1 _112_204 f2)))
end))
end)))

# 164 "FStar.Tc.Errors.fst"
let unexpected_non_trivial_precondition_on_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f -> (let _112_210 = (FStar_Tc_Normalize.formula_norm_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _112_210)))

# 167 "FStar.Tc.Errors.fst"
let expected_pure_expression = (fun e c -> (let _112_215 = (FStar_Absyn_Print.exp_to_string e)
in (let _112_214 = (let _112_213 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _112_213))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _112_215 _112_214))))

# 170 "FStar.Tc.Errors.fst"
let expected_ghost_expression = (fun e c -> (let _112_220 = (FStar_Absyn_Print.exp_to_string e)
in (let _112_219 = (let _112_218 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _112_218))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _112_220 _112_219))))

# 173 "FStar.Tc.Errors.fst"
let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _112_226 = (FStar_Absyn_Print.sli c1)
in (let _112_225 = (FStar_Absyn_Print.sli c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _112_226 _112_225))))

# 176 "FStar.Tc.Errors.fst"
let failed_to_prove_specification_of : FStar_Absyn_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _112_232 = (FStar_Absyn_Print.lbname_to_string l)
in (let _112_231 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _112_232 _112_231))))

# 179 "FStar.Tc.Errors.fst"
let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _33_144 -> begin
(let _112_235 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _112_235))
end))

# 184 "FStar.Tc.Errors.fst"
let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"

# 186 "FStar.Tc.Errors.fst"
let cardinality_constraint_violated = (fun l a -> (let _112_239 = (FStar_Absyn_Print.sli l)
in (let _112_238 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _112_239 _112_238))))




