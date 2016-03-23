
open Prims
# 32 "FStar.TypeChecker.Errors.fst"
let exhaustiveness_check : Prims.string = "Patterns are incomplete"

# 33 "FStar.TypeChecker.Errors.fst"
let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _146_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _146_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _146_10 _146_9))))

# 36 "FStar.TypeChecker.Errors.fst"
let ill_kinded_type : Prims.string = "Ill-kinded type"

# 37 "FStar.TypeChecker.Errors.fst"
let totality_check : Prims.string = "This term may not terminate"

# 39 "FStar.TypeChecker.Errors.fst"
let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _146_16 = (let _146_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _146_15 msg))
in (FStar_Util.print_string _146_16))
end else begin
()
end)

# 43 "FStar.TypeChecker.Errors.fst"
let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _146_22 = (let _146_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _146_21 msg))
in (FStar_Util.print_string _146_22)))

# 46 "FStar.TypeChecker.Errors.fst"
let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 47 "FStar.TypeChecker.Errors.fst"
let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 48 "FStar.TypeChecker.Errors.fst"
let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (
# 49 "FStar.TypeChecker.Errors.fst"
let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _61_13 -> (match (_61_13) with
| (msg, r) -> begin
(
# 49 "FStar.TypeChecker.Errors.fst"
let r = if (r = FStar_Range.dummyRange) then begin
(FStar_TypeChecker_Env.get_range env)
end else begin
r
end
in (r, msg))
end))))
in (
# 50 "FStar.TypeChecker.Errors.fst"
let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _61_17 -> (match (()) with
| () -> begin
(
# 52 "FStar.TypeChecker.Errors.fst"
let _61_18 = (let _146_30 = (let _146_29 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _146_29))
in (FStar_ST.op_Colon_Equals verification_errs _146_30))
in (let _146_31 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _146_31)))
end))))))

# 54 "FStar.TypeChecker.Errors.fst"
let report_all : Prims.unit  ->  Prims.int = (fun _61_20 -> (match (()) with
| () -> begin
(
# 55 "FStar.TypeChecker.Errors.fst"
let all_errs = (FStar_Util.atomically (fun _61_21 -> (match (()) with
| () -> begin
(
# 55 "FStar.TypeChecker.Errors.fst"
let x = (FStar_ST.read verification_errs)
in (
# 55 "FStar.TypeChecker.Errors.fst"
let _61_23 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (
# 56 "FStar.TypeChecker.Errors.fst"
let all_errs = (FStar_List.sortWith (fun _61_29 _61_33 -> (match ((_61_29, _61_33)) with
| ((r1, _61_28), (r2, _61_32)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (
# 57 "FStar.TypeChecker.Errors.fst"
let _61_38 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _61_37 -> (match (_61_37) with
| (r, msg) -> begin
(let _146_38 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _146_38 msg))
end))))
in (FStar_List.length all_errs))))
end))

# 61 "FStar.TypeChecker.Errors.fst"
let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (
# 62 "FStar.TypeChecker.Errors.fst"
let _61_42 = (FStar_Util.incr num_errs)
in (let _146_44 = (let _146_43 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _146_43 msg))
in (FStar_Util.print_string _146_44))))

# 64 "FStar.TypeChecker.Errors.fst"
let get_err_count : Prims.unit  ->  Prims.int = (fun _61_44 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))

# 66 "FStar.TypeChecker.Errors.fst"
let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _146_53 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => WP a => Effect);\ngot %s" m.FStar_Ident.str _146_53)))

# 70 "FStar.TypeChecker.Errors.fst"
let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _146_63 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_62 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _146_63 _146_62 msg))))

# 74 "FStar.TypeChecker.Errors.fst"
let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

# 77 "FStar.TypeChecker.Errors.fst"
let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _146_74 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_73 = (FStar_Syntax_Print.term_to_string e)
in (let _146_72 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _146_74 _146_73 _146_72)))))

# 81 "FStar.TypeChecker.Errors.fst"
let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _146_86 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_85 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _146_86 _146_85))))

# 85 "FStar.TypeChecker.Errors.fst"
let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _146_97 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_96 = (FStar_Syntax_Print.term_to_string e)
in (let _146_95 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _146_97 _146_96 _146_95)))))

# 89 "FStar.TypeChecker.Errors.fst"
let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _146_107 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_106 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _146_107 _146_106)))
end
| Some (e) -> begin
(let _146_110 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_109 = (FStar_Syntax_Print.term_to_string e)
in (let _146_108 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _146_110 _146_109 _146_108))))
end))

# 96 "FStar.TypeChecker.Errors.fst"
let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"

# 99 "FStar.TypeChecker.Errors.fst"
let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"

# 102 "FStar.TypeChecker.Errors.fst"
let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _146_118 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _146_117 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _146_118 _146_117))))

# 106 "FStar.TypeChecker.Errors.fst"
let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _146_129 = (FStar_Syntax_Print.term_to_string d)
in (let _146_128 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_127 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _146_129 _146_128 _146_127)))))

# 110 "FStar.TypeChecker.Errors.fst"
let constructor_fails_the_positivity_check = (fun env d l -> (let _146_134 = (FStar_Syntax_Print.term_to_string d)
in (let _146_133 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _146_134 _146_133))))

# 114 "FStar.TypeChecker.Errors.fst"
let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _146_137 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _146_137)))

# 118 "FStar.TypeChecker.Errors.fst"
let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _146_145 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_144 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _146_145 _146_144))))

# 122 "FStar.TypeChecker.Errors.fst"
let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _146_156 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _146_155 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_154 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _146_156 _146_155 _146_154)))))

# 126 "FStar.TypeChecker.Errors.fst"
let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _146_164 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_163 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _146_164 _146_163))))

# 130 "FStar.TypeChecker.Errors.fst"
let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _146_172 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_171 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _146_172 _146_171))))

# 134 "FStar.TypeChecker.Errors.fst"
let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _146_177 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _146_177)))

# 138 "FStar.TypeChecker.Errors.fst"
let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _146_188 = (FStar_Syntax_Print.term_to_string f)
in (let _146_187 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_186 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _146_188 _146_187 _146_186)))))

# 142 "FStar.TypeChecker.Errors.fst"
let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (
# 143 "FStar.TypeChecker.Errors.fst"
let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))

# 146 "FStar.TypeChecker.Errors.fst"
let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (
# 147 "FStar.TypeChecker.Errors.fst"
let vars = (fun v -> (let _146_197 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _146_197 (FStar_String.concat ", "))))
in (let _146_199 = (vars v1)
in (let _146_198 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _146_199 _146_198)))))

# 153 "FStar.TypeChecker.Errors.fst"
let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
("Tot", t)
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
("GTot", t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _146_201 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in (_146_201, ct.FStar_Syntax_Syntax.result_typ))
end))

# 158 "FStar.TypeChecker.Errors.fst"
let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (
# 159 "FStar.TypeChecker.Errors.fst"
let _61_119 = (name_and_result c)
in (match (_61_119) with
| (f1, r1) -> begin
(
# 160 "FStar.TypeChecker.Errors.fst"
let _61_122 = (name_and_result c')
in (match (_61_122) with
| (f2, r2) -> begin
(let _146_207 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _146_206 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _146_207 f1 _146_206 f2)))
end))
end)))

# 165 "FStar.TypeChecker.Errors.fst"
let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _146_212 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _146_212)))

# 168 "FStar.TypeChecker.Errors.fst"
let expected_pure_expression = (fun e c -> (let _146_217 = (FStar_Syntax_Print.term_to_string e)
in (let _146_216 = (let _146_215 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _146_215))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _146_217 _146_216))))

# 171 "FStar.TypeChecker.Errors.fst"
let expected_ghost_expression = (fun e c -> (let _146_222 = (FStar_Syntax_Print.term_to_string e)
in (let _146_221 = (let _146_220 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _146_220))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _146_222 _146_221))))

# 174 "FStar.TypeChecker.Errors.fst"
let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _146_228 = (FStar_Syntax_Print.lid_to_string c1)
in (let _146_227 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _146_228 _146_227))))

# 177 "FStar.TypeChecker.Errors.fst"
let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _146_234 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_233 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _146_234 _146_233))))

# 180 "FStar.TypeChecker.Errors.fst"
let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _61_136 -> begin
(let _146_237 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _146_237))
end))

# 185 "FStar.TypeChecker.Errors.fst"
let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"

# 187 "FStar.TypeChecker.Errors.fst"
let cardinality_constraint_violated = (fun l a -> (let _146_241 = (FStar_Syntax_Print.lid_to_string l)
in (let _146_240 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _146_241 _146_240))))




