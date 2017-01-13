
open Prims

let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _147_10 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _147_9 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _147_10 _147_9))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let add_errors : FStar_Tc_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _46_10 -> (match (_46_10) with
| (msg, r) -> begin
(

let r = if (r = FStar_Absyn_Syntax.dummyRange) then begin
(FStar_Tc_Env.get_range env)
end else begin
r
end
in ((msg), (r)))
end))))
in (FStar_Errors.add_errors errs)))


let unexpected_signature_for_monad : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env m k -> (let _147_22 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.FStar_Ident.str _147_22)))


let expected_a_term_of_type_t_got_a_function : FStar_Tc_Env.env  ->  Prims.string  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string = (fun env msg t e -> (let _147_32 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_31 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _147_32 _147_31 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _147_43 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _147_42 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_41 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _147_43 _147_42 _147_41)))))


let expected_function_with_parameter_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _147_55 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _147_54 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _147_55 _147_54))))


let expected_pattern_of_type : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t1 e t2 -> (let _147_66 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _147_65 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_64 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _147_66 _147_65 _147_64)))))


let basic_type_error : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _147_76 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _147_75 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _147_76 _147_75)))
end
| Some (e) -> begin
(let _147_79 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _147_78 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_77 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _147_79 _147_78 _147_77))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 k2 -> (let _147_87 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _147_86 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _147_87 _147_86))))


let constructor_builds_the_wrong_type : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env d t t' -> (let _147_98 = (FStar_Absyn_Print.exp_to_string d)
in (let _147_97 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_96 = (FStar_Tc_Normalize.typ_norm_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _147_98 _147_97 _147_96)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _147_103 = (FStar_Absyn_Print.exp_to_string d)
in (let _147_102 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _147_103 _147_102))))


let inline_type_annotation_and_val_decl : FStar_Ident.lident  ->  Prims.string = (fun l -> (let _147_106 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _147_106)))


let inferred_type_causes_variable_to_escape = (fun env t x -> (let _147_111 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_110 = (FStar_Absyn_Print.strBvd x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _147_111 _147_110))))


let expected_typ_of_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env k1 t k2 -> (let _147_122 = (FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _147_121 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_120 = (FStar_Tc_Normalize.kind_norm_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _147_122 _147_121 _147_120)))))


let expected_tcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _147_130 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_129 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _147_130 _147_129))))


let expected_dcon_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.knd  ->  Prims.string = (fun env t k -> (let _147_138 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_137 = (FStar_Tc_Normalize.kind_norm_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _147_138 _147_137))))


let expected_function_typ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env t -> (let _147_143 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _147_143)))


let expected_poly_typ : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f t targ -> (let _147_154 = (FStar_Absyn_Print.exp_to_string f)
in (let _147_153 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _147_152 = (FStar_Tc_Normalize.typ_norm_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _147_154 _147_153 _147_152)))))


let nonlinear_pattern_variable = (fun x -> (

let m = (match (x) with
| FStar_Util.Inl (x) -> begin
(FStar_Absyn_Print.strBvd x)
end
| FStar_Util.Inr (a) -> begin
(FStar_Absyn_Print.strBvd a)
end)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars = (fun v1 v2 -> (

let vars = (fun v -> (let _147_161 = (FStar_All.pipe_right v (FStar_List.map (fun _46_1 -> (match (_46_1) with
| FStar_Util.Inl (a) -> begin
(FStar_Absyn_Print.strBvd a)
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Print.strBvd x)
end))))
in (FStar_All.pipe_right _147_161 (FStar_String.concat ", "))))
in (let _147_163 = (vars v1)
in (let _147_162 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _147_163 _147_162)))))


let name_and_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(("Tot"), (t))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _147_165 = (FStar_Absyn_Print.sli ct.FStar_Absyn_Syntax.effect_name)
in ((_147_165), (ct.FStar_Absyn_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let _46_94 = (name_and_result c)
in (match (_46_94) with
| (f1, r1) -> begin
(

let _46_97 = (name_and_result c')
in (match (_46_97) with
| (f2, r2) -> begin
(let _147_171 = (FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _147_170 = (FStar_Tc_Normalize.typ_norm_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _147_171 f1 _147_170 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.string = (fun env f -> (let _147_176 = (FStar_Tc_Normalize.formula_norm_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _147_176)))


let expected_pure_expression = (fun e c -> (let _147_181 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_180 = (let _147_179 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _147_179))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _147_181 _147_180))))


let expected_ghost_expression = (fun e c -> (let _147_186 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_185 = (let _147_184 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _147_184))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _147_186 _147_185))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _147_192 = (FStar_Absyn_Print.sli c1)
in (let _147_191 = (FStar_Absyn_Print.sli c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _147_192 _147_191))))


let failed_to_prove_specification_of : FStar_Absyn_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _147_198 = (FStar_Absyn_Print.lbname_to_string l)
in (let _147_197 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _147_198 _147_197))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _46_111 -> begin
(let _147_201 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _147_201))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _147_205 = (FStar_Absyn_Print.sli l)
in (let _147_204 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _147_205 _147_204))))




