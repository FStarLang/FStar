
open Prims

let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _57_5 -> (match (_57_5) with
| (msg, r) -> begin
if (r = FStar_Range.dummyRange) then begin
(let _158_6 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_158_6)))
end else begin
(

let r' = (

let _57_6 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = _57_6.FStar_Range.use_range})
in if ((FStar_Range.file_of_range r') <> (let _158_7 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range _158_7))) then begin
(let _158_12 = (let _158_10 = (let _158_9 = (let _158_8 = (FStar_Range.string_of_use_range r)
in (Prims.strcat _158_8 ")"))
in (Prims.strcat "(Also see: " _158_9))
in (Prims.strcat msg _158_10))
in (let _158_11 = (FStar_TypeChecker_Env.get_range env)
in ((_158_12), (_158_11))))
end else begin
((msg), (r))
end)
end
end))))
in (FStar_Errors.add_errors errs)))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _158_22 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _158_21 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _158_22 _158_21))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _158_29 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str _158_29)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _158_39 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_38 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" _158_39 _158_38 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _158_50 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _158_49 = (FStar_Syntax_Print.term_to_string e)
in (let _158_48 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" _158_50 _158_49 _158_48)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _158_62 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _158_61 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _158_62 _158_61))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _158_73 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _158_72 = (FStar_Syntax_Print.term_to_string e)
in (let _158_71 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" _158_73 _158_72 _158_71)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _158_83 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _158_82 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" _158_83 _158_82)))
end
| Some (e) -> begin
(let _158_86 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _158_85 = (FStar_Syntax_Print.term_to_string e)
in (let _158_84 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _158_86 _158_85 _158_84))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _158_94 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _158_93 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _158_94 _158_93))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _158_105 = (FStar_Syntax_Print.term_to_string d)
in (let _158_104 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_103 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _158_105 _158_104 _158_103)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _158_110 = (FStar_Syntax_Print.term_to_string d)
in (let _158_109 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _158_110 _158_109))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _158_113 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _158_113)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _158_121 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_120 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _158_121 _158_120))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _158_132 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _158_131 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_130 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" _158_132 _158_131 _158_130)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _158_140 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_139 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _158_140 _158_139))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _158_148 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_147 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _158_148 _158_147))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _158_153 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" _158_153)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _158_164 = (FStar_Syntax_Print.term_to_string f)
in (let _158_163 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _158_162 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _158_164 _158_163 _158_162)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (let _158_173 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _158_173 (FStar_String.concat ", "))))
in (let _158_175 = (vars v1)
in (let _158_174 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _158_175 _158_174)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _57_78) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, _57_83) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _158_177 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((_158_177), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let _57_94 = (name_and_result c)
in (match (_57_94) with
| (f1, r1) -> begin
(

let _57_97 = (name_and_result c')
in (match (_57_97) with
| (f2, r2) -> begin
(let _158_183 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _158_182 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _158_183 f1 _158_182 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _158_188 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _158_188)))


let expected_pure_expression = (fun e c -> (let _158_193 = (FStar_Syntax_Print.term_to_string e)
in (let _158_192 = (let _158_191 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _158_191))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" _158_193 _158_192))))


let expected_ghost_expression = (fun e c -> (let _158_198 = (FStar_Syntax_Print.term_to_string e)
in (let _158_197 = (let _158_196 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _158_196))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" _158_198 _158_197))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _158_204 = (FStar_Syntax_Print.lid_to_string c1)
in (let _158_203 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" _158_204 _158_203))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _158_210 = (FStar_Syntax_Print.lbname_to_string l)
in (let _158_209 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _158_210 _158_209))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _57_111 -> begin
(let _158_213 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _158_213))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _158_217 = (FStar_Syntax_Print.lid_to_string l)
in (let _158_216 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _158_217 _158_216))))




