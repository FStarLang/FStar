
open Prims

let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun uu____27 -> (match (uu____27) with
| (msg, r) -> begin
(match ((r = FStar_Range.dummyRange)) with
| true -> begin
(

let uu____36 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____36)))
end
| uu____37 -> begin
(

let r' = (

let uu___184_39 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___184_39.FStar_Range.use_range})
in (

let uu____40 = (

let uu____41 = (FStar_Range.file_of_range r')
in (

let uu____42 = (

let uu____43 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____43))
in (uu____41 <> uu____42)))
in (match (uu____40) with
| true -> begin
(

let uu____46 = (

let uu____47 = (

let uu____48 = (

let uu____49 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____49 ")"))
in (Prims.strcat "(Also see: " uu____48))
in (Prims.strcat msg uu____47))
in (

let uu____50 = (FStar_TypeChecker_Env.get_range env)
in ((uu____46), (uu____50))))
end
| uu____51 -> begin
((msg), (r))
end)))
end)
end))))
in (FStar_Errors.add_errors errs)))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____64 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let uu____65 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" uu____64 uu____65))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (

let uu____75 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____75)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (

let uu____88 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____89 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____88 uu____89 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (

let uu____102 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____103 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____104 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" uu____102 uu____103 uu____104)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (

let uu____116 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____117 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" uu____116 uu____117))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (

let uu____130 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____131 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____132 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" uu____130 uu____131 uu____132)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(

let uu____147 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____148 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" uu____147 uu____148)))
end
| Some (e) -> begin
(

let uu____150 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____151 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____152 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" uu____150 uu____151 uu____152))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (

let uu____162 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____163 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____162 uu____163))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (

let uu____176 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____177 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____178 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____176 uu____177 uu____178)))))


let constructor_fails_the_positivity_check = (fun env d l -> (

let uu____196 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____197 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____196 uu____197))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (

let uu____201 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____201)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (

let uu____211 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____212 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____211 uu____212))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (

let uu____225 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____226 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____227 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" uu____225 uu____226 uu____227)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (

let uu____237 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____238 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" uu____237 uu____238))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (

let uu____248 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____249 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" uu____248 uu____249))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let uu____256 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____256)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (

let uu____269 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____270 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____271 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____269 uu____270 uu____271)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (

let uu____292 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____292 (FStar_String.concat ", "))))
in (

let uu____297 = (vars v1)
in (

let uu____298 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____297 uu____298)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____315) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____325) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____335 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____335), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let uu____372 = (name_and_result c)
in (match (uu____372) with
| (f1, r1) -> begin
(

let uu____383 = (name_and_result c')
in (match (uu____383) with
| (f2, r2) -> begin
(

let uu____394 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (

let uu____395 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" uu____394 f1 uu____395 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (

let uu____402 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____402)))


let expected_pure_expression = (fun e c -> (

let uu____419 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____420 = (

let uu____421 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst uu____421))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____419 uu____420))))


let expected_ghost_expression = (fun e c -> (

let uu____448 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____449 = (

let uu____450 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst uu____450))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____448 uu____449))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (

let uu____467 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____468 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____467 uu____468))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (

let uu____477 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____478 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____477 uu____478))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____485 -> begin
(

let uu____487 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____487))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (

let uu____505 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____506 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____505 uu____506))))




