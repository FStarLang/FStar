
open Prims
open FStar_Pervasives

let info_at_pos : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  ((Prims.string, FStar_Ident.lid) FStar_Util.either * FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env file row col -> (

let uu____25 = (

let uu____28 = (FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info)
in (FStar_TypeChecker_Common.id_info_at_pos uu____28 file row col))
in (match (uu____25) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(match (info.FStar_TypeChecker_Common.identifier) with
| FStar_Util.Inl (bv) -> begin
(

let uu____90 = (

let uu____101 = (

let uu____106 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____106))
in (

let uu____107 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____101), (info.FStar_TypeChecker_Common.identifier_ty), (uu____107))))
in FStar_Pervasives_Native.Some (uu____90))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____123 = (

let uu____134 = (

let uu____139 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____139))
in (

let uu____140 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____134), (info.FStar_TypeChecker_Common.identifier_ty), (uu____140))))
in FStar_Pervasives_Native.Some (uu____123))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____219 -> (match (uu____219) with
| (e, msg, r) -> begin
(match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(

let uu____241 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____241)))
end
| uu____242 -> begin
(

let r' = (

let uu____244 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____244))
in (

let uu____245 = (

let uu____246 = (FStar_Range.file_of_range r')
in (

let uu____247 = (

let uu____248 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____248))
in (Prims.op_disEquality uu____246 uu____247)))
in (match (uu____245) with
| true -> begin
(

let uu____255 = (

let uu____256 = (

let uu____257 = (

let uu____258 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____258 ")"))
in (Prims.strcat "(Also see: " uu____257))
in (Prims.strcat msg uu____256))
in (

let uu____259 = (FStar_TypeChecker_Env.get_range env)
in ((e), (uu____255), (uu____259))))
end
| uu____260 -> begin
((e), (msg), (r))
end)))
end)
end))))
in (FStar_Errors.add_errors errs1)))


let err_msg_type_strings : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (Prims.string * Prims.string) = (fun env t1 t2 -> (

let s1 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let s2 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (match ((Prims.op_Equality s1 s2)) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____292 -> ((

let uu____294 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes")
in ());
(

let uu____295 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____296 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in ((uu____295), (uu____296))));
)))
end
| uu____297 -> begin
((s1), (s2))
end))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____310 = (err_msg_type_strings env t1 t2)
in (match (uu____310) with
| (s1, s2) -> begin
(FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" s2 s1)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env m k -> (

let uu____330 = (

let uu____331 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____331))
in ((FStar_Errors.Fatal_UnexpectedSignatureForMonad), (uu____330))))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env msg t e -> (

let uu____348 = (

let uu____349 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____350 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____349 uu____350 msg)))
in ((FStar_Errors.Fatal_ExpectTermGotFunction), (uu____348))))


let unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_UnexpectedImplicitArgument), ("Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"))


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____371 = (err_msg_type_strings env t1 t2)
in (match (uu____371) with
| (s1, s2) -> begin
(

let uu____382 = (

let uu____383 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" s1 uu____383 s2))
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____382)))
end)))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (

let uu____395 = (err_msg_type_strings env t1 t2)
in (match (uu____395) with
| (s1, s2) -> begin
(FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" s1 s2)
end)))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____420 = (err_msg_type_strings env t1 t2)
in (match (uu____420) with
| (s1, s2) -> begin
(

let uu____431 = (

let uu____432 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" s1 uu____432 s2))
in ((FStar_Errors.Fatal_UnexpectedPattern), (uu____431)))
end)))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env eopt t1 t2 -> (

let uu____453 = (err_msg_type_strings env t1 t2)
in (match (uu____453) with
| (s1, s2) -> begin
(

let msg = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" s1 s2)
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____466 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1 uu____466 s2))
end)
in ((FStar_Errors.Error_TypeError), (msg)))
end)))


let occurs_check : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_PossibleInfiniteTyp), ("Possibly infinite typ (occurs check failed)"))


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env k1 k2 -> (

let uu____484 = (

let uu____485 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____486 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____485 uu____486)))
in ((FStar_Errors.Fatal_IncompatibleKinds), (uu____484))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d t t' -> (

let uu____503 = (

let uu____504 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____505 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____506 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____504 uu____505 uu____506))))
in ((FStar_Errors.Fatal_ConstsructorBuildWrongType), (uu____503))))


let constructor_fails_the_positivity_check : 'Auu____511 . 'Auu____511  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d l -> (

let uu____528 = (

let uu____529 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____530 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____529 uu____530)))
in ((FStar_Errors.Fatal_ConstructorFailedCheck), (uu____528))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____538 = (

let uu____539 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____539))
in ((FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl), (uu____538))))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t x -> (

let uu____553 = (

let uu____554 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____555 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____554 uu____555)))
in ((FStar_Errors.Fatal_InferredTypeCauseVarEscape), (uu____553))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t -> (

let uu____566 = (

let uu____567 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____567))
in ((FStar_Errors.Fatal_FunctionTypeExpected), (uu____566))))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f t targ -> (

let uu____584 = (

let uu____585 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____586 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____587 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____585 uu____586 uu____587))))
in ((FStar_Errors.Fatal_PolyTypeExpected), (uu____584))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____596 = (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)
in ((FStar_Errors.Fatal_NonLinearPatternVars), (uu____596)))))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____623 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____623 (FStar_String.concat ", "))))
in (

let uu____632 = (

let uu____633 = (vars v1)
in (

let uu____634 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____633 uu____634)))
in ((FStar_Errors.Fatal_DisjuctivePatternVarsMismatch), (uu____632)))))


let name_and_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____655) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____667) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____679 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____679), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation : 'Auu____687 . FStar_TypeChecker_Env.env  ->  'Auu____687  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____716 = (name_and_result c)
in (match (uu____716) with
| (f1, r1) -> begin
(

let uu____733 = (name_and_result c')
in (match (uu____733) with
| (f2, r2) -> begin
(

let uu____750 = (err_msg_type_strings env r1 r2)
in (match (uu____750) with
| (s1, s2) -> begin
(

let uu____761 = (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" s1 f1 s2 f2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____761)))
end))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f -> (

let uu____772 = (

let uu____773 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____773))
in ((FStar_Errors.Fatal_UnExpectedPreCondition), (uu____772))))


let expected_pure_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____788 = (

let uu____789 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____790 = (

let uu____791 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____791))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____789 uu____790)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____788))))


let expected_ghost_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____820 = (

let uu____821 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____822 = (

let uu____823 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____823))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____821 uu____822)))
in ((FStar_Errors.Fatal_ExpectedGhostExpression), (uu____820))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Errors.raw_error * Prims.string) = (fun c1 c2 -> (

let uu____848 = (

let uu____849 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____850 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____849 uu____850)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____848))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun l lbls -> (

let uu____865 = (

let uu____866 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____867 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____866 uu____867)))
in ((FStar_Errors.Error_TypeCheckerFailToProve), (uu____865))))


let failed_to_prove_specification : Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun lbls -> (

let msg = (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____882 -> begin
(

let uu____885 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____885))
end)
in ((FStar_Errors.Error_TypeCheckerFailToProve), (msg))))


let top_level_effect : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Warning_TopLevelEffect), ("Top-level let-bindings must be total; this term may have effects"))


let cardinality_constraint_violated : FStar_Ident.lid  ->  FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Errors.raw_error * Prims.string) = (fun l a -> (

let uu____906 = (

let uu____907 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____908 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____907 uu____908)))
in ((FStar_Errors.Fatal_CardinalityConstraintViolated), (uu____906))))




