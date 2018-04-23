
open Prims
open FStar_Pervasives

let info_at_pos : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  ((Prims.string, FStar_Ident.lid) FStar_Util.either * FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env file row col -> (

let uu____33 = (

let uu____36 = (FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info)
in (FStar_TypeChecker_Common.id_info_at_pos uu____36 file row col))
in (match (uu____33) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(match (info.FStar_TypeChecker_Common.identifier) with
| FStar_Util.Inl (bv) -> begin
(

let uu____96 = (

let uu____107 = (

let uu____112 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____112))
in (

let uu____113 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____107), (info.FStar_TypeChecker_Common.identifier_ty), (uu____113))))
in FStar_Pervasives_Native.Some (uu____96))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____129 = (

let uu____140 = (

let uu____145 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____145))
in (

let uu____146 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____140), (info.FStar_TypeChecker_Common.identifier_ty), (uu____146))))
in FStar_Pervasives_Native.Some (uu____129))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list  ->  unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____229 -> (match (uu____229) with
| (e, msg, r) -> begin
(match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(

let uu____251 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____251)))
end
| uu____252 -> begin
(

let r' = (

let uu____254 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____254))
in (

let uu____255 = (

let uu____256 = (FStar_Range.file_of_range r')
in (

let uu____257 = (

let uu____258 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____258))
in (Prims.op_disEquality uu____256 uu____257)))
in (match (uu____255) with
| true -> begin
(

let uu____265 = (

let uu____266 = (

let uu____267 = (

let uu____268 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____268 ")"))
in (Prims.strcat "(Also see: " uu____267))
in (Prims.strcat msg uu____266))
in (

let uu____269 = (FStar_TypeChecker_Env.get_range env)
in ((e), (uu____265), (uu____269))))
end
| uu____270 -> begin
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
(FStar_Options.with_saved_options (fun uu____308 -> ((

let uu____310 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes")
in ());
(

let uu____311 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____312 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in ((uu____311), (uu____312))));
)))
end
| uu____313 -> begin
((s1), (s2))
end))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____334 = (err_msg_type_strings env t1 t2)
in (match (uu____334) with
| (s1, s2) -> begin
(FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" s2 s1)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env m k -> (

let uu____360 = (

let uu____361 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____361))
in ((FStar_Errors.Fatal_UnexpectedSignatureForMonad), (uu____360))))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env msg t e -> (

let uu____386 = (

let uu____387 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____388 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____387 uu____388 msg)))
in ((FStar_Errors.Fatal_ExpectTermGotFunction), (uu____386))))


let unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_UnexpectedImplicitArgument), ("Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"))


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____417 = (err_msg_type_strings env t1 t2)
in (match (uu____417) with
| (s1, s2) -> begin
(

let uu____428 = (

let uu____429 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" s1 uu____429 s2))
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____428)))
end)))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (

let uu____448 = (err_msg_type_strings env t1 t2)
in (match (uu____448) with
| (s1, s2) -> begin
(FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" s1 s2)
end)))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____482 = (err_msg_type_strings env t1 t2)
in (match (uu____482) with
| (s1, s2) -> begin
(

let uu____493 = (

let uu____494 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" s1 uu____494 s2))
in ((FStar_Errors.Fatal_UnexpectedPattern), (uu____493)))
end)))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env eopt t1 t2 -> (

let uu____523 = (err_msg_type_strings env t1 t2)
in (match (uu____523) with
| (s1, s2) -> begin
(

let msg = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" s1 s2)
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____536 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1 uu____536 s2))
end)
in ((FStar_Errors.Error_TypeError), (msg)))
end)))


let occurs_check : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_PossibleInfiniteTyp), ("Possibly infinite typ (occurs check failed)"))


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env k1 k2 -> (

let uu____560 = (

let uu____561 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____562 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____561 uu____562)))
in ((FStar_Errors.Fatal_IncompatibleKinds), (uu____560))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d t t' -> (

let uu____587 = (

let uu____588 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____589 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____590 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____588 uu____589 uu____590))))
in ((FStar_Errors.Fatal_ConstsructorBuildWrongType), (uu____587))))


let constructor_fails_the_positivity_check : 'Auu____599 . 'Auu____599  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d l -> (

let uu____619 = (

let uu____620 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____621 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____620 uu____621)))
in ((FStar_Errors.Fatal_ConstructorFailedCheck), (uu____619))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____631 = (

let uu____632 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____632))
in ((FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl), (uu____631))))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t x -> (

let uu____652 = (

let uu____653 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____654 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____653 uu____654)))
in ((FStar_Errors.Fatal_InferredTypeCauseVarEscape), (uu____652))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t -> (

let uu____669 = (

let uu____670 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____670))
in ((FStar_Errors.Fatal_FunctionTypeExpected), (uu____669))))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f t targ -> (

let uu____695 = (

let uu____696 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____697 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____698 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____696 uu____697 uu____698))))
in ((FStar_Errors.Fatal_PolyTypeExpected), (uu____695))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____709 = (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)
in ((FStar_Errors.Fatal_NonLinearPatternVars), (uu____709)))))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____742 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____742 (FStar_String.concat ", "))))
in (

let uu____751 = (

let uu____752 = (vars v1)
in (

let uu____753 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____752 uu____753)))
in ((FStar_Errors.Fatal_DisjuctivePatternVarsMismatch), (uu____751)))))


let name_and_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____776) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____788) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____800 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____800), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation : 'Auu____813 . FStar_TypeChecker_Env.env  ->  'Auu____813  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____846 = (name_and_result c)
in (match (uu____846) with
| (f1, r1) -> begin
(

let uu____863 = (name_and_result c')
in (match (uu____863) with
| (f2, r2) -> begin
(

let uu____880 = (err_msg_type_strings env r1 r2)
in (match (uu____880) with
| (s1, s2) -> begin
(

let uu____891 = (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" s1 f1 s2 f2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____891)))
end))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f -> (

let uu____906 = (

let uu____907 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____907))
in ((FStar_Errors.Fatal_UnExpectedPreCondition), (uu____906))))


let expected_pure_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____926 = (

let uu____927 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____928 = (

let uu____929 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____929))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____927 uu____928)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____926))))


let expected_ghost_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____962 = (

let uu____963 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____964 = (

let uu____965 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____965))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____963 uu____964)))
in ((FStar_Errors.Fatal_ExpectedGhostExpression), (uu____962))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Errors.raw_error * Prims.string) = (fun c1 c2 -> (

let uu____994 = (

let uu____995 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____996 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____995 uu____996)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____994))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun l lbls -> (

let uu____1015 = (

let uu____1016 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1017 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____1016 uu____1017)))
in ((FStar_Errors.Error_TypeCheckerFailToProve), (uu____1015))))


let failed_to_prove_specification : Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun lbls -> (

let msg = (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____1034 -> begin
(

let uu____1037 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____1037))
end)
in ((FStar_Errors.Error_TypeCheckerFailToProve), (msg))))


let top_level_effect : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Warning_TopLevelEffect), ("Top-level let-bindings must be total; this term may have effects"))


let cardinality_constraint_violated : FStar_Ident.lid  ->  FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Errors.raw_error * Prims.string) = (fun l a -> (

let uu____1062 = (

let uu____1063 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____1064 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____1063 uu____1064)))
in ((FStar_Errors.Fatal_CardinalityConstraintViolated), (uu____1062))))




