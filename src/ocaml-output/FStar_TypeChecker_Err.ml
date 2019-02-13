
open Prims
open FStar_Pervasives

let info_at_pos : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  ((Prims.string, FStar_Ident.lid) FStar_Util.either * FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env file row col -> (

let uu____40 = (

let uu____43 = (FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info)
in (FStar_TypeChecker_Common.id_info_at_pos uu____43 file row col))
in (match (uu____40) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(match (info.FStar_TypeChecker_Common.identifier) with
| FStar_Util.Inl (bv) -> begin
(

let uu____102 = (

let uu____114 = (

let uu____120 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____120))
in (

let uu____123 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____114), (info.FStar_TypeChecker_Common.identifier_ty), (uu____123))))
in FStar_Pervasives_Native.Some (uu____102))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____141 = (

let uu____153 = (

let uu____159 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____159))
in (

let uu____161 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____153), (info.FStar_TypeChecker_Common.identifier_ty), (uu____161))))
in FStar_Pervasives_Native.Some (uu____141))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list  ->  unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____254 -> (match (uu____254) with
| (e, msg, r) -> begin
(match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(

let uu____282 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____282)))
end
| uu____284 -> begin
(

let r' = (

let uu____287 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____287))
in (

let uu____288 = (

let uu____290 = (FStar_Range.file_of_range r')
in (

let uu____292 = (

let uu____294 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____294))
in (Prims.op_disEquality uu____290 uu____292)))
in (match (uu____288) with
| true -> begin
(

let uu____304 = (

let uu____306 = (

let uu____308 = (

let uu____310 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____310 ")"))
in (Prims.strcat " (Also see: " uu____308))
in (Prims.strcat msg uu____306))
in (

let uu____314 = (FStar_TypeChecker_Env.get_range env)
in ((e), (uu____304), (uu____314))))
end
| uu____316 -> begin
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
(FStar_Options.with_saved_options (fun uu____369 -> ((

let uu____371 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes")
in ());
(

let uu____373 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____375 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in ((uu____373), (uu____375))));
)))
end
| uu____379 -> begin
((s1), (s2))
end))))


let err_msg_comp_strings : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (Prims.string * Prims.string) = (fun env c1 c2 -> (

let s1 = (FStar_TypeChecker_Normalize.comp_to_string env c1)
in (

let s2 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (match ((Prims.op_Equality s1 s2)) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____433 -> ((

let uu____435 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes --print_effect_args")
in ());
(

let uu____437 = (FStar_TypeChecker_Normalize.comp_to_string env c1)
in (

let uu____439 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in ((uu____437), (uu____439))));
)))
end
| uu____443 -> begin
((s1), (s2))
end))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____472 = (err_msg_type_strings env t1 t2)
in (match (uu____472) with
| (s1, s2) -> begin
(FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" s2 s1)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env m k -> (

let uu____514 = (

let uu____516 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____516))
in ((FStar_Errors.Fatal_UnexpectedSignatureForMonad), (uu____514))))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env msg t e -> (

let uu____548 = (

let uu____550 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____552 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____550 uu____552 msg)))
in ((FStar_Errors.Fatal_ExpectTermGotFunction), (uu____548))))


let unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_UnexpectedImplicitArgument), ("Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"))


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____590 = (err_msg_type_strings env t1 t2)
in (match (uu____590) with
| (s1, s2) -> begin
(

let uu____608 = (

let uu____610 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" s1 uu____610 s2))
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____608)))
end)))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____640 = (err_msg_type_strings env t1 t2)
in (match (uu____640) with
| (s1, s2) -> begin
(

let uu____658 = (

let uu____660 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" s1 uu____660 s2))
in ((FStar_Errors.Fatal_UnexpectedPattern), (uu____658)))
end)))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env eopt t1 t2 -> (

let uu____694 = (err_msg_type_strings env t1 t2)
in (match (uu____694) with
| (s1, s2) -> begin
(

let msg = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" s1 s2)
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____717 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1 uu____717 s2))
end)
in ((FStar_Errors.Error_TypeError), (msg)))
end)))


let occurs_check : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_PossibleInfiniteTyp), ("Possibly infinite typ (occurs check failed)"))


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env k1 k2 -> (

let uu____750 = (

let uu____752 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____754 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____752 uu____754)))
in ((FStar_Errors.Fatal_IncompatibleKinds), (uu____750))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d t t' -> (

let uu____784 = (

let uu____786 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____788 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____790 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____786 uu____788 uu____790))))
in ((FStar_Errors.Fatal_ConstsructorBuildWrongType), (uu____784))))


let constructor_fails_the_positivity_check : 'Auu____803 . 'Auu____803  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d l -> (

let uu____824 = (

let uu____826 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____828 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____826 uu____828)))
in ((FStar_Errors.Fatal_ConstructorFailedCheck), (uu____824))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____843 = (

let uu____845 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____845))
in ((FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl), (uu____843))))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t x -> (

let uu____870 = (

let uu____872 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____874 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____872 uu____874)))
in ((FStar_Errors.Fatal_InferredTypeCauseVarEscape), (uu____870))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t -> (

let uu____894 = (

let uu____896 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____896))
in ((FStar_Errors.Fatal_FunctionTypeExpected), (uu____894))))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f t targ -> (

let uu____926 = (

let uu____928 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____930 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____932 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____928 uu____930 uu____932))))
in ((FStar_Errors.Fatal_PolyTypeExpected), (uu____926))))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____971 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____971 (FStar_String.concat ", "))))
in (

let uu____986 = (

let uu____988 = (vars v1)
in (

let uu____990 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____988 uu____990)))
in ((FStar_Errors.Fatal_DisjuctivePatternVarsMismatch), (uu____986)))))


let name_and_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1019) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1033) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1047 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____1047), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation : 'Auu____1063 . FStar_TypeChecker_Env.env  ->  'Auu____1063  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____1097 = (name_and_result c)
in (match (uu____1097) with
| (f1, r1) -> begin
(

let uu____1118 = (name_and_result c')
in (match (uu____1118) with
| (f2, r2) -> begin
(

let uu____1139 = (err_msg_type_strings env r1 r2)
in (match (uu____1139) with
| (s1, s2) -> begin
(

let uu____1157 = (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" s1 f1 s2 f2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____1157)))
end))
end))
end)))


let computed_computation_type_does_not_match_annotation_eq : 'Auu____1172 . FStar_TypeChecker_Env.env  ->  'Auu____1172  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____1198 = (err_msg_comp_strings env c c')
in (match (uu____1198) with
| (s1, s2) -> begin
(

let uu____1216 = (FStar_Util.format2 "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed" s1 s2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____1216)))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f -> (

let uu____1236 = (

let uu____1238 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____1238))
in ((FStar_Errors.Fatal_UnExpectedPreCondition), (uu____1236))))


let expected_pure_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____1262 = (

let uu____1264 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____1266 = (

let uu____1268 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1268))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____1264 uu____1266)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____1262))))


let expected_ghost_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____1309 = (

let uu____1311 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____1313 = (

let uu____1315 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1315))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____1311 uu____1313)))
in ((FStar_Errors.Fatal_ExpectedGhostExpression), (uu____1309))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Errors.raw_error * Prims.string) = (fun c1 c2 -> (

let uu____1352 = (

let uu____1354 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____1356 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____1354 uu____1356)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____1352))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun l lbls -> (

let uu____1382 = (

let uu____1384 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1386 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____1384 uu____1386)))
in ((FStar_Errors.Error_TypeCheckerFailToProve), (uu____1382))))


let failed_to_prove_specification : Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun lbls -> (

let msg = (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____1417 -> begin
(

let uu____1421 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____1421))
end)
in ((FStar_Errors.Error_TypeCheckerFailToProve), (msg))))


let top_level_effect : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Warning_TopLevelEffect), ("Top-level let-bindings must be total; this term may have effects"))


let cardinality_constraint_violated : FStar_Ident.lid  ->  FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Errors.raw_error * Prims.string) = (fun l a -> (

let uu____1458 = (

let uu____1460 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____1462 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____1460 uu____1462)))
in ((FStar_Errors.Fatal_CardinalityConstraintViolated), (uu____1458))))




