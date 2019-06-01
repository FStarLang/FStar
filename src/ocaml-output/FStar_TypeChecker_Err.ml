
open Prims
open FStar_Pervasives

let info_at_pos : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  ((Prims.string, FStar_Ident.lid) FStar_Util.either * FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env file row col -> (

let uu____39 = (

let uu____42 = (FStar_ST.op_Bang env.FStar_TypeChecker_Env.identifier_info)
in (FStar_TypeChecker_Common.id_info_at_pos uu____42 file row col))
in (match (uu____39) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(match (info.FStar_TypeChecker_Common.identifier) with
| FStar_Util.Inl (bv) -> begin
(

let uu____101 = (

let uu____113 = (

let uu____119 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____119))
in (

let uu____122 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____113), (info.FStar_TypeChecker_Common.identifier_ty), (uu____122))))
in FStar_Pervasives_Native.Some (uu____101))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____140 = (

let uu____152 = (

let uu____158 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____158))
in (

let uu____160 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____152), (info.FStar_TypeChecker_Common.identifier_ty), (uu____160))))
in FStar_Pervasives_Native.Some (uu____140))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list  ->  unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____253 -> (match (uu____253) with
| (e, msg, r) -> begin
(match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(

let uu____281 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____281)))
end
| uu____283 -> begin
(

let r' = (

let uu____286 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____286))
in (

let uu____287 = (

let uu____289 = (FStar_Range.file_of_range r')
in (

let uu____291 = (

let uu____293 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____293))
in (Prims.op_disEquality uu____289 uu____291)))
in (match (uu____287) with
| true -> begin
(

let uu____303 = (

let uu____305 = (

let uu____307 = (

let uu____309 = (FStar_Range.string_of_use_range r)
in (

let uu____311 = (

let uu____313 = (

let uu____315 = (

let uu____317 = (FStar_Range.use_range r)
in (

let uu____318 = (FStar_Range.def_range r)
in (Prims.op_disEquality uu____317 uu____318)))
in (match (uu____315) with
| true -> begin
(

let uu____321 = (

let uu____323 = (FStar_Range.string_of_def_range r)
in (Prims.op_Hat uu____323 ")"))
in (Prims.op_Hat "(Other related locations: " uu____321))
end
| uu____327 -> begin
""
end))
in (Prims.op_Hat ")" uu____313))
in (Prims.op_Hat uu____309 uu____311)))
in (Prims.op_Hat " (Also see: " uu____307))
in (Prims.op_Hat msg uu____305))
in (

let uu____332 = (FStar_TypeChecker_Env.get_range env)
in ((e), (uu____303), (uu____332))))
end
| uu____334 -> begin
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
(FStar_Options.with_saved_options (fun uu____387 -> ((

let uu____389 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes")
in ());
(

let uu____391 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____393 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in ((uu____391), (uu____393))));
)))
end
| uu____397 -> begin
((s1), (s2))
end))))


let err_msg_comp_strings : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (Prims.string * Prims.string) = (fun env c1 c2 -> (

let s1 = (FStar_TypeChecker_Normalize.comp_to_string env c1)
in (

let s2 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in (match ((Prims.op_Equality s1 s2)) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____451 -> ((

let uu____453 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes --print_effect_args")
in ());
(

let uu____455 = (FStar_TypeChecker_Normalize.comp_to_string env c1)
in (

let uu____457 = (FStar_TypeChecker_Normalize.comp_to_string env c2)
in ((uu____455), (uu____457))));
)))
end
| uu____461 -> begin
((s1), (s2))
end))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____490 = (err_msg_type_strings env t1 t2)
in (match (uu____490) with
| (s1, s2) -> begin
(FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" s2 s1)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env m k -> (

let uu____532 = (

let uu____534 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____534))
in ((FStar_Errors.Fatal_UnexpectedSignatureForMonad), (uu____532))))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env msg t e -> (

let uu____566 = (

let uu____568 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____570 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____568 uu____570 msg)))
in ((FStar_Errors.Fatal_ExpectTermGotFunction), (uu____566))))


let unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_UnexpectedImplicitArgument), ("Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"))


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____608 = (err_msg_type_strings env t1 t2)
in (match (uu____608) with
| (s1, s2) -> begin
(

let uu____626 = (

let uu____628 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" s1 uu____628 s2))
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____626)))
end)))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____658 = (err_msg_type_strings env t1 t2)
in (match (uu____658) with
| (s1, s2) -> begin
(

let uu____676 = (

let uu____678 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" s1 uu____678 s2))
in ((FStar_Errors.Fatal_UnexpectedPattern), (uu____676)))
end)))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env eopt t1 t2 -> (

let uu____712 = (err_msg_type_strings env t1 t2)
in (match (uu____712) with
| (s1, s2) -> begin
(

let msg = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" s1 s2)
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____735 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1 uu____735 s2))
end)
in ((FStar_Errors.Error_TypeError), (msg)))
end)))


let occurs_check : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_PossibleInfiniteTyp), ("Possibly infinite typ (occurs check failed)"))


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env k1 k2 -> (

let uu____768 = (

let uu____770 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____772 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____770 uu____772)))
in ((FStar_Errors.Fatal_IncompatibleKinds), (uu____768))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d t t' -> (

let uu____802 = (

let uu____804 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____806 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____808 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____804 uu____806 uu____808))))
in ((FStar_Errors.Fatal_ConstsructorBuildWrongType), (uu____802))))


let constructor_fails_the_positivity_check : 'Auu____821 . 'Auu____821  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d l -> (

let uu____842 = (

let uu____844 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____846 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____844 uu____846)))
in ((FStar_Errors.Fatal_ConstructorFailedCheck), (uu____842))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____861 = (

let uu____863 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____863))
in ((FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl), (uu____861))))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t x -> (

let uu____888 = (

let uu____890 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____892 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____890 uu____892)))
in ((FStar_Errors.Fatal_InferredTypeCauseVarEscape), (uu____888))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t -> (

let uu____912 = (

let uu____914 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____914))
in ((FStar_Errors.Fatal_FunctionTypeExpected), (uu____912))))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f t targ -> (

let uu____944 = (

let uu____946 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____948 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____950 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____946 uu____948 uu____950))))
in ((FStar_Errors.Fatal_PolyTypeExpected), (uu____944))))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____989 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____989 (FStar_String.concat ", "))))
in (

let uu____1004 = (

let uu____1006 = (vars v1)
in (

let uu____1008 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____1006 uu____1008)))
in ((FStar_Errors.Fatal_DisjuctivePatternVarsMismatch), (uu____1004)))))


let name_and_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1037) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1051) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____1065 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____1065), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation : 'Auu____1081 . FStar_TypeChecker_Env.env  ->  'Auu____1081  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____1115 = (name_and_result c)
in (match (uu____1115) with
| (f1, r1) -> begin
(

let uu____1136 = (name_and_result c')
in (match (uu____1136) with
| (f2, r2) -> begin
(

let uu____1157 = (err_msg_type_strings env r1 r2)
in (match (uu____1157) with
| (s1, s2) -> begin
(

let uu____1175 = (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" s1 f1 s2 f2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____1175)))
end))
end))
end)))


let computed_computation_type_does_not_match_annotation_eq : 'Auu____1190 . FStar_TypeChecker_Env.env  ->  'Auu____1190  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____1216 = (err_msg_comp_strings env c c')
in (match (uu____1216) with
| (s1, s2) -> begin
(

let uu____1234 = (FStar_Util.format2 "Computed type \"%s\" does not match annotated type \"%s\", and no subtyping was allowed" s1 s2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____1234)))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f -> (

let uu____1254 = (

let uu____1256 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____1256))
in ((FStar_Errors.Fatal_UnExpectedPreCondition), (uu____1254))))


let expected_pure_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____1280 = (

let uu____1282 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____1284 = (

let uu____1286 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1286))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____1282 uu____1284)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____1280))))


let expected_ghost_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____1327 = (

let uu____1329 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____1331 = (

let uu____1333 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1333))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____1329 uu____1331)))
in ((FStar_Errors.Fatal_ExpectedGhostExpression), (uu____1327))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Errors.raw_error * Prims.string) = (fun c1 c2 -> (

let uu____1370 = (

let uu____1372 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____1374 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____1372 uu____1374)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____1370))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun l lbls -> (

let uu____1400 = (

let uu____1402 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____1404 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____1402 uu____1404)))
in ((FStar_Errors.Error_TypeCheckerFailToProve), (uu____1400))))


let failed_to_prove_specification : Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun lbls -> (

let msg = (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____1435 -> begin
(

let uu____1439 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____1439))
end)
in ((FStar_Errors.Error_TypeCheckerFailToProve), (msg))))


let top_level_effect : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Warning_TopLevelEffect), ("Top-level let-bindings must be total; this term may have effects"))


let cardinality_constraint_violated : FStar_Ident.lid  ->  FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Errors.raw_error * Prims.string) = (fun l a -> (

let uu____1476 = (

let uu____1478 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____1480 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____1478 uu____1480)))
in ((FStar_Errors.Fatal_CardinalityConstraintViolated), (uu____1476))))




