
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

let uu____102 = (

let uu____113 = (

let uu____118 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____118))
in (

let uu____119 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____113), (info.FStar_TypeChecker_Common.identifier_ty), (uu____119))))
in FStar_Pervasives_Native.Some (uu____102))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____135 = (

let uu____146 = (

let uu____151 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____151))
in (

let uu____152 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____146), (info.FStar_TypeChecker_Common.identifier_ty), (uu____152))))
in FStar_Pervasives_Native.Some (uu____135))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list  ->  unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____235 -> (match (uu____235) with
| (e, msg, r) -> begin
(match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
(

let uu____257 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____257)))
end
| uu____258 -> begin
(

let r' = (

let uu____260 = (FStar_Range.use_range r)
in (FStar_Range.set_def_range r uu____260))
in (

let uu____261 = (

let uu____262 = (FStar_Range.file_of_range r')
in (

let uu____263 = (

let uu____264 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____264))
in (Prims.op_disEquality uu____262 uu____263)))
in (match (uu____261) with
| true -> begin
(

let uu____271 = (

let uu____272 = (

let uu____273 = (

let uu____274 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____274 ")"))
in (Prims.strcat "(Also see: " uu____273))
in (Prims.strcat msg uu____272))
in (

let uu____275 = (FStar_TypeChecker_Env.get_range env)
in ((e), (uu____271), (uu____275))))
end
| uu____276 -> begin
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
(FStar_Options.with_saved_options (fun uu____314 -> ((

let uu____316 = (FStar_Options.set_options FStar_Options.Set "--print_full_names --print_universes")
in ());
(

let uu____317 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____318 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in ((uu____317), (uu____318))));
)))
end
| uu____319 -> begin
((s1), (s2))
end))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____340 = (err_msg_type_strings env t1 t2)
in (match (uu____340) with
| (s1, s2) -> begin
(FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" s2 s1)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env m k -> (

let uu____366 = (

let uu____367 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____367))
in ((FStar_Errors.Fatal_UnexpectedSignatureForMonad), (uu____366))))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env msg t e -> (

let uu____392 = (

let uu____393 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____394 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____393 uu____394 msg)))
in ((FStar_Errors.Fatal_ExpectTermGotFunction), (uu____392))))


let unexpected_implicit_argument : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_UnexpectedImplicitArgument), ("Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"))


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____423 = (err_msg_type_strings env t1 t2)
in (match (uu____423) with
| (s1, s2) -> begin
(

let uu____434 = (

let uu____435 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" s1 uu____435 s2))
in ((FStar_Errors.Fatal_UnexpectedExpressionType), (uu____434)))
end)))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t1 e t2 -> (

let uu____460 = (err_msg_type_strings env t1 t2)
in (match (uu____460) with
| (s1, s2) -> begin
(

let uu____471 = (

let uu____472 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" s1 uu____472 s2))
in ((FStar_Errors.Fatal_UnexpectedPattern), (uu____471)))
end)))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env eopt t1 t2 -> (

let uu____501 = (err_msg_type_strings env t1 t2)
in (match (uu____501) with
| (s1, s2) -> begin
(

let msg = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" s1 s2)
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____514 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" s1 uu____514 s2))
end)
in ((FStar_Errors.Error_TypeError), (msg)))
end)))


let occurs_check : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Fatal_PossibleInfiniteTyp), ("Possibly infinite typ (occurs check failed)"))


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env k1 k2 -> (

let uu____538 = (

let uu____539 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____540 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____539 uu____540)))
in ((FStar_Errors.Fatal_IncompatibleKinds), (uu____538))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d t t' -> (

let uu____565 = (

let uu____566 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____567 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____568 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____566 uu____567 uu____568))))
in ((FStar_Errors.Fatal_ConstsructorBuildWrongType), (uu____565))))


let constructor_fails_the_positivity_check : 'Auu____577 . 'Auu____577  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun env d l -> (

let uu____597 = (

let uu____598 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____599 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____598 uu____599)))
in ((FStar_Errors.Fatal_ConstructorFailedCheck), (uu____597))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  (FStar_Errors.raw_error * Prims.string) = (fun l -> (

let uu____609 = (

let uu____610 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____610))
in ((FStar_Errors.Fatal_DuplicateTypeAnnotationAndValDecl), (uu____609))))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t x -> (

let uu____630 = (

let uu____631 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____632 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____631 uu____632)))
in ((FStar_Errors.Fatal_InferredTypeCauseVarEscape), (uu____630))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env t -> (

let uu____647 = (

let uu____648 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____648))
in ((FStar_Errors.Fatal_FunctionTypeExpected), (uu____647))))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f t targ -> (

let uu____673 = (

let uu____674 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____675 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____676 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____674 uu____675 uu____676))))
in ((FStar_Errors.Fatal_PolyTypeExpected), (uu____673))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  (FStar_Errors.raw_error * Prims.string) = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____687 = (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)
in ((FStar_Errors.Fatal_NonLinearPatternVars), (uu____687)))))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____720 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____720 (FStar_String.concat ", "))))
in (

let uu____729 = (

let uu____730 = (vars v1)
in (

let uu____731 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____730 uu____731)))
in ((FStar_Errors.Fatal_DisjuctivePatternVarsMismatch), (uu____729)))))


let name_and_result : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (Prims.string * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____754) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____766) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____778 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____778), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation : 'Auu____791 . FStar_TypeChecker_Env.env  ->  'Auu____791  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun env e c c' -> (

let uu____824 = (name_and_result c)
in (match (uu____824) with
| (f1, r1) -> begin
(

let uu____841 = (name_and_result c')
in (match (uu____841) with
| (f2, r2) -> begin
(

let uu____858 = (err_msg_type_strings env r1 r2)
in (match (uu____858) with
| (s1, s2) -> begin
(

let uu____869 = (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" s1 f1 s2 f2)
in ((FStar_Errors.Fatal_ComputedTypeNotMatchAnnotation), (uu____869)))
end))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Errors.raw_error * Prims.string) = (fun env f -> (

let uu____884 = (

let uu____885 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____885))
in ((FStar_Errors.Fatal_UnExpectedPreCondition), (uu____884))))


let expected_pure_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____904 = (

let uu____905 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____906 = (

let uu____907 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____907))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____905 uu____906)))
in ((FStar_Errors.Fatal_ExpectedPureExpression), (uu____904))))


let expected_ghost_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  (FStar_Errors.raw_error * Prims.string) = (fun e c -> (

let uu____940 = (

let uu____941 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____942 = (

let uu____943 = (name_and_result c)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____943))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____941 uu____942)))
in ((FStar_Errors.Fatal_ExpectedGhostExpression), (uu____940))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Errors.raw_error * Prims.string) = (fun c1 c2 -> (

let uu____972 = (

let uu____973 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____974 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____973 uu____974)))
in ((FStar_Errors.Fatal_UnexpectedEffect), (uu____972))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun l lbls -> (

let uu____993 = (

let uu____994 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____995 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____994 uu____995)))
in ((FStar_Errors.Error_TypeCheckerFailToProve), (uu____993))))


let failed_to_prove_specification : Prims.string Prims.list  ->  (FStar_Errors.raw_error * Prims.string) = (fun lbls -> (

let msg = (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____1012 -> begin
(

let uu____1015 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____1015))
end)
in ((FStar_Errors.Error_TypeCheckerFailToProve), (msg))))


let top_level_effect : (FStar_Errors.raw_error * Prims.string) = ((FStar_Errors.Warning_TopLevelEffect), ("Top-level let-bindings must be total; this term may have effects"))


let cardinality_constraint_violated : FStar_Ident.lid  ->  FStar_Syntax_Syntax.bv FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Errors.raw_error * Prims.string) = (fun l a -> (

let uu____1040 = (

let uu____1041 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____1042 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____1041 uu____1042)))
in ((FStar_Errors.Fatal_CardinalityConstraintViolated), (uu____1040))))




