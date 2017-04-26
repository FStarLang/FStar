
open Prims

let info_at_pos = (fun env file row col -> (

let uu____29 = (FStar_TypeChecker_Common.info_at_pos file row col)
in (match (uu____29) with
| None -> begin
None
end
| Some (info) -> begin
(match (info.FStar_TypeChecker_Common.identifier) with
| FStar_Util.Inl (bv) -> begin
(

let uu____50 = (

let uu____56 = (

let uu____59 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____59))
in (

let uu____60 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____56), (info.FStar_TypeChecker_Common.identifier_ty), (uu____60))))
in Some (uu____50))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____69 = (

let uu____75 = (

let uu____78 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____78))
in (

let uu____79 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____75), (info.FStar_TypeChecker_Common.identifier_ty), (uu____79))))
in Some (uu____69))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____113 -> (match (uu____113) with
| (msg, r) -> begin
(match ((r = FStar_Range.dummyRange)) with
| true -> begin
(

let uu____122 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____122)))
end
| uu____123 -> begin
(

let r' = (

let uu___200_125 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___200_125.FStar_Range.use_range})
in (

let uu____126 = (

let uu____127 = (FStar_Range.file_of_range r')
in (

let uu____128 = (

let uu____129 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____129))
in (uu____127 <> uu____128)))
in (match (uu____126) with
| true -> begin
(

let uu____132 = (

let uu____133 = (

let uu____134 = (

let uu____135 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____135 ")"))
in (Prims.strcat "(Also see: " uu____134))
in (Prims.strcat msg uu____133))
in (

let uu____136 = (FStar_TypeChecker_Env.get_range env)
in ((uu____132), (uu____136))))
end
| uu____137 -> begin
((msg), (r))
end)))
end)
end))))
in (FStar_Errors.add_errors errs1)))


let possibly_verbose_message : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (Prims.string * Prims.string * Prims.string) = (fun env t1 t2 -> (

let s1 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let s2 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (

let extra = (match ((s1 = s2)) with
| true -> begin
(

let uu____153 = (FStar_Options.set_options FStar_Options.Set "--prn --print_universes")
in (

let s11 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let s21 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "\nMore precisely: expected type:\n%s\ngot:\n%s\n" s11 s21))))
end
| uu____156 -> begin
""
end)
in ((s1), (s2), (extra))))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____169 = (possibly_verbose_message env t2 t1)
in (match (uu____169) with
| (s2, s1, extra) -> begin
(FStar_Util.format3 "Subtyping check failed; expected type %s; got type %s%s" s2 s1 extra)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (

let uu____185 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____185)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (

let uu____198 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____199 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____198 uu____199 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (

let uu____212 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____213 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____214 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" uu____212 uu____213 uu____214)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (

let uu____226 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____227 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" uu____226 uu____227))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (

let uu____240 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____241 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____242 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" uu____240 uu____241 uu____242)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (

let uu____257 = (possibly_verbose_message env t1 t2)
in (match (uu____257) with
| (s1, s2, extra) -> begin
(match (eopt) with
| None -> begin
(FStar_Util.format3 "Expected type \"%s\"; got type \"%s\"%s" s1 s2 extra)
end
| Some (e) -> begin
(

let uu____265 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Expected type \"%s\"; but \"%s\" has type \"%s\"%s" s1 uu____265 s2 extra))
end)
end)))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (

let uu____275 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____276 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____275 uu____276))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (

let uu____289 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____290 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____291 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____289 uu____290 uu____291)))))


let constructor_fails_the_positivity_check = (fun env d l -> (

let uu____309 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____310 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____309 uu____310))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (

let uu____314 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____314)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (

let uu____324 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____325 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____324 uu____325))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (

let uu____338 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____339 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____340 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" uu____338 uu____339 uu____340)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (

let uu____350 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____351 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" uu____350 uu____351))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (

let uu____361 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____362 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" uu____361 uu____362))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let uu____369 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____369)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (

let uu____382 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____383 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____384 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____382 uu____383 uu____384)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____405 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____405 (FStar_String.concat ", "))))
in (

let uu____410 = (vars v1)
in (

let uu____411 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____410 uu____411)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____428) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____438) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____448 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____448), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let uu____485 = (name_and_result c)
in (match (uu____485) with
| (f1, r1) -> begin
(

let uu____496 = (name_and_result c')
in (match (uu____496) with
| (f2, r2) -> begin
(

let uu____507 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (

let uu____508 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" uu____507 f1 uu____508 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (

let uu____515 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____515)))


let expected_pure_expression = (fun e c -> (

let uu____532 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____533 = (

let uu____534 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst uu____534))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____532 uu____533))))


let expected_ghost_expression = (fun e c -> (

let uu____561 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____562 = (

let uu____563 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst uu____563))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____561 uu____562))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (

let uu____580 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____581 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____580 uu____581))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (

let uu____590 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____591 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____590 uu____591))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____598 -> begin
(

let uu____600 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____600))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (

let uu____618 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____619 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____618 uu____619))))




