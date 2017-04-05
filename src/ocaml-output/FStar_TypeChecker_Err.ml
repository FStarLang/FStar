
open Prims

let format_info : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  Prims.string Prims.option  ->  Prims.string = (fun env name typ range doc1 -> (

let uu____18 = (FStar_Range.string_of_range range)
in (

let uu____19 = (FStar_TypeChecker_Normalize.term_to_string env typ)
in (

let uu____20 = (match (doc1) with
| Some (docstring) -> begin
(FStar_Util.format1 "#doc %s" docstring)
end
| None -> begin
""
end)
in (FStar_Util.format4 "(defined at %s) %s: %s%s" uu____18 name uu____19 uu____20)))))


let info_at_pos = (fun env file row col -> (

let uu____50 = (FStar_TypeChecker_Common.info_at_pos file row col)
in (match (uu____50) with
| None -> begin
None
end
| Some (info) -> begin
(match (info.FStar_TypeChecker_Common.identifier) with
| FStar_Util.Inl (bv) -> begin
(

let uu____71 = (

let uu____77 = (

let uu____80 = (FStar_Syntax_Print.nm_to_string bv)
in FStar_Util.Inl (uu____80))
in (

let uu____81 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____77), (info.FStar_TypeChecker_Common.identifier_ty), (uu____81))))
in Some (uu____71))
end
| FStar_Util.Inr (fv) -> begin
(

let uu____90 = (

let uu____96 = (

let uu____99 = (FStar_Syntax_Syntax.lid_of_fv fv)
in FStar_Util.Inr (uu____99))
in (

let uu____100 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____96), (info.FStar_TypeChecker_Common.identifier_ty), (uu____100))))
in Some (uu____90))
end)
end)))


let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs1 = (FStar_All.pipe_right errs (FStar_List.map (fun uu____134 -> (match (uu____134) with
| (msg, r) -> begin
(match ((r = FStar_Range.dummyRange)) with
| true -> begin
(

let uu____143 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____143)))
end
| uu____144 -> begin
(

let r' = (

let uu___194_146 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___194_146.FStar_Range.use_range})
in (

let uu____147 = (

let uu____148 = (FStar_Range.file_of_range r')
in (

let uu____149 = (

let uu____150 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range uu____150))
in (uu____148 <> uu____149)))
in (match (uu____147) with
| true -> begin
(

let uu____153 = (

let uu____154 = (

let uu____155 = (

let uu____156 = (FStar_Range.string_of_use_range r)
in (Prims.strcat uu____156 ")"))
in (Prims.strcat "(Also see: " uu____155))
in (Prims.strcat msg uu____154))
in (

let uu____157 = (FStar_TypeChecker_Env.get_range env)
in ((uu____153), (uu____157))))
end
| uu____158 -> begin
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

let uu____174 = (FStar_Options.set_options FStar_Options.Set "--prn --print_universes")
in (

let s11 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let s21 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "\nMore precisely: expected type:\n%s\ngot:\n%s\n" s11 s21))))
end
| uu____177 -> begin
""
end)
in ((s1), (s2), (extra))))))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (

let uu____190 = (possibly_verbose_message env t2 t1)
in (match (uu____190) with
| (s2, s1, extra) -> begin
(FStar_Util.format3 "Subtyping check failed; expected type %s; got type %s%s" s2 s1 extra)
end)))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (

let uu____206 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str uu____206)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (

let uu____219 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____220 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" uu____219 uu____220 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (

let uu____233 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____234 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____235 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" uu____233 uu____234 uu____235)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (

let uu____247 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____248 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" uu____247 uu____248))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (

let uu____261 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (

let uu____262 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____263 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" uu____261 uu____262 uu____263)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (

let uu____278 = (possibly_verbose_message env t1 t2)
in (match (uu____278) with
| (s1, s2, extra) -> begin
(match (eopt) with
| None -> begin
(FStar_Util.format3 "Expected type \"%s\"; got type \"%s\"%s" s1 s2 extra)
end
| Some (e) -> begin
(

let uu____286 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format4 "Expected type \"%s\"; but \"%s\" has type \"%s\"%s" s1 uu____286 s2 extra))
end)
end)))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (

let uu____296 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____297 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" uu____296 uu____297))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (

let uu____310 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____311 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____312 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" uu____310 uu____311 uu____312)))))


let constructor_fails_the_positivity_check = (fun env d l -> (

let uu____330 = (FStar_Syntax_Print.term_to_string d)
in (

let uu____331 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" uu____330 uu____331))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (

let uu____335 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" uu____335)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (

let uu____345 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____346 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" uu____345 uu____346))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (

let uu____359 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (

let uu____360 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____361 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" uu____359 uu____360 uu____361)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (

let uu____371 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____372 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" uu____371 uu____372))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (

let uu____382 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____383 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" uu____382 uu____383))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let uu____390 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" uu____390)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (

let uu____403 = (FStar_Syntax_Print.term_to_string f)
in (

let uu____404 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (

let uu____405 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" uu____403 uu____404 uu____405)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v3 -> (

let uu____426 = (FStar_All.pipe_right v3 (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____426 (FStar_String.concat ", "))))
in (

let uu____431 = (vars v1)
in (

let uu____432 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" uu____431 uu____432)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____449) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____459) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____469 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((uu____469), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let uu____506 = (name_and_result c)
in (match (uu____506) with
| (f1, r1) -> begin
(

let uu____517 = (name_and_result c')
in (match (uu____517) with
| (f2, r2) -> begin
(

let uu____528 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (

let uu____529 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" uu____528 f1 uu____529 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (

let uu____536 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" uu____536)))


let expected_pure_expression = (fun e c -> (

let uu____553 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____554 = (

let uu____555 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst uu____555))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" uu____553 uu____554))))


let expected_ghost_expression = (fun e c -> (

let uu____582 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____583 = (

let uu____584 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst uu____584))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" uu____582 uu____583))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (

let uu____601 = (FStar_Syntax_Print.lid_to_string c1)
in (

let uu____602 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" uu____601 uu____602))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (

let uu____611 = (FStar_Syntax_Print.lbname_to_string l)
in (

let uu____612 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" uu____611 uu____612))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____619 -> begin
(

let uu____621 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" uu____621))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (

let uu____639 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____640 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" uu____639 uu____640))))




