
open Prims

let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun uu____27 -> (match (uu____27) with
| (msg, r) -> begin
(match ((r = FStar_Range.dummyRange)) with
| true -> begin
(let _0_507 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_0_507)))
end
| uu____36 -> begin
(

let r' = (

let uu___183_38 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = uu___183_38.FStar_Range.use_range})
in (

let uu____39 = (let _0_509 = (FStar_Range.file_of_range r')
in (let _0_508 = (FStar_Range.file_of_range (FStar_TypeChecker_Env.get_range env))
in (_0_509 <> _0_508)))
in (match (uu____39) with
| true -> begin
(let _0_514 = (let _0_512 = (let _0_511 = (let _0_510 = (FStar_Range.string_of_use_range r)
in (Prims.strcat _0_510 ")"))
in (Prims.strcat "(Also see: " _0_511))
in (Prims.strcat msg _0_512))
in (let _0_513 = (FStar_TypeChecker_Env.get_range env)
in ((_0_514), (_0_513))))
end
| uu____42 -> begin
((msg), (r))
end)))
end)
end))))
in (FStar_Errors.add_errors errs)))


let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _0_516 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _0_515 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _0_516 _0_515))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _0_517 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str _0_517)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _0_519 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_518 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" _0_519 _0_518 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _0_522 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_521 = (FStar_Syntax_Print.term_to_string e)
in (let _0_520 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" _0_522 _0_521 _0_520)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _0_524 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_523 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _0_524 _0_523))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _0_527 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_526 = (FStar_Syntax_Print.term_to_string e)
in (let _0_525 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" _0_527 _0_526 _0_525)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _0_529 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_528 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" _0_529 _0_528)))
end
| Some (e) -> begin
(let _0_532 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _0_531 = (FStar_Syntax_Print.term_to_string e)
in (let _0_530 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _0_532 _0_531 _0_530))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _0_534 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _0_533 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _0_534 _0_533))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _0_537 = (FStar_Syntax_Print.term_to_string d)
in (let _0_536 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_535 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _0_537 _0_536 _0_535)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _0_539 = (FStar_Syntax_Print.term_to_string d)
in (let _0_538 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _0_539 _0_538))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _0_540 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _0_540)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _0_542 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_541 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _0_542 _0_541))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _0_545 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _0_544 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_543 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" _0_545 _0_544 _0_543)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _0_547 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_546 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _0_547 _0_546))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _0_549 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_548 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _0_549 _0_548))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _0_550 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" _0_550)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _0_553 = (FStar_Syntax_Print.term_to_string f)
in (let _0_552 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _0_551 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _0_553 _0_552 _0_551)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (let _0_554 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _0_554 (FStar_String.concat ", "))))
in (let _0_556 = (vars v1)
in (let _0_555 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _0_556 _0_555)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____263) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, uu____273) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _0_557 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((_0_557), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let uu____319 = (name_and_result c)
in (match (uu____319) with
| (f1, r1) -> begin
(

let uu____330 = (name_and_result c')
in (match (uu____330) with
| (f2, r2) -> begin
(let _0_559 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _0_558 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _0_559 f1 _0_558 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _0_560 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _0_560)))


let expected_pure_expression = (fun e c -> (let _0_563 = (FStar_Syntax_Print.term_to_string e)
in (let _0_562 = (let _0_561 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _0_561))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" _0_563 _0_562))))


let expected_ghost_expression = (fun e c -> (let _0_566 = (FStar_Syntax_Print.term_to_string e)
in (let _0_565 = (let _0_564 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _0_564))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" _0_566 _0_565))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _0_568 = (FStar_Syntax_Print.lid_to_string c1)
in (let _0_567 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" _0_568 _0_567))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _0_570 = (FStar_Syntax_Print.lbname_to_string l)
in (let _0_569 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _0_570 _0_569))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| uu____411 -> begin
(let _0_571 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _0_571))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _0_573 = (FStar_Syntax_Print.lid_to_string l)
in (let _0_572 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _0_573 _0_572))))




