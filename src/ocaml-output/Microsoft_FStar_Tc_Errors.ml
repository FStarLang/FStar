
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun env t1 t2 x -> (Support.Microsoft.FStar.Util.format2 "Subtyping check failed; expected type %s; got type %s" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun r msg -> (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "%s (Diagnostic): %s\n" (Support.Microsoft.FStar.Range.string_of_range r) msg)))

let warn = (fun r msg -> (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "%s (Warning): %s\n" (Support.Microsoft.FStar.Range.string_of_range r) msg)))

let num_errs = (Support.Microsoft.FStar.Util.mk_ref 0)

let verification_errs = (Support.Microsoft.FStar.Util.mk_ref [])

let add_errors = (fun env errs -> (let errs = ((Support.List.map (fun _147711 -> (match (_147711) with
| (msg, r) -> begin
(let r = if (r = Microsoft_FStar_Absyn_Syntax.dummyRange) then begin
(Microsoft_FStar_Tc_Env.get_range env)
end else begin
r
end
in (r, msg))
end))) errs)
in (let n_errs = (Support.List.length errs)
in (Support.Microsoft.FStar.Util.atomically (fun _147715 -> (match (_147715) with
| () -> begin
(let _147716 = (verification_errs := (Support.List.append errs (! (verification_errs))))
in (num_errs := ((! (num_errs)) + n_errs)))
end))))))

let report_all = (fun _147718 -> (match (_147718) with
| () -> begin
(let all_errs = (Support.Microsoft.FStar.Util.atomically (fun _147719 -> (match (_147719) with
| () -> begin
(let x = (! (verification_errs))
in (let _147721 = (verification_errs := [])
in x))
end)))
in (let all_errs = (Support.List.sortWith (fun _147727 _147731 -> (match ((_147727, _147731)) with
| ((r1, _), (r2, _)) -> begin
(Support.Microsoft.FStar.Range.compare r1 r2)
end)) all_errs)
in (let _147736 = ((Support.List.iter (fun _147735 -> (match (_147735) with
| (r, msg) -> begin
(Support.Microsoft.FStar.Util.fprint2 "%s: %s\n" (Support.Microsoft.FStar.Range.string_of_range r) msg)
end))) all_errs)
in (Support.List.length all_errs))))
end))

let report = (fun r msg -> (let _147740 = (Support.Microsoft.FStar.Util.incr num_errs)
in (Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "%s: %s\n" (Support.Microsoft.FStar.Range.string_of_range r) msg))))

let get_err_count = (fun _147742 -> (match (_147742) with
| () -> begin
(! (num_errs))
end))

let unexpected_signature_for_monad = (fun env m k -> (Support.Microsoft.FStar.Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)))

let expected_a_term_of_type_t_got_a_function = (fun env msg t e -> (Support.Microsoft.FStar.Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Absyn_Print.exp_to_string e) msg))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun env t1 e t2 -> (Support.Microsoft.FStar.Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Absyn_Print.exp_to_string e) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)))

let expected_function_with_parameter_of_type = (fun env t1 t2 -> (Support.Microsoft.FStar.Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)))

let expected_pattern_of_type = (fun env t1 e t2 -> (Support.Microsoft.FStar.Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Absyn_Print.exp_to_string e) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)))

let basic_type_error = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(Support.Microsoft.FStar.Util.format2 "Expected type \"%s\";\ngot type \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2))
end
| Some (e) -> begin
(Support.Microsoft.FStar.Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1) (Microsoft_FStar_Absyn_Print.exp_to_string e) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun env k1 k2 -> (Support.Microsoft.FStar.Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1) (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)))

let constructor_builds_the_wrong_type = (fun env d t t' -> (Support.Microsoft.FStar.Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" (Microsoft_FStar_Absyn_Print.exp_to_string d) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t')))

let constructor_fails_the_positivity_check = (fun env d l -> (Support.Microsoft.FStar.Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type occurs \"%s\" occurs to the left of a pure function type" (Microsoft_FStar_Absyn_Print.exp_to_string d) (Microsoft_FStar_Absyn_Print.sli l)))

let inline_type_annotation_and_val_decl = (fun l -> (Support.Microsoft.FStar.Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" (Microsoft_FStar_Absyn_Print.sli l)))

let inferred_type_causes_variable_to_escape = (fun env t x -> (Support.Microsoft.FStar.Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Absyn_Print.strBvd x)))

let expected_typ_of_kind = (fun env k1 t k2 -> (Support.Microsoft.FStar.Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)))

let expected_tcon_kind = (fun env t k -> (Support.Microsoft.FStar.Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)))

let expected_dcon_kind = (fun env t k -> (Support.Microsoft.FStar.Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)))

let expected_function_typ = (fun env t -> (Support.Microsoft.FStar.Util.format1 "Expected a function;\ngot an expression of type \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)))

let expected_poly_typ = (fun env f t targ -> (Support.Microsoft.FStar.Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" (Microsoft_FStar_Absyn_Print.exp_to_string f) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t) (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env targ)))

let nonlinear_pattern_variable = (fun x -> (let m = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end)
in (Support.Microsoft.FStar.Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun v1 v2 -> (let vars = (fun v -> ((Support.String.concat ", ") ((Support.List.map (fun _147698 -> (match (_147698) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end))) v)))
in (Support.Microsoft.FStar.Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" (vars v1) (vars v2))))

let name_and_result = (fun c -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
((Microsoft_FStar_Absyn_Print.sli ct.Microsoft_FStar_Absyn_Syntax.effect_name), ct.Microsoft_FStar_Absyn_Syntax.result_typ)
end))

let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (let _147824 = (name_and_result c)
in (match (_147824) with
| (f1, r1) -> begin
(let _147827 = (name_and_result c')
in (match (_147827) with
| (f2, r2) -> begin
(Support.Microsoft.FStar.Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r1) f1 (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r2) f2)
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun env f -> (Support.Microsoft.FStar.Util.format1 "Term has an unexpected non-trivial pre-condition: %s" (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)))

let expected_pure_expression = (fun e c -> (Support.Microsoft.FStar.Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" (Microsoft_FStar_Absyn_Print.exp_to_string e) ((Support.Prims.fst) (name_and_result c))))

let expected_ghost_expression = (fun e c -> (Support.Microsoft.FStar.Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" (Microsoft_FStar_Absyn_Print.exp_to_string e) ((Support.Prims.fst) (name_and_result c))))

let expected_effect_1_got_effect_2 = (fun c1 c2 -> (Support.Microsoft.FStar.Util.format2 "Expected a computation with effect %s; but it has effect %s\n" (Microsoft_FStar_Absyn_Print.sli c1) (Microsoft_FStar_Absyn_Print.sli c2)))

let failed_to_prove_specification_of = (fun l lbls -> (Support.Microsoft.FStar.Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" (Microsoft_FStar_Absyn_Print.lbname_to_string l) ((Support.String.concat ", ") lbls)))

let failed_to_prove_specification = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _ -> begin
(Support.Microsoft.FStar.Util.format1 "The following problems were found:\n\t%s" ((Support.String.concat "\n\t") lbls))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"




