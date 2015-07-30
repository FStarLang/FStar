
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun ( env ) ( t1 ) ( t2 ) ( x ) -> (let _65_12602 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _65_12601 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (Support.Microsoft.FStar.Util.format2 "Subtyping check failed; expected type %s; got type %s" _65_12602 _65_12601))))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun ( r ) ( msg ) -> (let _65_12608 = (let _65_12607 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Diagnostic): %s\n" _65_12607 msg))
in (Support.Microsoft.FStar.Util.print_string _65_12608)))

let warn = (fun ( r ) ( msg ) -> (let _65_12614 = (let _65_12613 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Warning): %s\n" _65_12613 msg))
in (Support.Microsoft.FStar.Util.print_string _65_12614)))

let num_errs = (Support.Microsoft.FStar.Util.mk_ref 0)

let verification_errs = (Support.Microsoft.FStar.Util.mk_ref [])

let add_errors = (fun ( env ) ( errs ) -> (let errs = (Support.Prims.pipe_right errs (Support.List.map (fun ( _31_14 ) -> (match (_31_14) with
| (msg, r) -> begin
(let r = (match ((r = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
(Microsoft_FStar_Tc_Env.get_range env)
end
| false -> begin
r
end)
in (r, msg))
end))))
in (let n_errs = (Support.List.length errs)
in (Support.Microsoft.FStar.Util.atomically (fun ( _31_18 ) -> (match (()) with
| () -> begin
(let _31_19 = (let _65_12622 = (let _65_12621 = (Support.ST.read verification_errs)
in (Support.List.append errs _65_12621))
in (Support.ST.op_Colon_Equals verification_errs _65_12622))
in (let _65_12623 = ((Support.ST.read num_errs) + n_errs)
in (Support.ST.op_Colon_Equals num_errs _65_12623)))
end))))))

let report_all = (fun ( _31_21 ) -> (match (()) with
| () -> begin
(let all_errs = (Support.Microsoft.FStar.Util.atomically (fun ( _31_22 ) -> (match (()) with
| () -> begin
(let x = (Support.ST.read verification_errs)
in (let _31_24 = (Support.ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (Support.List.sortWith (fun ( _31_30 ) ( _31_34 ) -> (match ((_31_30, _31_34)) with
| ((r1, _), (r2, _)) -> begin
(Support.Microsoft.FStar.Range.compare r1 r2)
end)) all_errs)
in (let _31_39 = (Support.Prims.pipe_right all_errs (Support.List.iter (fun ( _31_38 ) -> (match (_31_38) with
| (r, msg) -> begin
(let _65_12630 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.fprint2 "%s: %s\n" _65_12630 msg))
end))))
in (Support.List.length all_errs))))
end))

let report = (fun ( r ) ( msg ) -> (let _31_43 = (Support.Microsoft.FStar.Util.incr num_errs)
in (let _65_12636 = (let _65_12635 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _65_12635 msg))
in (Support.Microsoft.FStar.Util.print_string _65_12636))))

let get_err_count = (fun ( _31_45 ) -> (match (()) with
| () -> begin
(Support.ST.read num_errs)
end))

let unexpected_signature_for_monad = (fun ( env ) ( m ) ( k ) -> (let _65_12645 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.Microsoft_FStar_Absyn_Syntax.str _65_12645)))

let expected_a_term_of_type_t_got_a_function = (fun ( env ) ( msg ) ( t ) ( e ) -> (let _65_12655 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12654 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _65_12655 _65_12654 msg))))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun ( env ) ( t1 ) ( e ) ( t2 ) -> (let _65_12666 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_12665 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _65_12664 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _65_12666 _65_12665 _65_12664)))))

let expected_function_with_parameter_of_type = (fun ( env ) ( t1 ) ( t2 ) -> (let _65_12678 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_12677 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _65_12678 _65_12677))))

let expected_pattern_of_type = (fun ( env ) ( t1 ) ( e ) ( t2 ) -> (let _65_12689 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_12688 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _65_12687 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _65_12689 _65_12688 _65_12687)))))

let basic_type_error = (fun ( env ) ( eopt ) ( t1 ) ( t2 ) -> (match (eopt) with
| None -> begin
(let _65_12699 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_12698 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _65_12699 _65_12698)))
end
| Some (e) -> begin
(let _65_12702 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _65_12701 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _65_12700 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _65_12702 _65_12701 _65_12700))))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun ( env ) ( k1 ) ( k2 ) -> (let _65_12710 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _65_12709 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _65_12710 _65_12709))))

let constructor_builds_the_wrong_type = (fun ( env ) ( d ) ( t ) ( t' ) -> (let _65_12721 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _65_12720 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12719 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t')
in (Support.Microsoft.FStar.Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _65_12721 _65_12720 _65_12719)))))

let constructor_fails_the_positivity_check = (fun ( env ) ( d ) ( l ) -> (let _65_12726 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _65_12725 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _65_12726 _65_12725))))

let inline_type_annotation_and_val_decl = (fun ( l ) -> (let _65_12729 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _65_12729)))

let inferred_type_causes_variable_to_escape = (fun ( env ) ( t ) ( x ) -> (let _65_12734 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12733 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (Support.Microsoft.FStar.Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _65_12734 _65_12733))))

let expected_typ_of_kind = (fun ( env ) ( k1 ) ( t ) ( k2 ) -> (let _65_12745 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _65_12744 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12743 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _65_12745 _65_12744 _65_12743)))))

let expected_tcon_kind = (fun ( env ) ( t ) ( k ) -> (let _65_12753 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12752 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _65_12753 _65_12752))))

let expected_dcon_kind = (fun ( env ) ( t ) ( k ) -> (let _65_12761 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12760 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _65_12761 _65_12760))))

let expected_function_typ = (fun ( env ) ( t ) -> (let _65_12766 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _65_12766)))

let expected_poly_typ = (fun ( env ) ( f ) ( t ) ( targ ) -> (let _65_12777 = (Microsoft_FStar_Absyn_Print.exp_to_string f)
in (let _65_12776 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _65_12775 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env targ)
in (Support.Microsoft.FStar.Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _65_12777 _65_12776 _65_12775)))))

let nonlinear_pattern_variable = (fun ( x ) -> (let m = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end)
in (Support.Microsoft.FStar.Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun ( v1 ) ( v2 ) -> (let vars = (fun ( v ) -> (let _65_12784 = (Support.Prims.pipe_right v (Support.List.map (fun ( _31_1 ) -> (match (_31_1) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end))))
in (Support.Prims.pipe_right _65_12784 (Support.String.concat ", "))))
in (let _65_12786 = (vars v1)
in (let _65_12785 = (vars v2)
in (Support.Microsoft.FStar.Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _65_12786 _65_12785)))))

let name_and_result = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _65_12788 = (Microsoft_FStar_Absyn_Print.sli ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (_65_12788, ct.Microsoft_FStar_Absyn_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun ( env ) ( e ) ( c ) ( c' ) -> (let _31_127 = (name_and_result c)
in (match (_31_127) with
| (f1, r1) -> begin
(let _31_130 = (name_and_result c')
in (match (_31_130) with
| (f2, r2) -> begin
(let _65_12794 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _65_12793 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r2)
in (Support.Microsoft.FStar.Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _65_12794 f1 _65_12793 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun ( env ) ( f ) -> (let _65_12799 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
in (Support.Microsoft.FStar.Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _65_12799)))

let expected_pure_expression = (fun ( e ) ( c ) -> (let _65_12804 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _65_12803 = (let _65_12802 = (name_and_result c)
in (Support.Prims.pipe_left Support.Prims.fst _65_12802))
in (Support.Microsoft.FStar.Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _65_12804 _65_12803))))

let expected_ghost_expression = (fun ( e ) ( c ) -> (let _65_12809 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _65_12808 = (let _65_12807 = (name_and_result c)
in (Support.Prims.pipe_left Support.Prims.fst _65_12807))
in (Support.Microsoft.FStar.Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _65_12809 _65_12808))))

let expected_effect_1_got_effect_2 = (fun ( c1 ) ( c2 ) -> (let _65_12815 = (Microsoft_FStar_Absyn_Print.sli c1)
in (let _65_12814 = (Microsoft_FStar_Absyn_Print.sli c2)
in (Support.Microsoft.FStar.Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _65_12815 _65_12814))))

let failed_to_prove_specification_of = (fun ( l ) ( lbls ) -> (let _65_12821 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _65_12820 = (Support.Prims.pipe_right lbls (Support.String.concat ", "))
in (Support.Microsoft.FStar.Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _65_12821 _65_12820))))

let failed_to_prove_specification = (fun ( lbls ) -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _ -> begin
(let _65_12824 = (Support.Prims.pipe_right lbls (Support.String.concat "\n\t"))
in (Support.Microsoft.FStar.Util.format1 "The following problems were found:\n\t%s" _65_12824))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"




