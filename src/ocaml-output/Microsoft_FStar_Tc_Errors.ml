
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun ( env ) ( t1 ) ( t2 ) ( x ) -> (let _70_12757 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _70_12756 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (Support.Microsoft.FStar.Util.format2 "Subtyping check failed; expected type %s; got type %s" _70_12757 _70_12756))))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun ( r ) ( msg ) -> (let _70_12763 = (let _70_12762 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Diagnostic): %s\n" _70_12762 msg))
in (Support.Microsoft.FStar.Util.print_string _70_12763)))

let warn = (fun ( r ) ( msg ) -> (let _70_12769 = (let _70_12768 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Warning): %s\n" _70_12768 msg))
in (Support.Microsoft.FStar.Util.print_string _70_12769)))

let num_errs = (Support.Microsoft.FStar.Util.mk_ref 0)

let verification_errs = (Support.Microsoft.FStar.Util.mk_ref [])

let add_errors = (fun ( env ) ( errs ) -> (let errs = (Support.All.pipe_right errs (Support.List.map (fun ( _33_14 ) -> (match (_33_14) with
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
in (Support.Microsoft.FStar.Util.atomically (fun ( _33_18 ) -> (match (()) with
| () -> begin
(let _33_19 = (let _70_12777 = (let _70_12776 = (Support.ST.read verification_errs)
in (Support.List.append errs _70_12776))
in (Support.ST.op_Colon_Equals verification_errs _70_12777))
in (let _70_12778 = ((Support.ST.read num_errs) + n_errs)
in (Support.ST.op_Colon_Equals num_errs _70_12778)))
end))))))

let report_all = (fun ( _33_21 ) -> (match (()) with
| () -> begin
(let all_errs = (Support.Microsoft.FStar.Util.atomically (fun ( _33_22 ) -> (match (()) with
| () -> begin
(let x = (Support.ST.read verification_errs)
in (let _33_24 = (Support.ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (Support.List.sortWith (fun ( _33_30 ) ( _33_34 ) -> (match ((_33_30, _33_34)) with
| ((r1, _33_29), (r2, _33_33)) -> begin
(Support.Microsoft.FStar.Range.compare r1 r2)
end)) all_errs)
in (let _33_39 = (Support.All.pipe_right all_errs (Support.List.iter (fun ( _33_38 ) -> (match (_33_38) with
| (r, msg) -> begin
(let _70_12785 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.fprint2 "%s: %s\n" _70_12785 msg))
end))))
in (Support.List.length all_errs))))
end))

let report = (fun ( r ) ( msg ) -> (let _33_43 = (Support.Microsoft.FStar.Util.incr num_errs)
in (let _70_12791 = (let _70_12790 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _70_12790 msg))
in (Support.Microsoft.FStar.Util.print_string _70_12791))))

let get_err_count = (fun ( _33_45 ) -> (match (()) with
| () -> begin
(Support.ST.read num_errs)
end))

let unexpected_signature_for_monad = (fun ( env ) ( m ) ( k ) -> (let _70_12800 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.Microsoft_FStar_Absyn_Syntax.str _70_12800)))

let expected_a_term_of_type_t_got_a_function = (fun ( env ) ( msg ) ( t ) ( e ) -> (let _70_12810 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12809 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _70_12810 _70_12809 msg))))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun ( env ) ( t1 ) ( e ) ( t2 ) -> (let _70_12821 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_12820 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_12819 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _70_12821 _70_12820 _70_12819)))))

let expected_function_with_parameter_of_type = (fun ( env ) ( t1 ) ( t2 ) -> (let _70_12833 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_12832 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _70_12833 _70_12832))))

let expected_pattern_of_type = (fun ( env ) ( t1 ) ( e ) ( t2 ) -> (let _70_12844 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_12843 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_12842 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _70_12844 _70_12843 _70_12842)))))

let basic_type_error = (fun ( env ) ( eopt ) ( t1 ) ( t2 ) -> (match (eopt) with
| None -> begin
(let _70_12854 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_12853 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _70_12854 _70_12853)))
end
| Some (e) -> begin
(let _70_12857 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _70_12856 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_12855 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _70_12857 _70_12856 _70_12855))))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun ( env ) ( k1 ) ( k2 ) -> (let _70_12865 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _70_12864 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _70_12865 _70_12864))))

let constructor_builds_the_wrong_type = (fun ( env ) ( d ) ( t ) ( t' ) -> (let _70_12876 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _70_12875 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12874 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t')
in (Support.Microsoft.FStar.Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _70_12876 _70_12875 _70_12874)))))

let constructor_fails_the_positivity_check = (fun ( env ) ( d ) ( l ) -> (let _70_12881 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _70_12880 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _70_12881 _70_12880))))

let inline_type_annotation_and_val_decl = (fun ( l ) -> (let _70_12884 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _70_12884)))

let inferred_type_causes_variable_to_escape = (fun ( env ) ( t ) ( x ) -> (let _70_12889 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12888 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (Support.Microsoft.FStar.Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _70_12889 _70_12888))))

let expected_typ_of_kind = (fun ( env ) ( k1 ) ( t ) ( k2 ) -> (let _70_12900 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _70_12899 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12898 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _70_12900 _70_12899 _70_12898)))))

let expected_tcon_kind = (fun ( env ) ( t ) ( k ) -> (let _70_12908 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12907 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _70_12908 _70_12907))))

let expected_dcon_kind = (fun ( env ) ( t ) ( k ) -> (let _70_12916 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12915 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _70_12916 _70_12915))))

let expected_function_typ = (fun ( env ) ( t ) -> (let _70_12921 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _70_12921)))

let expected_poly_typ = (fun ( env ) ( f ) ( t ) ( targ ) -> (let _70_12932 = (Microsoft_FStar_Absyn_Print.exp_to_string f)
in (let _70_12931 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _70_12930 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env targ)
in (Support.Microsoft.FStar.Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _70_12932 _70_12931 _70_12930)))))

let nonlinear_pattern_variable = (fun ( x ) -> (let m = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end)
in (Support.Microsoft.FStar.Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun ( v1 ) ( v2 ) -> (let vars = (fun ( v ) -> (let _70_12939 = (Support.All.pipe_right v (Support.List.map (fun ( _33_1 ) -> (match (_33_1) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end))))
in (Support.All.pipe_right _70_12939 (Support.String.concat ", "))))
in (let _70_12941 = (vars v1)
in (let _70_12940 = (vars v2)
in (Support.Microsoft.FStar.Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _70_12941 _70_12940)))))

let name_and_result = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _70_12943 = (Microsoft_FStar_Absyn_Print.sli ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (_70_12943, ct.Microsoft_FStar_Absyn_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun ( env ) ( e ) ( c ) ( c' ) -> (let _33_127 = (name_and_result c)
in (match (_33_127) with
| (f1, r1) -> begin
(let _33_130 = (name_and_result c')
in (match (_33_130) with
| (f2, r2) -> begin
(let _70_12949 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _70_12948 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r2)
in (Support.Microsoft.FStar.Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _70_12949 f1 _70_12948 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun ( env ) ( f ) -> (let _70_12954 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
in (Support.Microsoft.FStar.Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _70_12954)))

let expected_pure_expression = (fun ( e ) ( c ) -> (let _70_12959 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_12958 = (let _70_12957 = (name_and_result c)
in (Support.All.pipe_left Support.Prims.fst _70_12957))
in (Support.Microsoft.FStar.Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _70_12959 _70_12958))))

let expected_ghost_expression = (fun ( e ) ( c ) -> (let _70_12964 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_12963 = (let _70_12962 = (name_and_result c)
in (Support.All.pipe_left Support.Prims.fst _70_12962))
in (Support.Microsoft.FStar.Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _70_12964 _70_12963))))

let expected_effect_1_got_effect_2 = (fun ( c1 ) ( c2 ) -> (let _70_12970 = (Microsoft_FStar_Absyn_Print.sli c1)
in (let _70_12969 = (Microsoft_FStar_Absyn_Print.sli c2)
in (Support.Microsoft.FStar.Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _70_12970 _70_12969))))

let failed_to_prove_specification_of = (fun ( l ) ( lbls ) -> (let _70_12976 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _70_12975 = (Support.All.pipe_right lbls (Support.String.concat ", "))
in (Support.Microsoft.FStar.Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _70_12976 _70_12975))))

let failed_to_prove_specification = (fun ( lbls ) -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _33_144 -> begin
(let _70_12979 = (Support.All.pipe_right lbls (Support.String.concat "\n\t"))
in (Support.Microsoft.FStar.Util.format1 "The following problems were found:\n\t%s" _70_12979))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"




