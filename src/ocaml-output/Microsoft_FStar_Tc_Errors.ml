
let exhaustiveness_check = "Patterns are incomplete"

let subtyping_failed = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) ( x  :  unit ) -> (let _52_9193 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _52_9192 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (Support.Microsoft.FStar.Util.format2 "Subtyping check failed; expected type %s; got type %s" _52_9193 _52_9192))))

let ill_kinded_type = "Ill-kinded type"

let totality_check = "This term may not terminate"

let diag = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( msg  :  string ) -> (let _52_9199 = (let _52_9198 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Diagnostic): %s\n" _52_9198 msg))
in (Support.Microsoft.FStar.Util.print_string _52_9199)))

let warn = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( msg  :  string ) -> (let _52_9205 = (let _52_9204 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s (Warning): %s\n" _52_9204 msg))
in (Support.Microsoft.FStar.Util.print_string _52_9205)))

let num_errs = (Support.Microsoft.FStar.Util.mk_ref 0)

let verification_errs = (Support.Microsoft.FStar.Util.mk_ref [])

let add_errors = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( errs  :  (string * Support.Microsoft.FStar.Range.range) list ) -> (let errs = (Support.Prims.pipe_right errs (Support.List.map (fun ( _31_14  :  (string * Support.Microsoft.FStar.Range.range) ) -> (match (_31_14) with
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
in (Support.Microsoft.FStar.Util.atomically (fun ( _31_18  :  unit ) -> (match (()) with
| () -> begin
(let _31_19 = (let _52_9213 = (let _52_9212 = (Support.ST.read verification_errs)
in (Support.List.append errs _52_9212))
in (Support.ST.op_Colon_Equals verification_errs _52_9213))
in (let _52_9215 = (let _52_9214 = (Support.ST.read num_errs)
in (_52_9214 + n_errs))
in (Support.ST.op_Colon_Equals num_errs _52_9215)))
end))))))

let report_all = (fun ( _31_21  :  unit ) -> (match (()) with
| () -> begin
(let all_errs = (Support.Microsoft.FStar.Util.atomically (fun ( _31_22  :  unit ) -> (match (()) with
| () -> begin
(let x = (Support.ST.read verification_errs)
in (let _31_24 = (Support.ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (let all_errs = (Support.List.sortWith (fun ( _31_30  :  (Support.Microsoft.FStar.Range.range * string) ) ( _31_34  :  (Support.Microsoft.FStar.Range.range * string) ) -> (match ((_31_30, _31_34)) with
| ((r1, _), (r2, _)) -> begin
(Support.Microsoft.FStar.Range.compare r1 r2)
end)) all_errs)
in (let _31_39 = (Support.Prims.pipe_right all_errs (Support.List.iter (fun ( _31_38  :  (Support.Microsoft.FStar.Range.range * string) ) -> (match (_31_38) with
| (r, msg) -> begin
(let _52_9222 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.fprint2 "%s: %s\n" _52_9222 msg))
end))))
in (Support.List.length all_errs))))
end))

let report = (fun ( r  :  Support.Microsoft.FStar.Range.range ) ( msg  :  string ) -> (let _31_43 = (Support.Microsoft.FStar.Util.incr num_errs)
in (let _52_9228 = (let _52_9227 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _52_9227 msg))
in (Support.Microsoft.FStar.Util.print_string _52_9228))))

let get_err_count = (fun ( _31_45  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.read num_errs)
end))

let unexpected_signature_for_monad = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( m  :  Microsoft_FStar_Absyn_Syntax.l__LongIdent ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_9237 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Unexpected signature for monad \"%s\". Expected a kind of the form (\'a:Type => WP \'a => WP \'a => Type);\ngot %s" m.Microsoft_FStar_Absyn_Syntax.str _52_9237)))

let expected_a_term_of_type_t_got_a_function = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( msg  :  string ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_9247 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9246 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _52_9247 _52_9246 msg))))

let unexpected_implicit_argument = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"

let expected_expression_of_type = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9258 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_9257 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_9256 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _52_9258 _52_9257 _52_9256)))))

let expected_function_with_parameter_of_type = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9270 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_9269 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _52_9270 _52_9269))))

let expected_pattern_of_type = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9281 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_9280 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_9279 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _52_9281 _52_9280 _52_9279)))))

let basic_type_error = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( eopt  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax option ) ( t1  :  Microsoft_FStar_Absyn_Syntax.typ ) ( t2  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (match (eopt) with
| None -> begin
(let _52_9291 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_9290 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _52_9291 _52_9290)))
end
| Some (e) -> begin
(let _52_9294 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _52_9293 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_9292 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t2)
in (Support.Microsoft.FStar.Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _52_9294 _52_9293 _52_9292))))
end))

let occurs_check = "Possibly infinite typ (occurs check failed)"

let unification_well_formedness = "Term or type of an unexpected sort"

let incompatible_kinds = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k1  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k2  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_9302 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _52_9301 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _52_9302 _52_9301))))

let constructor_builds_the_wrong_type = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( d  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( t'  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9313 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _52_9312 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9311 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t')
in (Support.Microsoft.FStar.Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _52_9313 _52_9312 _52_9311)))))

let constructor_fails_the_positivity_check = (fun ( env  :  'u31u961 ) ( d  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let _52_9318 = (Microsoft_FStar_Absyn_Print.exp_to_string d)
in (let _52_9317 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _52_9318 _52_9317))))

let inline_type_annotation_and_val_decl = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let _52_9321 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _52_9321)))

let inferred_type_causes_variable_to_escape = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( x  :  'u31u977 Microsoft_FStar_Absyn_Syntax.bvdef ) -> (let _52_9326 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9325 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (Support.Microsoft.FStar.Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _52_9326 _52_9325))))

let expected_typ_of_kind = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( k1  :  Microsoft_FStar_Absyn_Syntax.knd ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( k2  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_9337 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k1)
in (let _52_9336 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9335 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k2)
in (Support.Microsoft.FStar.Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _52_9337 _52_9336 _52_9335)))))

let expected_tcon_kind = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_9345 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9344 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _52_9345 _52_9344))))

let expected_dcon_kind = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_9353 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9352 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env k)
in (Support.Microsoft.FStar.Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _52_9353 _52_9352))))

let expected_function_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9358 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (Support.Microsoft.FStar.Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _52_9358)))

let expected_poly_typ = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( f  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( t  :  Microsoft_FStar_Absyn_Syntax.typ ) ( targ  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9369 = (Microsoft_FStar_Absyn_Print.exp_to_string f)
in (let _52_9368 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env t)
in (let _52_9367 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env targ)
in (Support.Microsoft.FStar.Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _52_9369 _52_9368 _52_9367)))))

let nonlinear_pattern_variable = (fun ( x  :  ('u31u1095 Microsoft_FStar_Absyn_Syntax.bvdef, 'u31u1094 Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either ) -> (let m = (match (x) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end)
in (Support.Microsoft.FStar.Util.format1 "The pattern variable \"%s\" was used more than once" m)))

let disjunctive_pattern_vars = (fun ( v1  :  ('u31u1266 Microsoft_FStar_Absyn_Syntax.bvdef, 'u31u1265 Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either list ) ( v2  :  ('u31u1266 Microsoft_FStar_Absyn_Syntax.bvdef, 'u31u1265 Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either list ) -> (let vars = (fun ( v  :  ('u31u1266 Microsoft_FStar_Absyn_Syntax.bvdef, 'u31u1265 Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either list ) -> (let _52_9376 = (Support.Prims.pipe_right v (Support.List.map (fun ( _31_1  :  ('u31u1266 Microsoft_FStar_Absyn_Syntax.bvdef, 'u31u1265 Microsoft_FStar_Absyn_Syntax.bvdef) Support.Microsoft.FStar.Util.either ) -> (match (_31_1) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end))))
in (Support.Prims.pipe_right _52_9376 (Support.String.concat ", "))))
in (let _52_9378 = (vars v1)
in (let _52_9377 = (vars v2)
in (Support.Microsoft.FStar.Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _52_9378 _52_9377)))))

let name_and_result = (fun ( c  :  (Microsoft_FStar_Absyn_Syntax.comp', 'u31u1337) Microsoft_FStar_Absyn_Syntax.syntax ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
("Tot", t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _52_9380 = (Microsoft_FStar_Absyn_Print.sli ct.Microsoft_FStar_Absyn_Syntax.effect_name)
in (_52_9380, ct.Microsoft_FStar_Absyn_Syntax.result_typ))
end))

let computed_computation_type_does_not_match_annotation = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( e  :  'u31u1406 ) ( c  :  (Microsoft_FStar_Absyn_Syntax.comp', 'u31u1405) Microsoft_FStar_Absyn_Syntax.syntax ) ( c'  :  (Microsoft_FStar_Absyn_Syntax.comp', 'u31u1404) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _31_127 = (name_and_result c)
in (match (_31_127) with
| (f1, r1) -> begin
(let _31_130 = (name_and_result c')
in (match (_31_130) with
| (f2, r2) -> begin
(let _52_9386 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r1)
in (let _52_9385 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env r2)
in (Support.Microsoft.FStar.Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _52_9386 f1 _52_9385 f2)))
end))
end)))

let unexpected_non_trivial_precondition_on_term = (fun ( env  :  Microsoft_FStar_Tc_Env.env ) ( f  :  Microsoft_FStar_Absyn_Syntax.typ ) -> (let _52_9391 = (Microsoft_FStar_Tc_Normalize.formula_norm_to_string env f)
in (Support.Microsoft.FStar.Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _52_9391)))

let expected_pure_expression = (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( c  :  (Microsoft_FStar_Absyn_Syntax.comp', 'u31u1436) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_9396 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_9395 = (let _52_9394 = (name_and_result c)
in (Support.Prims.pipe_left Support.Prims.fst _52_9394))
in (Support.Microsoft.FStar.Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _52_9396 _52_9395))))

let expected_ghost_expression = (fun ( e  :  (Microsoft_FStar_Absyn_Syntax.exp', (Microsoft_FStar_Absyn_Syntax.typ', (Microsoft_FStar_Absyn_Syntax.knd', unit) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax) Microsoft_FStar_Absyn_Syntax.syntax ) ( c  :  (Microsoft_FStar_Absyn_Syntax.comp', 'u31u1459) Microsoft_FStar_Absyn_Syntax.syntax ) -> (let _52_9401 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_9400 = (let _52_9399 = (name_and_result c)
in (Support.Prims.pipe_left Support.Prims.fst _52_9399))
in (Support.Microsoft.FStar.Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _52_9401 _52_9400))))

let expected_effect_1_got_effect_2 = (fun ( c1  :  Microsoft_FStar_Absyn_Syntax.lident ) ( c2  :  Microsoft_FStar_Absyn_Syntax.lident ) -> (let _52_9407 = (Microsoft_FStar_Absyn_Print.sli c1)
in (let _52_9406 = (Microsoft_FStar_Absyn_Print.sli c2)
in (Support.Microsoft.FStar.Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _52_9407 _52_9406))))

let failed_to_prove_specification_of = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.lbname ) ( lbls  :  string list ) -> (let _52_9413 = (Microsoft_FStar_Absyn_Print.lbname_to_string l)
in (let _52_9412 = (Support.Prims.pipe_right lbls (Support.String.concat ", "))
in (Support.Microsoft.FStar.Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _52_9413 _52_9412))))

let failed_to_prove_specification = (fun ( lbls  :  string list ) -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _ -> begin
(let _52_9416 = (Support.Prims.pipe_right lbls (Support.String.concat "\n\t"))
in (Support.Microsoft.FStar.Util.format1 "The following problems were found:\n\t%s" _52_9416))
end))

let top_level_effect = "Top-level let-bindings must be total; this term may have effects"




