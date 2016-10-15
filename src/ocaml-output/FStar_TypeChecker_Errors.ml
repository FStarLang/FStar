
open Prims

let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _149_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _149_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _149_10 _149_9))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> if (FStar_Options.debug_any ()) then begin
(let _149_16 = (let _149_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Diagnostic): %s\n" _149_15 msg))
in (FStar_Util.print_string _149_16))
end else begin
()
end)


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _149_22 = (let _149_21 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s (Warning): %s\n" _149_21 msg))
in (FStar_Util.print_string _149_22)))


let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let is_Mkerror_message_prefix : error_message_prefix  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkerror_message_prefix"))))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.op_Colon_Equals pfx (Some (s))))
in (

let clear_prefix = (fun _54_18 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals pfx None)
end))
in (

let append_prefix = (fun s -> (match ((FStar_ST.read pfx)) with
| None -> begin
s
end
| Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let add_errors : FStar_TypeChecker_Env.env  ->  (Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun env errs -> (

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _54_28 -> (match (_54_28) with
| (msg, r) -> begin
(

let r = if (r = FStar_Range.dummyRange) then begin
(FStar_TypeChecker_Env.get_range env)
end else begin
r
end
in (let _149_62 = (message_prefix.append_prefix msg)
in ((r), (_149_62))))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _54_32 -> (match (()) with
| () -> begin
(

let _54_33 = (let _149_65 = (let _149_64 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _149_64))
in (FStar_ST.op_Colon_Equals verification_errs _149_65))
in (let _149_66 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _149_66)))
end))))))


let report_all : Prims.unit  ->  Prims.int = (fun _54_35 -> (match (()) with
| () -> begin
(

let all_errs = (FStar_Util.atomically (fun _54_36 -> (match (()) with
| () -> begin
(

let x = (FStar_ST.read verification_errs)
in (

let _54_38 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (

let all_errs = (FStar_List.sortWith (fun _54_44 _54_48 -> (match (((_54_44), (_54_48))) with
| ((r1, _54_43), (r2, _54_47)) -> begin
(FStar_Range.compare r1 r2)
end)) all_errs)
in (

let _54_53 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _54_52 -> (match (_54_52) with
| (r, msg) -> begin
(let _149_73 = (FStar_Range.string_of_range r)
in (FStar_Util.print2 "%s: %s\n" _149_73 msg))
end))))
in (FStar_List.length all_errs))))
end))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (let _149_79 = (let _149_78 = (FStar_Range.string_of_range r)
in (_149_78)::(if warning then begin
"Warning"
end else begin
"Error"
end)::(msg)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s : %s\n%s\n" _149_79)))
end
| FStar_Util.NYI (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.fprint FStar_Util.stderr "Feature not yet implemented: %s" ((msg)::[])))
end
| FStar_Syntax_Syntax.Err (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.fprint FStar_Util.stderr "Error: %s" ((msg)::[])))
end
| _54_69 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _54_1 -> (match (_54_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _54_81 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let _54_84 = (FStar_Util.incr num_errs)
in (

let msg = (message_prefix.append_prefix msg)
in (let _149_87 = (let _149_86 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _149_86 msg))
in (FStar_Util.print_string _149_87)))))


let get_err_count : Prims.unit  ->  Prims.int = (fun _54_87 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _149_96 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect);\ngot %s" m.FStar_Ident.str _149_96)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _149_106 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_105 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\";\ngot a function \"%s\" (%s)" _149_106 _149_105 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _149_117 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_116 = (FStar_Syntax_Print.term_to_string e)
in (let _149_115 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\";\ngot expression \"%s\" of type \"%s\"" _149_117 _149_116 _149_115)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _149_129 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_128 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _149_129 _149_128))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _149_140 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_139 = (FStar_Syntax_Print.term_to_string e)
in (let _149_138 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\";\ngot pattern \"%s\" of type \"%s\"" _149_140 _149_139 _149_138)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _149_150 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_149 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\";\ngot type \"%s\"" _149_150 _149_149)))
end
| Some (e) -> begin
(let _149_153 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_152 = (FStar_Syntax_Print.term_to_string e)
in (let _149_151 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _149_153 _149_152 _149_151))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _149_161 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _149_160 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _149_161 _149_160))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _149_172 = (FStar_Syntax_Print.term_to_string d)
in (let _149_171 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_170 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _149_172 _149_171 _149_170)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _149_177 = (FStar_Syntax_Print.term_to_string d)
in (let _149_176 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _149_177 _149_176))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _149_180 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _149_180)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _149_188 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_187 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _149_188 _149_187))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _149_199 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _149_198 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_197 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\";\ngot \"%s\" of kind \"%s\"" _149_199 _149_198 _149_197)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _149_207 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_206 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _149_207 _149_206))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _149_215 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_214 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function;\ngot a type \"%s\" of kind \"%s\"" _149_215 _149_214))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _149_220 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function;\ngot an expression of type \"%s\"" _149_220)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _149_231 = (FStar_Syntax_Print.term_to_string f)
in (let _149_230 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_229 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function;\ngot an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _149_231 _149_230 _149_229)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (let _149_240 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _149_240 (FStar_String.concat ", "))))
in (let _149_242 = (vars v1)
in (let _149_241 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _149_242 _149_241)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _54_152) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, _54_157) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _149_244 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((_149_244), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let _54_168 = (name_and_result c)
in (match (_54_168) with
| (f1, r1) -> begin
(

let _54_171 = (name_and_result c')
in (match (_54_171) with
| (f2, r2) -> begin
(let _149_250 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _149_249 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _149_250 f1 _149_249 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _149_255 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _149_255)))


let expected_pure_expression = (fun e c -> (let _149_260 = (FStar_Syntax_Print.term_to_string e)
in (let _149_259 = (let _149_258 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _149_258))
in (FStar_Util.format2 "Expected a pure expression;\ngot an expression \"%s\" with effect \"%s\"" _149_260 _149_259))))


let expected_ghost_expression = (fun e c -> (let _149_265 = (FStar_Syntax_Print.term_to_string e)
in (let _149_264 = (let _149_263 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _149_263))
in (FStar_Util.format2 "Expected a ghost expression;\ngot an expression \"%s\" with effect \"%s\"" _149_265 _149_264))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _149_271 = (FStar_Syntax_Print.lid_to_string c1)
in (let _149_270 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s\n" _149_271 _149_270))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _149_277 = (FStar_Syntax_Print.lbname_to_string l)
in (let _149_276 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _149_277 _149_276))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _54_185 -> begin
(let _149_280 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _149_280))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _149_284 = (FStar_Syntax_Print.lid_to_string l)
in (let _149_283 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _149_284 _149_283))))




