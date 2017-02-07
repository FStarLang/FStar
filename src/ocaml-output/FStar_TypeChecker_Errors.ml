
open Prims

let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _155_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _155_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _155_10 _155_9))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> if (FStar_Options.debug_any ()) then begin
(let _155_16 = (let _155_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s : (Diagnostic) %s\n" _155_15 msg))
in (FStar_Util.print_string _155_16))
end else begin
()
end)


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _155_21 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "%s: (Warning) %s\n" _155_21 msg)))


let num_errs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let verification_errs : (FStar_Range.range * Prims.string) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let is_Mkerror_message_prefix : error_message_prefix  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkerror_message_prefix"))))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref None)
in (

let set_prefix = (fun s -> (FStar_ST.op_Colon_Equals pfx (Some (s))))
in (

let clear_prefix = (fun _56_18 -> (match (()) with
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

let errs = (FStar_All.pipe_right errs (FStar_List.map (fun _56_28 -> (match (_56_28) with
| (msg, r) -> begin
(

let _56_34 = if (r = FStar_Range.dummyRange) then begin
(let _155_61 = (FStar_TypeChecker_Env.get_range env)
in ((_155_61), (msg)))
end else begin
(

let r' = (

let _56_29 = r
in {FStar_Range.def_range = r.FStar_Range.use_range; FStar_Range.use_range = _56_29.FStar_Range.use_range})
in if ((FStar_Range.file_of_range r') <> (let _155_62 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.file_of_range _155_62))) then begin
(let _155_67 = (FStar_TypeChecker_Env.get_range env)
in (let _155_66 = (let _155_65 = (let _155_64 = (let _155_63 = (FStar_Range.string_of_use_range r)
in (Prims.strcat _155_63 ")"))
in (Prims.strcat "(Also see: " _155_64))
in (Prims.strcat msg _155_65))
in ((_155_67), (_155_66))))
end else begin
((r), (msg))
end)
end
in (match (_56_34) with
| (r, msg) -> begin
(let _155_68 = (message_prefix.append_prefix msg)
in ((r), (_155_68)))
end))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _56_37 -> (match (()) with
| () -> begin
(

let _56_38 = (let _155_71 = (let _155_70 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _155_70))
in (FStar_ST.op_Colon_Equals verification_errs _155_71))
in (let _155_72 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _155_72)))
end))))))


let mk_error : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun msg r -> if (r.FStar_Range.use_range <> r.FStar_Range.def_range) then begin
(let _155_78 = (FStar_Range.string_of_use_range r)
in (let _155_77 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s: (Error) %s (see %s)\n" _155_78 msg _155_77)))
end else begin
(let _155_79 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: (Error) %s\n" _155_79 msg))
end)


let report_all : Prims.unit  ->  Prims.int = (fun _56_42 -> (match (()) with
| () -> begin
(

let all_errs = (FStar_Util.atomically (fun _56_43 -> (match (()) with
| () -> begin
(

let x = (FStar_ST.read verification_errs)
in (

let _56_45 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (

let all_errs = (FStar_List.sortWith (fun _56_51 _56_55 -> (match (((_56_51), (_56_55))) with
| ((r1, _56_50), (r2, _56_54)) -> begin
(FStar_Range.compare_use_range r1 r2)
end)) all_errs)
in (

let _56_60 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _56_59 -> (match (_56_59) with
| (r, msg) -> begin
(let _155_86 = (mk_error msg r)
in (FStar_Util.print_error _155_86))
end))))
in (FStar_List.length all_errs))))
end))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (let _155_91 = (FStar_Range.string_of_range r)
in (FStar_Util.print3_error "%s : %s %s\n" _155_91 (if warning then begin
"(Warning)"
end else begin
"(Error)"
end) msg)))
end
| FStar_Util.NYI (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.print1_error "Feature not yet implemented: %s" msg))
end
| FStar_Syntax_Syntax.Err (msg) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (FStar_Util.print1_error "Error: %s" msg))
end
| _56_76 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _56_1 -> (match (_56_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _56_88 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let _56_91 = (FStar_Util.incr num_errs)
in (

let msg = (message_prefix.append_prefix msg)
in (let _155_98 = (mk_error msg r)
in (FStar_Util.print_error _155_98)))))


let get_err_count : Prims.unit  ->  Prims.int = (fun _56_94 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _155_107 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str _155_107)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _155_117 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_116 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" _155_117 _155_116 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _155_128 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_127 = (FStar_Syntax_Print.term_to_string e)
in (let _155_126 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" _155_128 _155_127 _155_126)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _155_140 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_139 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _155_140 _155_139))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _155_151 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_150 = (FStar_Syntax_Print.term_to_string e)
in (let _155_149 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" _155_151 _155_150 _155_149)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _155_161 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_160 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" _155_161 _155_160)))
end
| Some (e) -> begin
(let _155_164 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_163 = (FStar_Syntax_Print.term_to_string e)
in (let _155_162 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _155_164 _155_163 _155_162))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _155_172 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _155_171 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _155_172 _155_171))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _155_183 = (FStar_Syntax_Print.term_to_string d)
in (let _155_182 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_181 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _155_183 _155_182 _155_181)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _155_188 = (FStar_Syntax_Print.term_to_string d)
in (let _155_187 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _155_188 _155_187))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _155_191 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _155_191)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _155_199 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_198 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _155_199 _155_198))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _155_210 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _155_209 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_208 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" _155_210 _155_209 _155_208)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _155_218 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_217 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _155_218 _155_217))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _155_226 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_225 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _155_226 _155_225))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _155_231 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" _155_231)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _155_242 = (FStar_Syntax_Print.term_to_string f)
in (let _155_241 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_240 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _155_242 _155_241 _155_240)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (let _155_251 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _155_251 (FStar_String.concat ", "))))
in (let _155_253 = (vars v1)
in (let _155_252 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _155_253 _155_252)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _56_159) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, _56_164) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _155_255 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((_155_255), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let _56_175 = (name_and_result c)
in (match (_56_175) with
| (f1, r1) -> begin
(

let _56_178 = (name_and_result c')
in (match (_56_178) with
| (f2, r2) -> begin
(let _155_261 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _155_260 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _155_261 f1 _155_260 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _155_266 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _155_266)))


let expected_pure_expression = (fun e c -> (let _155_271 = (FStar_Syntax_Print.term_to_string e)
in (let _155_270 = (let _155_269 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _155_269))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" _155_271 _155_270))))


let expected_ghost_expression = (fun e c -> (let _155_276 = (FStar_Syntax_Print.term_to_string e)
in (let _155_275 = (let _155_274 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _155_274))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" _155_276 _155_275))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _155_282 = (FStar_Syntax_Print.lid_to_string c1)
in (let _155_281 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" _155_282 _155_281))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _155_288 = (FStar_Syntax_Print.lbname_to_string l)
in (let _155_287 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _155_288 _155_287))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _56_192 -> begin
(let _155_291 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _155_291))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _155_295 = (FStar_Syntax_Print.lid_to_string l)
in (let _155_294 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _155_295 _155_294))))




