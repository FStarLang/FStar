
open Prims

let exhaustiveness_check : Prims.string = "Patterns are incomplete"


let subtyping_failed : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit  ->  Prims.string = (fun env t1 t2 x -> (let _154_10 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _154_9 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (FStar_Util.format2 "Subtyping check failed; expected type %s; got type %s" _154_10 _154_9))))


let ill_kinded_type : Prims.string = "Ill-kinded type"


let totality_check : Prims.string = "This term may not terminate"


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> if (FStar_Options.debug_any ()) then begin
(let _154_16 = (let _154_15 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s : (Diagnostic) %s\n" _154_15 msg))
in (FStar_Util.print_string _154_16))
end else begin
()
end)


let warn : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (let _154_21 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "%s: (Warning) %s\n" _154_21 msg)))


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

let r = if (r = FStar_Range.dummyRange) then begin
(FStar_TypeChecker_Env.get_range env)
end else begin
r
end
in (let _154_61 = (message_prefix.append_prefix msg)
in ((r), (_154_61))))
end))))
in (

let n_errs = (FStar_List.length errs)
in (FStar_Util.atomically (fun _56_32 -> (match (()) with
| () -> begin
(

let _56_33 = (let _154_64 = (let _154_63 = (FStar_ST.read verification_errs)
in (FStar_List.append errs _154_63))
in (FStar_ST.op_Colon_Equals verification_errs _154_64))
in (let _154_65 = ((FStar_ST.read num_errs) + n_errs)
in (FStar_ST.op_Colon_Equals num_errs _154_65)))
end))))))


let mk_error : Prims.string  ->  FStar_Range.range  ->  Prims.string = (fun msg r -> if (r.FStar_Range.use_range <> r.FStar_Range.def_range) then begin
(let _154_71 = (FStar_Range.string_of_use_range r)
in (let _154_70 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s: (Error) %s (see %s)\n" _154_71 msg _154_70)))
end else begin
(let _154_72 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: (Error) %s\n" _154_72 msg))
end)


let report_all : Prims.unit  ->  Prims.int = (fun _56_37 -> (match (()) with
| () -> begin
(

let all_errs = (FStar_Util.atomically (fun _56_38 -> (match (()) with
| () -> begin
(

let x = (FStar_ST.read verification_errs)
in (

let _56_40 = (FStar_ST.op_Colon_Equals verification_errs [])
in x))
end)))
in (

let all_errs = (FStar_List.sortWith (fun _56_46 _56_50 -> (match (((_56_46), (_56_50))) with
| ((r1, _56_45), (r2, _56_49)) -> begin
(FStar_Range.compare_use_range r1 r2)
end)) all_errs)
in (

let _56_55 = (FStar_All.pipe_right all_errs (FStar_List.iter (fun _56_54 -> (match (_56_54) with
| (r, msg) -> begin
(let _154_79 = (mk_error msg r)
in (FStar_Util.print_error _154_79))
end))))
in (FStar_List.length all_errs))))
end))


let handle_err : Prims.bool  ->  Prims.exn  ->  Prims.unit = (fun warning e -> (match (e) with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(

let msg = (message_prefix.append_prefix msg)
in (let _154_84 = (FStar_Range.string_of_range r)
in (FStar_Util.print3_error "%s : %s %s\n" _154_84 (if warning then begin
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
| _56_71 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _56_1 -> (match (_56_1) with
| (FStar_Syntax_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Syntax_Syntax.Err (_)) -> begin
true
end
| _56_83 -> begin
false
end))


let report : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let _56_86 = (FStar_Util.incr num_errs)
in (

let msg = (message_prefix.append_prefix msg)
in (let _154_91 = (mk_error msg r)
in (FStar_Util.print_error _154_91)))))


let get_err_count : Prims.unit  ->  Prims.int = (fun _56_89 -> (match (()) with
| () -> begin
(FStar_ST.read num_errs)
end))


let unexpected_signature_for_monad : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env m k -> (let _154_100 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Unexpected signature for monad \"%s\". Expected a signature of the form (a:Type => WP a => Effect); got %s" m.FStar_Ident.str _154_100)))


let expected_a_term_of_type_t_got_a_function : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env msg t e -> (let _154_110 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_109 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Expected a term of type \"%s\"; got a function \"%s\" (%s)" _154_110 _154_109 msg))))


let unexpected_implicit_argument : Prims.string = "Unexpected instantiation of an implicit argument to a function that only expects explicit arguments"


let expected_expression_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _154_121 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _154_120 = (FStar_Syntax_Print.term_to_string e)
in (let _154_119 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected expression of type \"%s\"; got expression \"%s\" of type \"%s\"" _154_121 _154_120 _154_119)))))


let expected_function_with_parameter_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string  ->  Prims.string = (fun env t1 t2 -> (let _154_133 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _154_132 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected a function with a parameter of type \"%s\"; this function has a parameter of type \"%s\"" _154_133 _154_132))))


let expected_pattern_of_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t1 e t2 -> (let _154_144 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _154_143 = (FStar_Syntax_Print.term_to_string e)
in (let _154_142 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected pattern of type \"%s\"; got pattern \"%s\" of type \"%s\"" _154_144 _154_143 _154_142)))))


let basic_type_error : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env eopt t1 t2 -> (match (eopt) with
| None -> begin
(let _154_154 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _154_153 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format2 "Expected type \"%s\"; got type \"%s\"" _154_154 _154_153)))
end
| Some (e) -> begin
(let _154_157 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _154_156 = (FStar_Syntax_Print.term_to_string e)
in (let _154_155 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.format3 "Expected type \"%s\"; but \"%s\" has type \"%s\"" _154_157 _154_156 _154_155))))
end))


let occurs_check : Prims.string = "Possibly infinite typ (occurs check failed)"


let unification_well_formedness : Prims.string = "Term or type of an unexpected sort"


let incompatible_kinds : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 k2 -> (let _154_165 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _154_164 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format2 "Kinds \"%s\" and \"%s\" are incompatible" _154_165 _154_164))))


let constructor_builds_the_wrong_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env d t t' -> (let _154_176 = (FStar_Syntax_Print.term_to_string d)
in (let _154_175 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_174 = (FStar_TypeChecker_Normalize.term_to_string env t')
in (FStar_Util.format3 "Constructor \"%s\" builds a value of type \"%s\"; expected \"%s\"" _154_176 _154_175 _154_174)))))


let constructor_fails_the_positivity_check = (fun env d l -> (let _154_181 = (FStar_Syntax_Print.term_to_string d)
in (let _154_180 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format2 "Constructor \"%s\" fails the strict positivity check; the constructed type \"%s\" occurs to the left of a pure function type" _154_181 _154_180))))


let inline_type_annotation_and_val_decl : FStar_Ident.lid  ->  Prims.string = (fun l -> (let _154_184 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "\"%s\" has a val declaration as well as an inlined type annotation; remove one" _154_184)))


let inferred_type_causes_variable_to_escape : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun env t x -> (let _154_192 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_191 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format2 "Inferred type \"%s\" causes variable \"%s\" to escape its scope" _154_192 _154_191))))


let expected_typ_of_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env k1 t k2 -> (let _154_203 = (FStar_TypeChecker_Normalize.term_to_string env k1)
in (let _154_202 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_201 = (FStar_TypeChecker_Normalize.term_to_string env k2)
in (FStar_Util.format3 "Expected type of kind \"%s\"; got \"%s\" of kind \"%s\"" _154_203 _154_202 _154_201)))))


let expected_tcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _154_211 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_210 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a type-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _154_211 _154_210))))


let expected_dcon_kind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t k -> (let _154_219 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_218 = (FStar_TypeChecker_Normalize.term_to_string env k)
in (FStar_Util.format2 "Expected a term-to-type constructor or function; got a type \"%s\" of kind \"%s\"" _154_219 _154_218))))


let expected_function_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _154_224 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format1 "Expected a function; got an expression of type \"%s\"" _154_224)))


let expected_poly_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f t targ -> (let _154_235 = (FStar_Syntax_Print.term_to_string f)
in (let _154_234 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_233 = (FStar_TypeChecker_Normalize.term_to_string env targ)
in (FStar_Util.format3 "Expected a polymorphic function; got an expression \"%s\" of type \"%s\" applied to a type \"%s\"" _154_235 _154_234 _154_233)))))


let nonlinear_pattern_variable : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (

let m = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "The pattern variable \"%s\" was used more than once" m)))


let disjunctive_pattern_vars : FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun v1 v2 -> (

let vars = (fun v -> (let _154_244 = (FStar_All.pipe_right v (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right _154_244 (FStar_String.concat ", "))))
in (let _154_246 = (vars v1)
in (let _154_245 = (vars v2)
in (FStar_Util.format2 "Every alternative of an \'or\' pattern must bind the same variables; here one branch binds (\"%s\") and another (\"%s\")" _154_246 _154_245)))))


let name_and_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _56_154) -> begin
(("Tot"), (t))
end
| FStar_Syntax_Syntax.GTotal (t, _56_159) -> begin
(("GTot"), (t))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _154_248 = (FStar_Syntax_Print.lid_to_string ct.FStar_Syntax_Syntax.effect_name)
in ((_154_248), (ct.FStar_Syntax_Syntax.result_typ)))
end))


let computed_computation_type_does_not_match_annotation = (fun env e c c' -> (

let _56_170 = (name_and_result c)
in (match (_56_170) with
| (f1, r1) -> begin
(

let _56_173 = (name_and_result c')
in (match (_56_173) with
| (f2, r2) -> begin
(let _154_254 = (FStar_TypeChecker_Normalize.term_to_string env r1)
in (let _154_253 = (FStar_TypeChecker_Normalize.term_to_string env r2)
in (FStar_Util.format4 "Computed type \"%s\" and effect \"%s\" is not compatible with the annotated type \"%s\" effect \"%s\"" _154_254 f1 _154_253 f2)))
end))
end)))


let unexpected_non_trivial_precondition_on_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env f -> (let _154_259 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.format1 "Term has an unexpected non-trivial pre-condition: %s" _154_259)))


let expected_pure_expression = (fun e c -> (let _154_264 = (FStar_Syntax_Print.term_to_string e)
in (let _154_263 = (let _154_262 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _154_262))
in (FStar_Util.format2 "Expected a pure expression; got an expression \"%s\" with effect \"%s\"" _154_264 _154_263))))


let expected_ghost_expression = (fun e c -> (let _154_269 = (FStar_Syntax_Print.term_to_string e)
in (let _154_268 = (let _154_267 = (name_and_result c)
in (FStar_All.pipe_left Prims.fst _154_267))
in (FStar_Util.format2 "Expected a ghost expression; got an expression \"%s\" with effect \"%s\"" _154_269 _154_268))))


let expected_effect_1_got_effect_2 : FStar_Ident.lident  ->  FStar_Ident.lident  ->  Prims.string = (fun c1 c2 -> (let _154_275 = (FStar_Syntax_Print.lid_to_string c1)
in (let _154_274 = (FStar_Syntax_Print.lid_to_string c2)
in (FStar_Util.format2 "Expected a computation with effect %s; but it has effect %s" _154_275 _154_274))))


let failed_to_prove_specification_of : FStar_Syntax_Syntax.lbname  ->  Prims.string Prims.list  ->  Prims.string = (fun l lbls -> (let _154_281 = (FStar_Syntax_Print.lbname_to_string l)
in (let _154_280 = (FStar_All.pipe_right lbls (FStar_String.concat ", "))
in (FStar_Util.format2 "Failed to prove specification of %s; assertions at [%s] may fail" _154_281 _154_280))))


let failed_to_prove_specification : Prims.string Prims.list  ->  Prims.string = (fun lbls -> (match (lbls) with
| [] -> begin
"An unknown assertion in the term at this location was not provable"
end
| _56_187 -> begin
(let _154_284 = (FStar_All.pipe_right lbls (FStar_String.concat "\n\t"))
in (FStar_Util.format1 "The following problems were found:\n\t%s" _154_284))
end))


let top_level_effect : Prims.string = "Top-level let-bindings must be total; this term may have effects"


let cardinality_constraint_violated = (fun l a -> (let _154_288 = (FStar_Syntax_Print.lid_to_string l)
in (let _154_287 = (FStar_Syntax_Print.bv_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "Constructor %s violates the cardinality of Type at parameter \'%s\'; type arguments are not allowed" _154_288 _154_287))))




