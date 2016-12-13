
open Prims

type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.bool  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  FStar_Parser_ParseIt.input_frag  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit; tc_prims : Prims.unit  ->  'env; tc_one_file : Prims.string Prims.list  ->  'env  ->  ((Prims.string Prims.option * Prims.string) * 'env * 'modul * Prims.string Prims.list)}


let is_Mkinteractive_tc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_tc"))))


type input_chunks =
| Push of (Prims.bool * Prims.int * Prims.int)
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))


let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))


let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))


let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))


let ___Push____0 = (fun projectee -> (match (projectee) with
| Push (_91_15) -> begin
_91_15
end))


let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_91_18) -> begin
_91_18
end))


let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_91_21) -> begin
_91_21
end))


type ('env, 'modul) stack =
('env * 'modul) Prims.list


type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))


let the_interactive_state : interactive_state = (let _186_179 = (FStar_Util.new_string_builder ())
in (let _186_178 = (FStar_ST.alloc None)
in (let _186_177 = (FStar_ST.alloc [])
in (let _186_176 = (FStar_ST.alloc None)
in {chunk = _186_179; stdin = _186_178; buffer = _186_177; log = _186_176}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun _91_29 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (

let log = if (FStar_Options.debug_any ()) then begin
(

let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in (

let _91_35 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (

let _91_39 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _91_41 -> ())
end
in (

let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(

let i = (FStar_Util.open_stdin ())
in (

let _91_48 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (

let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| Some (l) -> begin
l
end)
in (

let _91_55 = (log line)
in (

let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (_91_61)::(ok)::(fail)::[] -> begin
((ok), (fail))
end
| _91_64 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in (

let _91_67 = (FStar_Util.clear_string_builder s.chunk)
in Code (((str), (responses))))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(

let _91_69 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(

let _91_71 = (FStar_Util.clear_string_builder s.chunk)
in (

let lc_lax = (let _186_187 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string _186_187))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l)::(c)::("#lax")::[] -> begin
(let _186_189 = (FStar_Util.int_of_string l)
in (let _186_188 = (FStar_Util.int_of_string c)
in ((true), (_186_189), (_186_188))))
end
| (l)::(c)::[] -> begin
(let _186_191 = (FStar_Util.int_of_string l)
in (let _186_190 = (FStar_Util.int_of_string c)
in ((false), (_186_191), (_186_190))))
end
| _91_82 -> begin
(

let _91_83 = (FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax))
in ((false), ((Prims.parse_int "1")), ((Prims.parse_int "0"))))
end)
in Push (lc))))
end else begin
if (l = "#finish") then begin
(FStar_All.exit (Prims.parse_int "0"))
end else begin
(

let _91_86 = (FStar_Util.string_builder_append s.chunk line)
in (

let _91_88 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))


let shift_chunk : Prims.unit  ->  input_chunks = (fun _91_90 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
(

let _91_96 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun _91_98 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (let _186_199 = (let _186_198 = (FStar_ST.read s.buffer)
in (let _186_197 = (let _186_196 = (read_chunk ())
in (_186_196)::[])
in (FStar_List.append _186_198 _186_197)))
in (FStar_ST.op_Colon_Equals s.buffer _186_199)))
end))


exception Found of (Prims.string)


let is_Found = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))


let ___Found____0 = (fun projectee -> (match (projectee) with
| Found (_91_101) -> begin
_91_101
end))


let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _91_102 -> (match (()) with
| () -> begin
(

let _91_103 = (fill_buffer ())
in (

let _91_105 = (fill_buffer ())
in try
(match (()) with
| () -> begin
(

let _91_129 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| (Push (_91_120))::(Code (code, _91_116))::[] -> begin
(

let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (

let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > (Prims.parse_int "7")) && ((FStar_Util.substring line (Prims.parse_int "0") (Prims.parse_int "6")) = "module")) then begin
(

let module_name = (FStar_Util.substring line (Prims.parse_int "7") ((FStar_String.length line) - (Prims.parse_int "7")))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _91_128 -> begin
()
end)
in None)
end)
with
| Found (n) -> begin
Some (n)
end))
end))


let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  (Prims.string * Prims.string Prims.list) = (fun _91_131 -> (match (()) with
| () -> begin
(

let failr = (fun msg r -> (

let _91_135 = if (FStar_Options.universes ()) then begin
(FStar_TypeChecker_Errors.warn r msg)
end else begin
(FStar_Tc_Errors.warn r msg)
end
in (FStar_All.exit (Prims.parse_int "1"))))
in (

let fail = (fun msg -> (failr msg FStar_Range.dummyRange))
in (

let parse_msg = "Dependency analysis may not be correct because the file failed to parse: "
in try
(match (()) with
| () -> begin
(match ((find_initial_module_name ())) with
| None -> begin
(fail "No initial module directive found\n")
end
| Some (module_name) -> begin
(

let file_of_module_name = (FStar_Parser_Dep.build_map [])
in (

let filename = (FStar_Util.smap_try_find file_of_module_name (FStar_String.lowercase module_name))
in (match (filename) with
| None -> begin
(let _186_219 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in (fail _186_219))
end
| (Some (None, Some (filename))) | (Some (Some (filename), None)) -> begin
(

let _91_169 = (FStar_Options.add_verify_module module_name)
in (

let _91_176 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyUserList ((filename)::[]))
in (match (_91_176) with
| (_91_172, all_filenames, _91_175) -> begin
(let _186_221 = (let _186_220 = (FStar_List.tl all_filenames)
in (FStar_List.rev _186_220))
in ((filename), (_186_221)))
end)))
end
| Some (Some (_91_178), Some (_91_181)) -> begin
(let _186_222 = (FStar_Util.format1 "The combination of split interfaces and interactive verification is not supported for: %s\n" module_name)
in (fail _186_222))
end
| Some (None, None) -> begin
(FStar_All.failwith "impossible")
end)))
end)
end)
with
| (FStar_Syntax_Syntax.Error (msg, r)) | (FStar_Absyn_Syntax.Error (msg, r)) -> begin
(failr (Prims.strcat parse_msg msg) r)
end
| (FStar_Syntax_Syntax.Err (msg)) | (FStar_Absyn_Syntax.Err (msg)) -> begin
(fail (Prims.strcat parse_msg msg))
end)))
end))


type m_timestamps =
(Prims.string Prims.option * Prims.string * FStar_Util.time) Prims.list


let interactive_mode = (fun filename filenames initial_mod tc -> (

let _91_197 = (let _186_230 = (FStar_List.fold_left (fun s f -> (Prims.strcat s f)) "" filenames)
in (FStar_Util.print1 "Interactive mode called with: %s\n" _186_230))
in (

let _91_199 = if (let _186_231 = (FStar_Options.codegen ())
in (FStar_Option.isSome _186_231)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (

let rec tc_deps = (fun stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| _91_208 -> begin
(

let _91_215 = (tc.tc_one_file remaining env)
in (match (_91_215) with
| ((intf, impl), env, modl, remaining) -> begin
(

let stack = (((env), (modl)))::stack
in (

let _91_217 = (FStar_Util.print_string "\nCalling push\n")
in (

let env = (tc.push env true "tc modul")
in (let _186_243 = (let _186_242 = (let _186_241 = (let _186_240 = (FStar_Util.now ())
in ((intf), (impl), (_186_240)))
in (_186_241)::[])
in (FStar_List.append ts _186_242))
in (tc_deps stack env remaining _186_243)))))
end))
end))
in (

let update_deps = (fun stk env ts -> (

let _91_224 = (FStar_Util.print_string "Update deps called")
in (

let is_stale = (fun intf impl t -> ((FStar_Util.is_file_modified_after impl t) || (match (intf) with
| Some (f) -> begin
(FStar_Util.is_file_modified_after f t)
end
| None -> begin
false
end)))
in (

let rec iterate = (fun good_stack good_ts stack env ts -> (match (((stack), (ts))) with
| (((env, modl))::stack, ((intf, impl, t))::ts') -> begin
if (is_stale intf impl t) then begin
(

let filenames = (FStar_List.fold_left (fun acc _91_256 -> (match (_91_256) with
| (intf, impl, _91_255) -> begin
(

let _91_257 = (FStar_Util.print_string "\nCalling pop\n")
in (

let _91_259 = (tc.pop env "")
in (match (intf) with
| Some (f) -> begin
(FStar_List.append acc ((f)::(impl)::[]))
end
| None -> begin
(FStar_List.append acc ((impl)::[]))
end)))
end)) [] ts)
in (tc_deps (FStar_List.rev good_stack) env filenames good_ts))
end else begin
(iterate (FStar_List.append good_stack ((((env), (modl)))::[])) (FStar_List.append good_ts ((((intf), (impl), (t)))::[])) stack env ts')
end
end
| ([], []) -> begin
(

let _91_268 = (FStar_Util.print_string "No file was found stale\n")
in (((FStar_List.rev good_stack)), (env), (good_ts)))
end
| (_91_271, _91_273) -> begin
(FStar_All.failwith "Impossible")
end))
in (iterate [] [] (FStar_List.rev stk) env ts)))))
in (

let rec go = (fun line_col stack curmod env ts -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(

let _91_283 = (tc.pop env msg)
in (

let _91_295 = (match (stack) with
| [] -> begin
(

let _91_286 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit (Prims.parse_int "1")))
end
| (hd)::tl -> begin
((hd), (tl))
end)
in (match (_91_295) with
| ((env, curmod), stack) -> begin
(go line_col stack curmod env ts)
end)))
end
| Push (lax, l, c) -> begin
(

let _91_304 = if ((FStar_List.length stack) = (FStar_List.length ts)) then begin
(update_deps stack env ts)
end else begin
((stack), (env), (ts))
end
in (match (_91_304) with
| (stack, env, ts) -> begin
(

let stack = (((env), (curmod)))::stack
in (

let env = (tc.push env lax "#push")
in (go ((l), (c)) stack curmod env ts)))
end))
end
| Code (text, (ok, fail)) -> begin
(

let fail = (fun curmod env_mark -> (

let _91_316 = (tc.report_fail ())
in (

let _91_318 = (FStar_Util.print1 "%s\n" fail)
in (

let env = (tc.reset_mark env_mark)
in (go line_col stack curmod env ts)))))
in (

let env_mark = (tc.mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (Prims.fst line_col); FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)}
in (

let res = (tc.check_frag env_mark curmod frag)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
if (n_errs = (Prims.parse_int "0")) then begin
(

let _91_329 = (FStar_Util.print1 "\n%s\n" ok)
in (

let env = (tc.commit_mark env)
in (go line_col stack curmod env ts)))
end else begin
(fail curmod env_mark)
end
end
| _91_333 -> begin
(fail curmod env_mark)
end)))))
end))
in (

let env = (tc.tc_prims ())
in (

let _91_338 = (tc_deps [] env filenames [])
in (match (_91_338) with
| (stack, env, ts) -> begin
if (((FStar_Options.universes ()) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) && (FStar_Option.isSome filename)) then begin
(let _186_283 = (FStar_Option.get filename)
in (FStar_SMTEncoding_Solver.with_hints_db _186_283 (fun _91_339 -> (match (()) with
| () -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) stack initial_mod env ts)
end))))
end else begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) stack initial_mod env ts)
end
end)))))))))




