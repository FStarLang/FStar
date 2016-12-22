
open Prims

type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  FStar_Parser_ParseIt.input_frag  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit; tc_prims : Prims.unit  ->  'env; tc_one_file : Prims.string Prims.list  ->  'env  ->  ((Prims.string Prims.option * Prims.string) * 'env * 'modul * Prims.string Prims.list); cleanup : 'env  ->  Prims.unit}


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
| Push (_93_16) -> begin
_93_16
end))


let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_93_19) -> begin
_93_19
end))


let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_93_22) -> begin
_93_22
end))


type ('env, 'modul) stack =
('env * 'modul) Prims.list


type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))


let the_interactive_state : interactive_state = (let _190_194 = (FStar_Util.new_string_builder ())
in (let _190_193 = (FStar_ST.alloc None)
in (let _190_192 = (FStar_ST.alloc [])
in (let _190_191 = (FStar_ST.alloc None)
in {chunk = _190_194; stdin = _190_193; buffer = _190_192; log = _190_191}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun _93_30 -> (match (()) with
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

let _93_36 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (

let _93_40 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _93_42 -> ())
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

let _93_49 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
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

let _93_56 = (log line)
in (

let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (_93_62)::(ok)::(fail)::[] -> begin
((ok), (fail))
end
| _93_65 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in (

let _93_68 = (FStar_Util.clear_string_builder s.chunk)
in Code (((str), (responses))))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(

let _93_70 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(

let _93_72 = (FStar_Util.clear_string_builder s.chunk)
in (

let lc_lax = (let _190_202 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string _190_202))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l)::(c)::("#lax")::[] -> begin
(let _190_204 = (FStar_Util.int_of_string l)
in (let _190_203 = (FStar_Util.int_of_string c)
in ((true), (_190_204), (_190_203))))
end
| (l)::(c)::[] -> begin
(let _190_206 = (FStar_Util.int_of_string l)
in (let _190_205 = (FStar_Util.int_of_string c)
in ((false), (_190_206), (_190_205))))
end
| _93_83 -> begin
(

let _93_84 = (FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax))
in ((false), ((Prims.parse_int "1")), ((Prims.parse_int "0"))))
end)
in Push (lc))))
end else begin
if (l = "#finish") then begin
(FStar_All.exit (Prims.parse_int "0"))
end else begin
(

let _93_87 = (FStar_Util.string_builder_append s.chunk line)
in (

let _93_89 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))


let shift_chunk : Prims.unit  ->  input_chunks = (fun _93_91 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
(

let _93_97 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun _93_99 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (let _190_214 = (let _190_213 = (FStar_ST.read s.buffer)
in (let _190_212 = (let _190_211 = (read_chunk ())
in (_190_211)::[])
in (FStar_List.append _190_213 _190_212)))
in (FStar_ST.op_Colon_Equals s.buffer _190_214)))
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
| Found (_93_102) -> begin
_93_102
end))


let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _93_103 -> (match (()) with
| () -> begin
(

let _93_104 = (fill_buffer ())
in (

let _93_106 = (fill_buffer ())
in try
(match (()) with
| () -> begin
(

let _93_130 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| (Push (_93_121))::(Code (code, _93_117))::[] -> begin
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
| _93_129 -> begin
()
end)
in None)
end)
with
| Found (n) -> begin
Some (n)
end))
end))


let detect_dependencies_for_module : Prims.string Prims.option  ->  (Prims.string * Prims.string * Prims.string Prims.list) = (fun mname -> (

let failr = (fun msg r -> (

let _93_136 = if (FStar_Options.universes ()) then begin
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
(match (mname) with
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
(let _190_234 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in (fail _190_234))
end
| (Some (None, Some (filename))) | (Some (Some (filename), None)) -> begin
(

let _93_170 = (FStar_Options.add_verify_module module_name)
in (

let _93_177 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyUserList ((filename)::[]))
in (match (_93_177) with
| (_93_173, all_filenames, _93_176) -> begin
(let _190_236 = (let _190_235 = (FStar_List.tl all_filenames)
in (FStar_List.rev _190_235))
in ((filename), (module_name), (_190_236)))
end)))
end
| Some (Some (_93_179), Some (_93_182)) -> begin
(let _190_237 = (FStar_Util.format1 "The combination of split interfaces and interactive verification is not supported for: %s\n" module_name)
in (fail _190_237))
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
end))))


let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  (Prims.string * Prims.string * Prims.string Prims.list) = (fun _93_190 -> (match (()) with
| () -> begin
(let _190_241 = (find_initial_module_name ())
in (detect_dependencies_for_module _190_241))
end))


type m_timestamps =
(Prims.string Prims.option * Prims.string * FStar_Util.time Prims.option * FStar_Util.time) Prims.list


let interactive_mode = (fun filename modname verify_mode filenames initial_mod tc -> (

let _93_199 = if (let _190_248 = (FStar_Options.codegen ())
in (FStar_Option.isSome _190_248)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (

let rec tc_deps = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| _93_209 -> begin
(

let stack = (((env), (m)))::stack
in (

let env = (let _190_259 = (FStar_Options.lax ())
in (tc.push env _190_259 true "typecheck_modul"))
in (

let _93_218 = (tc.tc_one_file remaining env)
in (match (_93_218) with
| ((intf, impl), env, modl, remaining) -> begin
(

let _93_226 = (

let intf_t = (match (intf) with
| Some (intf) -> begin
(let _190_260 = (FStar_Util.get_file_last_modification_time intf)
in Some (_190_260))
end
| None -> begin
None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (_93_226) with
| (intf_t, impl_t) -> begin
(tc_deps m stack env remaining ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))
in (

let update_deps = (fun m stk env ts -> (

let is_stale = (fun intf impl intf_t impl_t -> (

let impl_mt = (FStar_Util.get_file_last_modification_time impl)
in ((FStar_Util.is_before impl_t impl_mt) || (match (((intf), (intf_t))) with
| (Some (intf), Some (intf_t)) -> begin
(

let intf_mt = (FStar_Util.get_file_last_modification_time intf)
in (FStar_Util.is_before intf_t intf_mt))
end
| (None, None) -> begin
false
end
| (_93_248, _93_250) -> begin
(FStar_All.failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts good_stack good_ts -> (

let match_dep = (fun depnames intf impl -> (match (intf) with
| None -> begin
(match (depnames) with
| (dep)::depnames' -> begin
if (dep = impl) then begin
((true), (depnames'))
end else begin
((false), (depnames))
end
end
| _93_268 -> begin
((false), (depnames))
end)
end
| Some (intf) -> begin
(match (depnames) with
| (depintf)::(dep)::depnames' -> begin
if ((depintf = intf) && (dep = impl)) then begin
((true), (depnames'))
end else begin
((false), (depnames))
end
end
| _93_277 -> begin
((false), (depnames))
end)
end))
in (

let rec pop_tc_and_stack = (fun env stack ts -> (match (ts) with
| [] -> begin
env
end
| (_93_285)::ts -> begin
(

let _93_287 = (tc.pop env "")
in (

let _93_294 = (let _190_302 = (FStar_List.hd stack)
in (let _190_301 = (FStar_List.tl stack)
in ((_190_302), (_190_301))))
in (match (_93_294) with
| ((env, _93_291), stack) -> begin
(pop_tc_and_stack env stack ts)
end)))
end))
in (match (ts) with
| (ts_elt)::ts' -> begin
(

let _93_302 = ts_elt
in (match (_93_302) with
| (intf, impl, intf_t, impl_t) -> begin
(

let _93_305 = (match_dep depnames intf impl)
in (match (_93_305) with
| (b, depnames') -> begin
if ((not (b)) || (is_stale intf impl intf_t impl_t)) then begin
(

let env = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts)
in (tc_deps m good_stack env depnames good_ts))
end else begin
(

let _93_309 = (let _190_304 = (FStar_List.hd st)
in (let _190_303 = (FStar_List.tl st)
in ((_190_304), (_190_303))))
in (match (_93_309) with
| (stack_elt, st') -> begin
(iterate depnames' st' env' ts' ((stack_elt)::good_stack) ((ts_elt)::good_ts))
end))
end
end))
end))
end
| [] -> begin
(tc_deps m good_stack env' depnames good_ts)
end))))
in (

let _93_316 = (detect_dependencies_for_module modname)
in (match (_93_316) with
| (_93_312, _93_314, filenames) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] []))
end)))))
in (

let rec go = (fun line_col stack curmod env ts -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(

let _93_326 = (tc.pop env msg)
in (

let _93_338 = (match (stack) with
| [] -> begin
(

let _93_329 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit (Prims.parse_int "1")))
end
| (hd)::tl -> begin
((hd), (tl))
end)
in (match (_93_338) with
| ((env, curmod), stack) -> begin
(

let _93_339 = if ((FStar_List.length stack) = (FStar_List.length ts)) then begin
(tc.cleanup env)
end else begin
()
end
in (go line_col stack curmod env ts))
end)))
end
| Push (lax, l, c) -> begin
(

let _93_351 = if ((FStar_List.length stack) = (FStar_List.length ts)) then begin
(let _190_315 = (update_deps curmod stack env ts)
in ((true), (_190_315)))
end else begin
((false), (((stack), (env), (ts))))
end
in (match (_93_351) with
| (restore_cmd_line_options, (stack, env, ts)) -> begin
(

let stack = (((env), (curmod)))::stack
in (

let env = (tc.push env lax restore_cmd_line_options "#push")
in (go ((l), (c)) stack curmod env ts)))
end))
end
| Code (text, (ok, fail)) -> begin
(

let fail = (fun curmod env_mark -> (

let _93_363 = (tc.report_fail ())
in (

let _93_365 = (FStar_Util.print1 "%s\n" fail)
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

let _93_376 = (FStar_Util.print1 "\n%s\n" ok)
in (

let env = (tc.commit_mark env)
in (go line_col stack curmod env ts)))
end else begin
(fail curmod env_mark)
end
end
| _93_380 -> begin
(fail curmod env_mark)
end)))))
end))
in (

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let env = (tc.tc_prims ())
in (

let _93_386 = (tc_deps initial_mod [] env filenames [])
in (match (_93_386) with
| (stack, env, ts) -> begin
if (((FStar_Options.universes ()) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) && (FStar_Option.isSome filename)) then begin
(let _190_321 = (FStar_Option.get filename)
in (FStar_SMTEncoding_Solver.with_hints_db _190_321 (fun _93_387 -> (match (()) with
| () -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) stack initial_mod env ts)
end))))
end else begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) stack initial_mod env ts)
end
end)))))))))




