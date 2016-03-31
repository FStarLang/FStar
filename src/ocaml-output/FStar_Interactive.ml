
open Prims

type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  Prims.string  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit}


let is_Mkinteractive_tc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_tc"))))


type input_chunks =
| Push of Prims.string
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
| Push (_85_13) -> begin
_85_13
end))


let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_85_16) -> begin
_85_16
end))


let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_85_19) -> begin
_85_19
end))


type ('env, 'modul) stack =
('env * 'modul) Prims.list


type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))


let the_interactive_state : interactive_state = (let _174_149 = (FStar_Util.new_string_builder ())
in (let _174_148 = (FStar_ST.alloc None)
in (let _174_147 = (FStar_ST.alloc [])
in (let _174_146 = (FStar_ST.alloc None)
in {chunk = _174_149; stdin = _174_148; buffer = _174_147; log = _174_146}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun _85_27 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (

let log = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(

let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in (

let _85_33 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (

let _85_37 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _85_39 -> ())
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

let _85_46 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (

let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (

let _85_53 = (log line)
in (

let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(

let responses = (match ((FStar_Util.split l " ")) with
| _85_59::ok::fail::[] -> begin
(ok, fail)
end
| _85_62 -> begin
("ok", "fail")
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in (

let _85_65 = (FStar_Util.clear_string_builder s.chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(

let _85_67 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(

let _85_69 = (FStar_Util.clear_string_builder s.chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(

let _85_71 = (FStar_Util.string_builder_append s.chunk line)
in (

let _85_73 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))


let shift_chunk : Prims.unit  ->  input_chunks = (fun _85_75 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| chunk::chunks -> begin
(

let _85_81 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun _85_83 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (let _174_164 = (let _174_163 = (FStar_ST.read s.buffer)
in (let _174_162 = (let _174_161 = (read_chunk ())
in (_174_161)::[])
in (FStar_List.append _174_163 _174_162)))
in (FStar_ST.op_Colon_Equals s.buffer _174_164)))
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
| Found (_85_86) -> begin
_85_86
end))


let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _85_87 -> (match (()) with
| () -> begin
(

let _85_88 = (fill_buffer ())
in (

let _85_90 = (fill_buffer ())
in try
(match (()) with
| () -> begin
(

let _85_114 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| Push (_85_105)::Code (code, _85_101)::[] -> begin
(

let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (

let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > 7) && ((FStar_Util.substring line 0 6) = "module")) then begin
(

let module_name = (FStar_Util.substring line 7 ((FStar_String.length line) - 7))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _85_113 -> begin
()
end)
in None)
end)
with
| Found (n) -> begin
Some (n)
end))
end))


let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  Prims.string Prims.list = (fun _85_116 -> (match (()) with
| () -> begin
try
(match (()) with
| () -> begin
(

let fail = (fun msg -> if (FStar_ST.read FStar_Options.universes) then begin
(Prims.raise (FStar_Syntax_Syntax.Err (msg)))
end else begin
(Prims.raise (FStar_Absyn_Syntax.Err (msg)))
end)
in (match ((find_initial_module_name ())) with
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
(let _174_180 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in (fail _174_180))
end
| Some (filename) -> begin
(

let _85_152 = (FStar_ST.op_Colon_Equals FStar_Options.verify_module ((module_name)::[]))
in (

let _85_157 = (FStar_Parser_Dep.collect ((filename)::[]))
in (match (_85_157) with
| (_85_155, all_filenames) -> begin
(let _174_181 = (FStar_List.tl all_filenames)
in (FStar_List.rev _174_181))
end)))
end)))
end))
end)
with
| FStar_Syntax_Syntax.Error (msg, r) -> begin
(

let _85_124 = (FStar_TypeChecker_Errors.warn r msg)
in (

let _85_126 = (FStar_TypeChecker_Errors.warn r (Prims.strcat "Dependency analysis may not be correct because the file failed to parse: " msg))
in []))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(

let _85_132 = (FStar_Tc_Errors.warn r msg)
in (

let _85_134 = (FStar_Tc_Errors.warn r (Prims.strcat "Dependency analysis may not be correct because the file failed to parse: " msg))
in []))
end
| _85_137 -> begin
(

let _85_138 = (FStar_Tc_Errors.warn FStar_Range.dummyRange "Dependency analysis may not be correct because the file failed to parse: ")
in [])
end
end))


let interactive_mode = (fun env initial_mod tc -> (

let _85_163 = if (let _174_186 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _174_186)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (

let rec go = (fun stack curmod env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(

let _85_171 = (tc.pop env msg)
in (

let _85_183 = (match (stack) with
| [] -> begin
(

let _85_174 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit 1))
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_85_183) with
| ((env, curmod), stack) -> begin
(go stack curmod env)
end)))
end
| Push (msg) -> begin
(

let stack = ((env, curmod))::stack
in (

let env = (tc.push env msg)
in (go stack curmod env)))
end
| Code (text, (ok, fail)) -> begin
(

let fail = (fun curmod env_mark -> (

let _85_197 = (tc.report_fail ())
in (

let _85_199 = (FStar_Util.print1 "%s\n" fail)
in (

let env = (tc.reset_mark env_mark)
in (go stack curmod env)))))
in (

let env_mark = (tc.mark env)
in (

let res = (tc.check_frag env_mark curmod text)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
if (n_errs = 0) then begin
(

let _85_209 = (FStar_Util.print1 "\n%s\n" ok)
in (

let env = (tc.commit_mark env)
in (go stack curmod env)))
end else begin
(fail curmod env_mark)
end
end
| _85_213 -> begin
(fail curmod env_mark)
end))))
end))
in (go [] initial_mod env))))




