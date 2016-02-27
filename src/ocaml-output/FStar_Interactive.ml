
open Prims
# 28 "FStar.Interactive.fst"
type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  Prims.string  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit}

# 28 "FStar.Interactive.fst"
let is_Mkinteractive_tc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_tc"))))

# 41 "FStar.Interactive.fst"
type input_chunks =
| Push of Prims.string
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))

# 42 "FStar.Interactive.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 43 "FStar.Interactive.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.Interactive.fst"
let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Interactive.fst"
let ___Push____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Push (_78_13) -> begin
_78_13
end))

# 43 "FStar.Interactive.fst"
let ___Pop____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Pop (_78_16) -> begin
_78_16
end))

# 44 "FStar.Interactive.fst"
let ___Code____0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_78_19) -> begin
_78_19
end))

# 46 "FStar.Interactive.fst"
type ('env, 'modul) stack =
('env * 'modul) Prims.list

# 48 "FStar.Interactive.fst"
type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}

# 48 "FStar.Interactive.fst"
let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))

# 56 "FStar.Interactive.fst"
let the_interactive_state : interactive_state = (let _160_149 = (FStar_Util.new_string_builder ())
in (let _160_148 = (FStar_ST.alloc None)
in (let _160_147 = (FStar_ST.alloc [])
in (let _160_146 = (FStar_ST.alloc None)
in {chunk = _160_149; stdin = _160_148; buffer = _160_147; log = _160_146}))))

# 66 "FStar.Interactive.fst"
let rec read_chunk : Prims.unit  ->  input_chunks = (fun _78_27 -> (match (()) with
| () -> begin
(
# 67 "FStar.Interactive.fst"
let s = the_interactive_state
in (
# 68 "FStar.Interactive.fst"
let log = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(
# 70 "FStar.Interactive.fst"
let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(
# 74 "FStar.Interactive.fst"
let transcript = (FStar_Util.open_file_for_writing "transcript")
in (
# 75 "FStar.Interactive.fst"
let _78_33 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (
# 79 "FStar.Interactive.fst"
let _78_37 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _78_39 -> ())
end
in (
# 84 "FStar.Interactive.fst"
let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(
# 88 "FStar.Interactive.fst"
let i = (FStar_Util.open_stdin ())
in (
# 89 "FStar.Interactive.fst"
let _78_46 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (
# 92 "FStar.Interactive.fst"
let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (
# 97 "FStar.Interactive.fst"
let _78_53 = (log line)
in (
# 99 "FStar.Interactive.fst"
let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(
# 101 "FStar.Interactive.fst"
let responses = (match ((FStar_Util.split l " ")) with
| _78_59::ok::fail::[] -> begin
(ok, fail)
end
| _78_62 -> begin
("ok", "fail")
end)
in (
# 105 "FStar.Interactive.fst"
let str = (FStar_Util.string_of_string_builder s.chunk)
in (
# 106 "FStar.Interactive.fst"
let _78_65 = (FStar_Util.clear_string_builder s.chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(
# 108 "FStar.Interactive.fst"
let _78_67 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(
# 109 "FStar.Interactive.fst"
let _78_69 = (FStar_Util.clear_string_builder s.chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(
# 112 "FStar.Interactive.fst"
let _78_71 = (FStar_Util.string_builder_append s.chunk line)
in (
# 113 "FStar.Interactive.fst"
let _78_73 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))

# 116 "FStar.Interactive.fst"
let shift_chunk : Prims.unit  ->  input_chunks = (fun _78_75 -> (match (()) with
| () -> begin
(
# 117 "FStar.Interactive.fst"
let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| chunk::chunks -> begin
(
# 121 "FStar.Interactive.fst"
let _78_81 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))

# 124 "FStar.Interactive.fst"
let fill_buffer : Prims.unit  ->  Prims.unit = (fun _78_83 -> (match (()) with
| () -> begin
(
# 125 "FStar.Interactive.fst"
let s = the_interactive_state
in (let _160_164 = (let _160_163 = (FStar_ST.read s.buffer)
in (let _160_162 = (let _160_161 = (read_chunk ())
in (_160_161)::[])
in (FStar_List.append _160_163 _160_162)))
in (FStar_ST.op_Colon_Equals s.buffer _160_164)))
end))

# 128 "FStar.Interactive.fst"
exception Found of (Prims.string)

# 128 "FStar.Interactive.fst"
let is_Found = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "FStar.Interactive.fst"
let ___Found____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Found (_78_86) -> begin
_78_86
end))

# 129 "FStar.Interactive.fst"
let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _78_87 -> (match (()) with
| () -> begin
(
# 130 "FStar.Interactive.fst"
let _78_88 = (fill_buffer ())
in (
# 130 "FStar.Interactive.fst"
let _78_90 = (fill_buffer ())
in (FStar_All.try_with (fun _78_93 -> (match (()) with
| () -> begin
(
# 131 "FStar.Interactive.fst"
let _78_114 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| Push (_78_105)::Code (code, _78_101)::[] -> begin
(
# 133 "FStar.Interactive.fst"
let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (
# 135 "FStar.Interactive.fst"
let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > 7) && ((FStar_Util.substring line 0 6) = "module")) then begin
(
# 137 "FStar.Interactive.fst"
let module_name = (FStar_Util.substring line 7 ((FStar_String.length line) - 7))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _78_113 -> begin
()
end)
in None)
end)) (fun _78_92 -> (match (_78_92) with
| Found (n) -> begin
Some (n)
end)))))
end))

# 147 "FStar.Interactive.fst"
let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  Prims.string Prims.list = (fun _78_116 -> (match (()) with
| () -> begin
(
# 148 "FStar.Interactive.fst"
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
# 156 "FStar.Interactive.fst"
let file_of_module_name = (FStar_Parser_Dep.build_map [])
in (
# 157 "FStar.Interactive.fst"
let filename = (FStar_Util.smap_try_find file_of_module_name (FStar_String.lowercase module_name))
in (match (filename) with
| None -> begin
(let _160_179 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in (fail _160_179))
end
| Some (filename) -> begin
(
# 163 "FStar.Interactive.fst"
let _78_130 = (FStar_Parser_Dep.collect ((filename)::[]))
in (match (_78_130) with
| (_78_128, all_filenames) -> begin
(let _160_180 = (FStar_List.tl all_filenames)
in (FStar_List.rev _160_180))
end))
end)))
end))
end))

# 170 "FStar.Interactive.fst"
let interactive_mode = (fun env initial_mod tc -> (
# 171 "FStar.Interactive.fst"
let _78_136 = if (let _160_184 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _160_184)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (
# 173 "FStar.Interactive.fst"
let rec go = (fun stack curmod env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(
# 176 "FStar.Interactive.fst"
let _78_144 = (tc.pop env msg)
in (
# 177 "FStar.Interactive.fst"
let _78_156 = (match (stack) with
| [] -> begin
(
# 179 "FStar.Interactive.fst"
let _78_147 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit 1))
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_78_156) with
| ((env, curmod), stack) -> begin
(go stack curmod env)
end)))
end
| Push (msg) -> begin
(
# 184 "FStar.Interactive.fst"
let stack = ((env, curmod))::stack
in (
# 185 "FStar.Interactive.fst"
let env = (tc.push env msg)
in (go stack curmod env)))
end
| Code (text, (ok, fail)) -> begin
(
# 189 "FStar.Interactive.fst"
let fail = (fun curmod env_mark -> (
# 190 "FStar.Interactive.fst"
let _78_170 = (tc.report_fail ())
in (
# 191 "FStar.Interactive.fst"
let _78_172 = (FStar_Util.print1 "%s\n" fail)
in (
# 192 "FStar.Interactive.fst"
let env = (tc.reset_mark env_mark)
in (go stack curmod env)))))
in (
# 195 "FStar.Interactive.fst"
let env_mark = (tc.mark env)
in (
# 196 "FStar.Interactive.fst"
let res = (tc.check_frag env_mark curmod text)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
if (n_errs = 0) then begin
(
# 200 "FStar.Interactive.fst"
let _78_182 = (FStar_Util.print1 "\n%s\n" ok)
in (
# 201 "FStar.Interactive.fst"
let env = (tc.commit_mark env)
in (go stack curmod env)))
end else begin
(fail curmod env_mark)
end
end
| _78_186 -> begin
(fail curmod env_mark)
end))))
end))
in (go [] initial_mod env))))




