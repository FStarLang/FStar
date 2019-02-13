
open Prims
open FStar_Pervasives

let tc_one_file : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  ((Prims.string FStar_Pervasives_Native.option * Prims.string) * FStar_TypeChecker_Env.env_t * Prims.string Prims.list) = (fun remaining env -> (

let uu____34 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____79 = (FStar_Universal.tc_one_file_for_ide env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____79) with
| (uu____102, env1) -> begin
((((FStar_Pervasives_Native.Some (intf)), (impl))), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____127 = (FStar_Universal.tc_one_file_for_ide env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____127) with
| (uu____150, env1) -> begin
((((FStar_Pervasives_Native.None), (intf_or_impl))), (env1), (remaining1))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____34) with
| ((intf, impl), env1, remaining1) -> begin
((((intf), (impl))), (env1), (remaining1))
end)))


type env_t =
FStar_TypeChecker_Env.env


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let pop : FStar_TypeChecker_Env.env  ->  Prims.string  ->  unit = (fun env msg -> ((

let uu____267 = (FStar_TypeChecker_Tc.pop_context env msg)
in ());
(FStar_Options.pop ());
))


let push_with_kind : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env lax1 restore_cmd_line_options1 msg -> (

let env1 = (

let uu___462_296 = env
in {FStar_TypeChecker_Env.solver = uu___462_296.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___462_296.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___462_296.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___462_296.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___462_296.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___462_296.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___462_296.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___462_296.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___462_296.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___462_296.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___462_296.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___462_296.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___462_296.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___462_296.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___462_296.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___462_296.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___462_296.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___462_296.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___462_296.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___462_296.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___462_296.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___462_296.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___462_296.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___462_296.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___462_296.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___462_296.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___462_296.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___462_296.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___462_296.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___462_296.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___462_296.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___462_296.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___462_296.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___462_296.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___462_296.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___462_296.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___462_296.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___462_296.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___462_296.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___462_296.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___462_296.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___462_296.FStar_TypeChecker_Env.nbe})
in (

let res = (FStar_TypeChecker_Tc.push_context env1 msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____301 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____301 (fun a1 -> ())))
end
| uu____303 -> begin
()
end);
res;
))))


let check_frag : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env_t * Prims.int) FStar_Pervasives_Native.option = (fun env curmod frag -> (FStar_All.try_with (fun uu___464_352 -> (match (()) with
| () -> begin
(

let uu____364 = (FStar_Universal.tc_one_fragment curmod env frag)
in (match (uu____364) with
| (m, env1) -> begin
(

let uu____388 = (

let uu____398 = (FStar_Errors.get_err_count ())
in ((m), (env1), (uu____398)))
in FStar_Pervasives_Native.Some (uu____388))
end))
end)) (fun uu___463_417 -> (match (uu___463_417) with
| FStar_Errors.Error (e, msg, r) when (

let uu____434 = (FStar_Options.trace_error ())
in (not (uu____434))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((e), (msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (e, msg) when (

let uu____465 = (FStar_Options.trace_error ())
in (not (uu____465))) -> begin
((

let uu____468 = (

let uu____478 = (

let uu____486 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____486)))
in (uu____478)::[])
in (FStar_TypeChecker_Err.add_errors env uu____468));
FStar_Pervasives_Native.None;
)
end))))


let report_fail : unit  ->  unit = (fun uu____516 -> ((

let uu____518 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____518 (fun a2 -> ())));
(FStar_Errors.clear ());
))

type input_chunks =
| Push of (Prims.bool * Prims.int * Prims.int)
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))
| Info of (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option)
| Completions of Prims.string


let uu___is_Push : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____608 -> begin
false
end))


let __proj__Push__item___0 : input_chunks  ->  (Prims.bool * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
_0
end))


let uu___is_Pop : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop (_0) -> begin
true
end
| uu____656 -> begin
false
end))


let __proj__Pop__item___0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Pop (_0) -> begin
_0
end))


let uu___is_Code : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Code (_0) -> begin
true
end
| uu____690 -> begin
false
end))


let __proj__Code__item___0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_0) -> begin
_0
end))


let uu___is_Info : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Info (_0) -> begin
true
end
| uu____762 -> begin
false
end))


let __proj__Info__item___0 : input_chunks  ->  (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Info (_0) -> begin
_0
end))


let uu___is_Completions : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Completions (_0) -> begin
true
end
| uu____840 -> begin
false
end))


let __proj__Completions__item___0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Completions (_0) -> begin
_0
end))

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref}


let __proj__Mkinteractive_state__item__chunk : interactive_state  ->  FStar_Util.string_builder = (fun projectee -> (match (projectee) with
| {chunk = chunk; stdin = stdin; buffer = buffer; log = log1} -> begin
chunk
end))


let __proj__Mkinteractive_state__item__stdin : interactive_state  ->  FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {chunk = chunk; stdin = stdin; buffer = buffer; log = log1} -> begin
stdin
end))


let __proj__Mkinteractive_state__item__buffer : interactive_state  ->  input_chunks Prims.list FStar_ST.ref = (fun projectee -> (match (projectee) with
| {chunk = chunk; stdin = stdin; buffer = buffer; log = log1} -> begin
buffer
end))


let __proj__Mkinteractive_state__item__log : interactive_state  ->  FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {chunk = chunk; stdin = stdin; buffer = buffer; log = log1} -> begin
log1
end))


let the_interactive_state : interactive_state = (

let uu____1160 = (FStar_Util.new_string_builder ())
in (

let uu____1161 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____1168 = (FStar_Util.mk_ref [])
in (

let uu____1175 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {chunk = uu____1160; stdin = uu____1161; buffer = uu____1168; log = uu____1175}))))


let rec read_chunk : unit  ->  input_chunks = (fun uu____1253 -> (

let s = the_interactive_state
in (

let log1 = (

let uu____1261 = (FStar_Options.debug_any ())
in (match (uu____1261) with
| true -> begin
(

let transcript = (

let uu____1269 = (FStar_ST.op_Bang s.log)
in (match (uu____1269) with
| FStar_Pervasives_Native.Some (transcript) -> begin
transcript
end
| FStar_Pervasives_Native.None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in ((FStar_ST.op_Colon_Equals s.log (FStar_Pervasives_Native.Some (transcript)));
transcript;
))
end))
in (fun line -> ((FStar_Util.append_to_file transcript line);
(FStar_Util.flush_file transcript);
)))
end
| uu____1325 -> begin
(fun uu____1327 -> ())
end))
in (

let stdin = (

let uu____1330 = (FStar_ST.op_Bang s.stdin)
in (match (uu____1330) with
| FStar_Pervasives_Native.Some (i) -> begin
i
end
| FStar_Pervasives_Native.None -> begin
(

let i = (FStar_Util.open_stdin ())
in ((FStar_ST.op_Colon_Equals s.stdin (FStar_Pervasives_Native.Some (i)));
i;
))
end))
in (

let line = (

let uu____1384 = (FStar_Util.read_line stdin)
in (match (uu____1384) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (l) -> begin
l
end))
in ((log1 line);
(

let l = (FStar_Util.trim_string line)
in (match ((FStar_Util.starts_with l "#end")) with
| true -> begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (uu____1414)::(ok)::(fail1)::[] -> begin
((ok), (fail1))
end
| uu____1426 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____1444 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____1449 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____1456 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____1456))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l1)::(c)::("#lax")::[] -> begin
(

let uu____1488 = (FStar_Util.int_of_string l1)
in (

let uu____1490 = (FStar_Util.int_of_string c)
in ((true), (uu____1488), (uu____1490))))
end
| (l1)::(c)::[] -> begin
(

let uu____1503 = (FStar_Util.int_of_string l1)
in (

let uu____1505 = (FStar_Util.int_of_string c)
in ((false), (uu____1503), (uu____1505))))
end
| uu____1511 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_WrongErrorLocation), ((Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax))));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____1524 -> begin
(match ((FStar_Util.starts_with l "#info ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1529)::(symbol)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Info (((symbol), (true), (FStar_Pervasives_Native.None)));
)
end
| (uu____1560)::(symbol)::(file)::(row)::(col)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let uu____1577 = (

let uu____1597 = (

let uu____1609 = (

let uu____1619 = (FStar_Util.int_of_string row)
in (

let uu____1621 = (FStar_Util.int_of_string col)
in ((file), (uu____1619), (uu____1621))))
in FStar_Pervasives_Native.Some (uu____1609))
in ((symbol), (false), (uu____1597)))
in Info (uu____1577));
)
end
| uu____1649 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDEUnrecognized), ((Prims.strcat "Unrecognized \"#info\" request: " l))));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1657 -> begin
(match ((FStar_Util.starts_with l "#completions ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1662)::(prefix1)::("#")::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Completions (prefix1);
)
end
| uu____1672 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDEUnrecognized), ((Prims.strcat "Unrecognized \"#completions\" request: " l))));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1680 -> begin
(match ((Prims.op_Equality l "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____1686 -> begin
((FStar_Util.string_builder_append s.chunk line);
(FStar_Util.string_builder_append s.chunk "\n");
(read_chunk ());
)
end)
end)
end)
end)
end)
end));
))))))


let shift_chunk : unit  ->  input_chunks = (fun uu____1696 -> (

let s = the_interactive_state
in (

let uu____1698 = (FStar_ST.op_Bang s.buffer)
in (match (uu____1698) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.op_Colon_Equals s.buffer chunks);
chunk;
)
end))))


let fill_buffer : unit  ->  unit = (fun uu____1757 -> (

let s = the_interactive_state
in (

let uu____1759 = (

let uu____1762 = (FStar_ST.op_Bang s.buffer)
in (

let uu____1788 = (

let uu____1791 = (read_chunk ())
in (uu____1791)::[])
in (FStar_List.append uu____1762 uu____1788)))
in (FStar_ST.op_Colon_Equals s.buffer uu____1759))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option * FStar_Parser_Dep.deps) = (fun filename -> (

let uu____1835 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____1835) with
| (deps, dep_graph1) -> begin
(

let uu____1865 = (FStar_List.partition (fun x -> (

let uu____1882 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____1884 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____1882 uu____1884)))) deps)
in (match (uu____1865) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____1928 = ((

let uu____1932 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____1932))) || (

let uu____1935 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____1935))))
in (match (uu____1928) with
| true -> begin
(

let uu____1938 = (

let uu____1944 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in ((FStar_Errors.Warning_MissingInterfaceOrImplementation), (uu____1944)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1938))
end
| uu____1948 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____1956 -> begin
((

let uu____1961 = (

let uu____1967 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in ((FStar_Errors.Warning_UnexpectedFile), (uu____1967)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1961));
FStar_Pervasives_Native.None;
)
end)
in ((deps1), (maybe_intf), (dep_graph1)))
end))
end)))


type m_timestamps =
(Prims.string FStar_Pervasives_Native.option * Prims.string * FStar_Util.time FStar_Pervasives_Native.option * FStar_Util.time) Prims.list


let rec tc_deps : modul_t  ->  stack_t  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  m_timestamps  ->  (stack_t * FStar_TypeChecker_Env.env * m_timestamps) = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| uu____2040 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____2056 = (FStar_Options.lax ())
in (push_with_kind env uu____2056 true "typecheck_modul"))
in (

let uu____2060 = (tc_one_file remaining env1)
in (match (uu____2060) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____2110 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____2125 = (FStar_Parser_ParseIt.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____2125))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Parser_ParseIt.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____2110) with
| (intf_t, impl_t) -> begin
(tc_deps m stack1 env2 remaining1 ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))


let update_deps : Prims.string  ->  modul_t  ->  stack_t  ->  env_t  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun filename m stk env ts -> (

let is_stale = (fun intf impl intf_t impl_t -> (

let impl_mt = (FStar_Parser_ParseIt.get_file_last_modification_time impl)
in ((FStar_Util.is_before impl_t impl_mt) || (match (((intf), (intf_t))) with
| (FStar_Pervasives_Native.Some (intf1), FStar_Pervasives_Native.Some (intf_t1)) -> begin
(

let intf_mt = (FStar_Parser_ParseIt.get_file_last_modification_time intf1)
in (FStar_Util.is_before intf_t1 intf_mt))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
false
end
| (uu____2264, uu____2265) -> begin
(failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts1 good_stack good_ts -> (

let match_dep = (fun depnames1 intf impl -> (match (intf) with
| FStar_Pervasives_Native.None -> begin
(match (depnames1) with
| (dep1)::depnames' -> begin
(match ((Prims.op_Equality dep1 impl)) with
| true -> begin
((true), (depnames'))
end
| uu____2406 -> begin
((false), (depnames1))
end)
end
| uu____2413 -> begin
((false), (depnames1))
end)
end
| FStar_Pervasives_Native.Some (intf1) -> begin
(match (depnames1) with
| (depintf)::(dep1)::depnames' -> begin
(match (((Prims.op_Equality depintf intf1) && (Prims.op_Equality dep1 impl))) with
| true -> begin
((true), (depnames'))
end
| uu____2459 -> begin
((false), (depnames1))
end)
end
| uu____2466 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____2549)::ts3 -> begin
((pop env1 "");
(

let uu____2597 = (

let uu____2612 = (FStar_List.hd stack)
in (

let uu____2621 = (FStar_List.tl stack)
in ((uu____2612), (uu____2621))))
in (match (uu____2597) with
| ((env2, uu____2643), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____2713 = ts_elt
in (match (uu____2713) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____2750 = (match_dep depnames intf impl)
in (match (uu____2750) with
| (b, depnames') -> begin
(

let uu____2775 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____2775) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____2793 -> begin
(

let uu____2795 = (

let uu____2804 = (FStar_List.hd st)
in (

let uu____2813 = (FStar_List.tl st)
in ((uu____2804), (uu____2813))))
in (match (uu____2795) with
| (stack_elt, st') -> begin
(iterate depnames' st' env' ts' ((stack_elt)::good_stack) ((ts_elt)::good_ts))
end))
end))
end))
end))
end
| [] -> begin
(tc_deps m good_stack env' depnames good_ts)
end))))
in (

let uu____2870 = (deps_of_our_file filename)
in (match (uu____2870) with
| (filenames, uu____2890, dep_graph1) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let format_info : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun env name typ range doc1 -> (

let uu____2993 = (FStar_Range.string_of_range range)
in (

let uu____2995 = (FStar_TypeChecker_Normalize.term_to_string env typ)
in (

let uu____2997 = (match (doc1) with
| FStar_Pervasives_Native.Some (docstring) -> begin
(FStar_Util.format1 "#doc %s" docstring)
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2993 name uu____2995 uu____2997)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  unit = (fun line_col filename stack curmod env ts -> (

let uu____3052 = (shift_chunk ())
in (match (uu____3052) with
| Info (symbol, fqn_only, pos_opt) -> begin
(

let info_at_pos_opt = (match (pos_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos env file row col)
end)
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____3174) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3235 -> begin
(

let lid = (

let uu____3238 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split symbol "."))
in (FStar_Ident.lid_of_ids uu____3238))
in (

let lid1 = (match (fqn_only) with
| true -> begin
lid
end
| uu____3245 -> begin
(

let uu____3247 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____3247) with
| FStar_Pervasives_Native.None -> begin
lid
end
| FStar_Pervasives_Native.Some (lid1) -> begin
lid1
end))
end)
in (

let uu____3251 = (FStar_TypeChecker_Env.try_lookup_lid env lid1)
in (FStar_All.pipe_right uu____3251 (FStar_Util.map_option (fun uu____3308 -> (match (uu____3308) with
| ((uu____3328, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end)))))))
end)
end)
in ((match (info_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "\n#done-nok\n")
end
| FStar_Pervasives_Native.Some (name_or_lid, typ, rng) -> begin
(

let uu____3378 = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
((name), (FStar_Pervasives_Native.None))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____3405 = (FStar_Ident.string_of_lid lid)
in (

let uu____3407 = (

let uu____3411 = (FStar_Syntax_DsEnv.try_lookup_doc env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____3411 (FStar_Util.map_option FStar_Pervasives_Native.fst)))
in ((uu____3405), (uu____3407))))
end)
in (match (uu____3378) with
| (name, doc1) -> begin
(

let uu____3482 = (format_info env name typ rng doc1)
in (FStar_Util.print1 "%s\n#done-ok\n" uu____3482))
end))
end);
(go line_col filename stack curmod env ts);
)))
end
| Completions (search_term) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____3531) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____3551, []) -> begin
FStar_Pervasives_Native.None
end
| ((hs)::ts1, (hc)::tc1) -> begin
(

let hc_text = (FStar_Ident.text_of_id hc)
in (match ((FStar_Util.starts_with hc_text hs)) with
| true -> begin
(match (ts1) with
| [] -> begin
FStar_Pervasives_Native.Some (((candidate), ((FStar_String.length hs))))
end
| uu____3615 -> begin
(

let uu____3619 = (measure_anchored_match ts1 tc1)
in (FStar_All.pipe_right uu____3619 (FStar_Util.map_option (fun uu____3664 -> (match (uu____3664) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____3691 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____3734 = (measure_anchored_match needle candidate)
in (match (uu____3734) with
| FStar_Pervasives_Native.Some (matched, n1) -> begin
FStar_Pervasives_Native.Some ((([]), (matched), (n1)))
end
| FStar_Pervasives_Native.None -> begin
(match (candidate) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hc)::tc1 -> begin
(

let uu____3823 = (locate_match needle tc1)
in (FStar_All.pipe_right uu____3823 (FStar_Util.map_option (fun uu____3889 -> (match (uu____3889) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____3941 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____3941)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____4005 -> (match (uu____4005) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____4045)::[] -> begin
true
end
| uu____4047 -> begin
false
end)
in (

let uu____4051 = (FStar_Syntax_DsEnv.shorten_module_path env.FStar_TypeChecker_Env.dsenv prefix1 naked_match)
in (match (uu____4051) with
| (stripped_ns, shortened) -> begin
(

let uu____4082 = (str_of_ids shortened)
in (

let uu____4084 = (str_of_ids matched)
in (

let uu____4086 = (str_of_ids stripped_ns)
in ((uu____4082), (uu____4084), (uu____4086), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____4118 -> (match (uu____4118) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((Prims.op_Equality prefix1 "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____4167 -> begin
(((Prims.strcat prefix1 (Prims.strcat "." matched))), (stripped_ns), ((((FStar_String.length prefix1) + match_len) + (Prims.parse_int "1"))))
end)
end))
in (

let needle = (FStar_Util.split search_term ".")
in (

let all_lidents_in_env = (FStar_TypeChecker_Env.lidents env)
in (

let matches = (

let case_a_find_transitive_includes = (fun orig_ns m id1 -> (

let exported_names = (FStar_Syntax_DsEnv.transitive_exported_ids env.FStar_TypeChecker_Env.dsenv m)
in (

let matched_length = (FStar_List.fold_left (fun out s -> (((FStar_String.length s) + out) + (Prims.parse_int "1"))) (FStar_String.length id1) orig_ns)
in (FStar_All.pipe_right exported_names (FStar_List.filter_map (fun n1 -> (match ((FStar_Util.starts_with n1 id1)) with
| true -> begin
(

let lid = (

let uu____4307 = (FStar_Ident.ids_of_lid m)
in (

let uu____4310 = (FStar_Ident.id_of_text n1)
in (FStar_Ident.lid_of_ns_and_id uu____4307 uu____4310)))
in (

let uu____4311 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____4328 = (

let uu____4331 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____4331 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____4328), (matched_length)))) uu____4311)))
end
| uu____4340 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____4371 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____4452 -> (match (uu____4452) with
| (ns, id1, uu____4467) -> begin
(

let uu____4478 = (

let uu____4481 = (FStar_Ident.lid_of_ids id1)
in (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv uu____4481))
in (match (uu____4478) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____4485 = (FStar_Ident.lid_of_ids (FStar_List.append ns id1))
in (FStar_Ident.lid_equals l uu____4485))
end))
end))))))
in (

let uu____4486 = (FStar_Util.prefix needle)
in (match (uu____4486) with
| (ns, id1) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____4545 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____4550 = (FStar_Syntax_DsEnv.resolve_module_name env.FStar_TypeChecker_Env.dsenv l true)
in (match (uu____4550) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id1)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____4626 = (shorten_namespace x)
in (prepare_candidate uu____4626))))))
end))))
in ((

let uu____4640 = (FStar_Util.sort_with (fun uu____4669 uu____4670 -> (match (((uu____4669), (uu____4670))) with
| ((cd1, ns1, uu____4710), (cd2, ns2, uu____4713)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_1 when (_0_1 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.iter (fun uu____4761 -> (match (uu____4761) with
| (candidate, ns, match_len) -> begin
(

let uu____4780 = (FStar_Util.string_of_int match_len)
in (FStar_Util.print3 "%s %s %s \n" uu____4780 ns candidate))
end)) uu____4640));
(FStar_Util.print_string "#done-ok\n");
(go line_col filename stack curmod env ts);
))))))))))
end
| Pop (msg) -> begin
((pop env msg);
(

let uu____4788 = (match (stack) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDETooManyPops), ("too many pops")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd1)::tl1 -> begin
((hd1), (tl1))
end)
in (match (uu____4788) with
| ((env1, curmod1), stack1) -> begin
(go line_col filename stack1 curmod1 env1 ts)
end));
)
end
| Push (lax1, l, c) -> begin
(

let uu____4857 = (match ((Prims.op_Equality (FStar_List.length stack) (FStar_List.length ts))) with
| true -> begin
(

let uu____4899 = (update_deps filename curmod stack env ts)
in ((true), (uu____4899)))
end
| uu____4914 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____4857) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (curmod)))::stack1
in (

let env2 = (push_with_kind env1 lax1 restore_cmd_line_options1 "#push")
in (go ((l), (c)) filename stack2 curmod env2 ts1)))
end))
end
| Code (text, (ok, fail1)) -> begin
(

let fail2 = (fun curmod1 tcenv -> ((report_fail ());
(FStar_Util.print1 "%s\n" fail1);
(go line_col filename stack curmod1 tcenv ts);
))
in (

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (FStar_Pervasives_Native.fst line_col); FStar_Parser_ParseIt.frag_col = (FStar_Pervasives_Native.snd line_col)}
in (

let res = (check_frag env curmod frag)
in (match (res) with
| FStar_Pervasives_Native.Some (curmod1, env1, n_errs) -> begin
(match ((Prims.op_Equality n_errs (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print1 "\n%s\n" ok);
(go line_col filename stack curmod1 env1 ts);
)
end
| uu____5020 -> begin
(fail2 curmod1 env1)
end)
end
| uu____5022 -> begin
(fail2 curmod env)
end))))
end)))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((

let uu____5043 = (

let uu____5045 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____5045))
in (match (uu____5043) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("code-generation is not supported in interactive mode, ignoring the codegen flag")))
end
| uu____5051 -> begin
()
end));
(

let uu____5053 = (deps_of_our_file filename)
in (match (uu____5053) with
| (filenames, maybe_intf, dep_graph1) -> begin
(

let env = (FStar_Universal.init_env dep_graph1)
in (

let uu____5082 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____5082) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____5111 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____5114 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____5111 uu____5114)))
in (

let env2 = (FStar_TypeChecker_Env.set_range env1 initial_range)
in (

let env3 = (match (maybe_intf) with
| FStar_Pervasives_Native.Some (intf) -> begin
(FStar_Universal.load_interface_decls env2 intf)
end
| FStar_Pervasives_Native.None -> begin
env2
end)
in (

let uu____5124 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____5124) with
| true -> begin
(

let uu____5127 = (

let uu____5129 = (FStar_Options.file_list ())
in (FStar_List.hd uu____5129))
in (FStar_SMTEncoding_Solver.with_hints_db uu____5127 (fun uu____5135 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts))))
end
| uu____5140 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts)
end)))))
end)))
end));
))




