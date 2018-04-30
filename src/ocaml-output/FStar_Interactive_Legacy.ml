
open Prims
open FStar_Pervasives

let tc_one_file : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  ((Prims.string FStar_Pervasives_Native.option * Prims.string) * FStar_TypeChecker_Env.env * Prims.string Prims.list) = (fun remaining env -> (

let uu____29 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____63 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____63) with
| (uu____91, env1, delta1) -> begin
(

let uu____102 = (FStar_Universal.apply_delta_env env1 delta1)
in ((((FStar_Pervasives_Native.Some (intf)), (impl))), (uu____102), (remaining1)))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____119 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____119) with
| (uu____147, env1, delta1) -> begin
(

let uu____158 = (FStar_Universal.apply_delta_env env1 delta1)
in ((((FStar_Pervasives_Native.None), (intf_or_impl))), (uu____158), (remaining1)))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____29) with
| ((intf, impl), env1, remaining1) -> begin
((((intf), (impl))), (env1), (remaining1))
end)))


type env_t =
FStar_TypeChecker_Env.env


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let pop : FStar_TypeChecker_Env.env  ->  Prims.string  ->  unit = (fun env msg -> ((FStar_Universal.pop_context env msg);
(FStar_Options.pop ());
))


let push_with_kind : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env lax1 restore_cmd_line_options1 msg -> (

let env1 = (

let uu___60_267 = env
in {FStar_TypeChecker_Env.solver = uu___60_267.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___60_267.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___60_267.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___60_267.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___60_267.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___60_267.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___60_267.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___60_267.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___60_267.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___60_267.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___60_267.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___60_267.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___60_267.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___60_267.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___60_267.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___60_267.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___60_267.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___60_267.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___60_267.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___60_267.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___60_267.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___60_267.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___60_267.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___60_267.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___60_267.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___60_267.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___60_267.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___60_267.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___60_267.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___60_267.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___60_267.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___60_267.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___60_267.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___60_267.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___60_267.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___60_267.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___60_267.FStar_TypeChecker_Env.dep_graph})
in (

let res = (FStar_Universal.push_context env1 msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____271 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____271 (fun a239 -> ())))
end
| uu____272 -> begin
()
end);
res;
))))


let check_frag : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env * Prims.int) FStar_Pervasives_Native.option = (fun env curmod frag -> (FStar_All.try_with (fun uu___62_317 -> (match (()) with
| () -> begin
(

let uu____328 = (FStar_Universal.tc_one_fragment curmod env frag)
in (match (uu____328) with
| (m, env1) -> begin
(

let uu____351 = (

let uu____360 = (FStar_Errors.get_err_count ())
in ((m), (env1), (uu____360)))
in FStar_Pervasives_Native.Some (uu____351))
end))
end)) (fun uu___61_376 -> (match (uu___61_376) with
| FStar_Errors.Error (e, msg, r) when (

let uu____390 = (FStar_Options.trace_error ())
in (not (uu____390))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((e), (msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (e, msg) when (

let uu____414 = (FStar_Options.trace_error ())
in (not (uu____414))) -> begin
((

let uu____416 = (

let uu____425 = (

let uu____432 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____432)))
in (uu____425)::[])
in (FStar_TypeChecker_Err.add_errors env uu____416));
FStar_Pervasives_Native.None;
)
end))))


let report_fail : unit  ->  unit = (fun uu____457 -> ((

let uu____459 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____459 (fun a240 -> ())));
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
| uu____529 -> begin
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
| uu____561 -> begin
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
| uu____583 -> begin
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
| uu____635 -> begin
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
| uu____691 -> begin
false
end))


let __proj__Completions__item___0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Completions (_0) -> begin
_0
end))

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref}


let __proj__Mkinteractive_state__item__chunk : interactive_state  ->  FStar_Util.string_builder = (fun projectee -> (match (projectee) with
| {chunk = __fname__chunk; stdin = __fname__stdin; buffer = __fname__buffer; log = __fname__log} -> begin
__fname__chunk
end))


let __proj__Mkinteractive_state__item__stdin : interactive_state  ->  FStar_Util.stream_reader FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {chunk = __fname__chunk; stdin = __fname__stdin; buffer = __fname__buffer; log = __fname__log} -> begin
__fname__stdin
end))


let __proj__Mkinteractive_state__item__buffer : interactive_state  ->  input_chunks Prims.list FStar_ST.ref = (fun projectee -> (match (projectee) with
| {chunk = __fname__chunk; stdin = __fname__stdin; buffer = __fname__buffer; log = __fname__log} -> begin
__fname__buffer
end))


let __proj__Mkinteractive_state__item__log : interactive_state  ->  FStar_Util.file_handle FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {chunk = __fname__chunk; stdin = __fname__stdin; buffer = __fname__buffer; log = __fname__log} -> begin
__fname__log
end))


let the_interactive_state : interactive_state = (

let uu____1001 = (FStar_Util.new_string_builder ())
in (

let uu____1002 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____1009 = (FStar_Util.mk_ref [])
in (

let uu____1016 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {chunk = uu____1001; stdin = uu____1002; buffer = uu____1009; log = uu____1016}))))


let rec read_chunk : unit  ->  input_chunks = (fun uu____1093 -> (

let s = the_interactive_state
in (

let log1 = (

let uu____1100 = (FStar_Options.debug_any ())
in (match (uu____1100) with
| true -> begin
(

let transcript = (

let uu____1105 = (FStar_ST.op_Bang s.log)
in (match (uu____1105) with
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
| uu____1167 -> begin
(fun uu____1168 -> ())
end))
in (

let stdin = (

let uu____1170 = (FStar_ST.op_Bang s.stdin)
in (match (uu____1170) with
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

let uu____1231 = (FStar_Util.read_line stdin)
in (match (uu____1231) with
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
| (uu____1246)::(ok)::(fail1)::[] -> begin
((ok), (fail1))
end
| uu____1249 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____1258 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____1260 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____1263 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____1263))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l1)::(c)::("#lax")::[] -> begin
(

let uu____1279 = (FStar_Util.int_of_string l1)
in (

let uu____1280 = (FStar_Util.int_of_string c)
in ((true), (uu____1279), (uu____1280))))
end
| (l1)::(c)::[] -> begin
(

let uu____1283 = (FStar_Util.int_of_string l1)
in (

let uu____1284 = (FStar_Util.int_of_string c)
in ((false), (uu____1283), (uu____1284))))
end
| uu____1285 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_WrongErrorLocation), ((Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax))));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____1289 -> begin
(match ((FStar_Util.starts_with l "#info ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1290)::(symbol)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Info (((symbol), (true), (FStar_Pervasives_Native.None)));
)
end
| (uu____1307)::(symbol)::(file)::(row)::(col)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let uu____1313 = (

let uu____1328 = (

let uu____1337 = (

let uu____1344 = (FStar_Util.int_of_string row)
in (

let uu____1345 = (FStar_Util.int_of_string col)
in ((file), (uu____1344), (uu____1345))))
in FStar_Pervasives_Native.Some (uu____1337))
in ((symbol), (false), (uu____1328)))
in Info (uu____1313));
)
end
| uu____1360 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDEUnrecognized), ((Prims.strcat "Unrecognized \"#info\" request: " l))));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1364 -> begin
(match ((FStar_Util.starts_with l "#completions ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1365)::(prefix1)::("#")::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Completions (prefix1);
)
end
| uu____1368 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDEUnrecognized), ((Prims.strcat "Unrecognized \"#completions\" request: " l))));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1372 -> begin
(match ((Prims.op_Equality l "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____1373 -> begin
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


let shift_chunk : unit  ->  input_chunks = (fun uu____1380 -> (

let s = the_interactive_state
in (

let uu____1382 = (FStar_ST.op_Bang s.buffer)
in (match (uu____1382) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.op_Colon_Equals s.buffer chunks);
chunk;
)
end))))


let fill_buffer : unit  ->  unit = (fun uu____1448 -> (

let s = the_interactive_state
in (

let uu____1450 = (

let uu____1453 = (FStar_ST.op_Bang s.buffer)
in (

let uu____1483 = (

let uu____1486 = (read_chunk ())
in (uu____1486)::[])
in (FStar_List.append uu____1453 uu____1483)))
in (FStar_ST.op_Colon_Equals s.buffer uu____1450))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option * FStar_Parser_Dep.deps) = (fun filename -> (

let uu____1529 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____1529) with
| (deps, dep_graph1) -> begin
(

let uu____1552 = (FStar_List.partition (fun x -> (

let uu____1565 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____1566 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____1565 uu____1566)))) deps)
in (match (uu____1552) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____1595 = ((

let uu____1598 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____1598))) || (

let uu____1600 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____1600))))
in (match (uu____1595) with
| true -> begin
(

let uu____1601 = (

let uu____1606 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in ((FStar_Errors.Warning_MissingInterfaceOrImplementation), (uu____1606)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1601))
end
| uu____1607 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____1609 -> begin
((

let uu____1613 = (

let uu____1618 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in ((FStar_Errors.Warning_UnexpectedFile), (uu____1618)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1613));
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
| uu____1678 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____1693 = (FStar_Options.lax ())
in (push_with_kind env uu____1693 true "typecheck_modul"))
in (

let uu____1694 = (tc_one_file remaining env1)
in (match (uu____1694) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____1733 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____1746 = (FStar_Parser_ParseIt.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____1746))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Parser_ParseIt.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____1733) with
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
| (uu____1863, uu____1864) -> begin
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
| uu____1974 -> begin
((false), (depnames1))
end)
end
| uu____1977 -> begin
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
| uu____2002 -> begin
((false), (depnames1))
end)
end
| uu____2005 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____2078)::ts3 -> begin
((pop env1 "");
(

let uu____2119 = (

let uu____2134 = (FStar_List.hd stack)
in (

let uu____2143 = (FStar_List.tl stack)
in ((uu____2134), (uu____2143))))
in (match (uu____2119) with
| ((env2, uu____2165), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____2229 = ts_elt
in (match (uu____2229) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____2260 = (match_dep depnames intf impl)
in (match (uu____2260) with
| (b, depnames') -> begin
(

let uu____2279 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____2279) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____2295 -> begin
(

let uu____2296 = (

let uu____2305 = (FStar_List.hd st)
in (

let uu____2314 = (FStar_List.tl st)
in ((uu____2305), (uu____2314))))
in (match (uu____2296) with
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

let uu____2367 = (deps_of_our_file filename)
in (match (uu____2367) with
| (filenames, uu____2385, dep_graph1) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let format_info : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun env name typ range doc1 -> (

let uu____2472 = (FStar_Range.string_of_range range)
in (

let uu____2473 = (FStar_TypeChecker_Normalize.term_to_string env typ)
in (

let uu____2474 = (match (doc1) with
| FStar_Pervasives_Native.Some (docstring) -> begin
(FStar_Util.format1 "#doc %s" docstring)
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2472 name uu____2473 uu____2474)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  unit = (fun line_col filename stack curmod env ts -> (

let uu____2514 = (shift_chunk ())
in (match (uu____2514) with
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
| FStar_Pervasives_Native.Some (uu____2609) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2662 -> begin
(

let lid = (

let uu____2664 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split symbol "."))
in (FStar_Ident.lid_of_ids uu____2664))
in (

let lid1 = (match (fqn_only) with
| true -> begin
lid
end
| uu____2668 -> begin
(

let uu____2669 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____2669) with
| FStar_Pervasives_Native.None -> begin
lid
end
| FStar_Pervasives_Native.Some (lid1) -> begin
lid1
end))
end)
in (

let uu____2673 = (FStar_TypeChecker_Env.try_lookup_lid env lid1)
in (FStar_All.pipe_right uu____2673 (FStar_Util.map_option (fun uu____2728 -> (match (uu____2728) with
| ((uu____2747, typ), r) -> begin
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

let uu____2790 = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
((name), (FStar_Pervasives_Native.None))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____2807 = (FStar_Ident.string_of_lid lid)
in (

let uu____2808 = (

let uu____2811 = (FStar_Syntax_DsEnv.try_lookup_doc env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____2811 (FStar_Util.map_option FStar_Pervasives_Native.fst)))
in ((uu____2807), (uu____2808))))
end)
in (match (uu____2790) with
| (name, doc1) -> begin
(

let uu____2862 = (format_info env name typ rng doc1)
in (FStar_Util.print1 "%s\n#done-ok\n" uu____2862))
end))
end);
(go line_col filename stack curmod env ts);
)))
end
| Completions (search_term) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____2903) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____2918, []) -> begin
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
| uu____2968 -> begin
(

let uu____2971 = (measure_anchored_match ts1 tc1)
in (FStar_All.pipe_right uu____2971 (FStar_Util.map_option (fun uu____3011 -> (match (uu____3011) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____3032 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____3070 = (measure_anchored_match needle candidate)
in (match (uu____3070) with
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

let uu____3149 = (locate_match needle tc1)
in (FStar_All.pipe_right uu____3149 (FStar_Util.map_option (fun uu____3210 -> (match (uu____3210) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____3256 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____3256)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____3309 -> (match (uu____3309) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____3340)::[] -> begin
true
end
| uu____3341 -> begin
false
end)
in (

let uu____3344 = (FStar_Syntax_DsEnv.shorten_module_path env.FStar_TypeChecker_Env.dsenv prefix1 naked_match)
in (match (uu____3344) with
| (stripped_ns, shortened) -> begin
(

let uu____3371 = (str_of_ids shortened)
in (

let uu____3372 = (str_of_ids matched)
in (

let uu____3373 = (str_of_ids stripped_ns)
in ((uu____3371), (uu____3372), (uu____3373), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____3393 -> (match (uu____3393) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((Prims.op_Equality prefix1 "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____3418 -> begin
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

let uu____3527 = (FStar_Ident.ids_of_lid m)
in (

let uu____3530 = (FStar_Ident.id_of_text n1)
in (FStar_Ident.lid_of_ns_and_id uu____3527 uu____3530)))
in (

let uu____3531 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____3547 = (

let uu____3550 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____3550 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____3547), (matched_length)))) uu____3531)))
end
| uu____3557 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____3585 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____3660 -> (match (uu____3660) with
| (ns, id1, uu____3673) -> begin
(

let uu____3682 = (

let uu____3685 = (FStar_Ident.lid_of_ids id1)
in (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv uu____3685))
in (match (uu____3682) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3687 = (FStar_Ident.lid_of_ids (FStar_List.append ns id1))
in (FStar_Ident.lid_equals l uu____3687))
end))
end))))))
in (

let uu____3688 = (FStar_Util.prefix needle)
in (match (uu____3688) with
| (ns, id1) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____3734 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____3738 = (FStar_Syntax_DsEnv.resolve_module_name env.FStar_TypeChecker_Env.dsenv l true)
in (match (uu____3738) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id1)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____3803 = (shorten_namespace x)
in (prepare_candidate uu____3803))))))
end))))
in ((

let uu____3813 = (FStar_Util.sort_with (fun uu____3836 uu____3837 -> (match (((uu____3836), (uu____3837))) with
| ((cd1, ns1, uu____3864), (cd2, ns2, uu____3867)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_17 when (_0_17 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.iter (fun uu____3892 -> (match (uu____3892) with
| (candidate, ns, match_len) -> begin
(

let uu____3902 = (FStar_Util.string_of_int match_len)
in (FStar_Util.print3 "%s %s %s \n" uu____3902 ns candidate))
end)) uu____3813));
(FStar_Util.print_string "#done-ok\n");
(go line_col filename stack curmod env ts);
))))))))))
end
| Pop (msg) -> begin
((pop env msg);
(

let uu____3906 = (match (stack) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDETooManyPops), ("too many pops")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd1)::tl1 -> begin
((hd1), (tl1))
end)
in (match (uu____3906) with
| ((env1, curmod1), stack1) -> begin
(go line_col filename stack1 curmod1 env1 ts)
end));
)
end
| Push (lax1, l, c) -> begin
(

let uu____4002 = (match ((Prims.op_Equality (FStar_List.length stack) (FStar_List.length ts))) with
| true -> begin
(

let uu____4039 = (update_deps filename curmod stack env ts)
in ((true), (uu____4039)))
end
| uu____4052 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____4002) with
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
| uu____4129 -> begin
(fail2 curmod1 env1)
end)
end
| uu____4130 -> begin
(fail2 curmod env)
end))))
end)))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((

let uu____4147 = (

let uu____4148 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____4148))
in (match (uu____4147) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("code-generation is not supported in interactive mode, ignoring the codegen flag")))
end
| uu____4151 -> begin
()
end));
(

let uu____4152 = (deps_of_our_file filename)
in (match (uu____4152) with
| (filenames, maybe_intf, dep_graph1) -> begin
(

let env = (FStar_Universal.init_env dep_graph1)
in (

let uu____4175 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____4175) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____4202 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____4203 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____4202 uu____4203)))
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

let uu____4207 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____4207) with
| true -> begin
(

let uu____4208 = (

let uu____4209 = (FStar_Options.file_list ())
in (FStar_List.hd uu____4209))
in (FStar_SMTEncoding_Solver.with_hints_db uu____4208 (fun uu____4213 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts))))
end
| uu____4214 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts)
end)))))
end)))
end));
))




