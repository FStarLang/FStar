
open Prims
open FStar_Pervasives

let tc_one_file : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  ((Prims.string FStar_Pervasives_Native.option * Prims.string) * FStar_TypeChecker_Env.env * Prims.string Prims.list) = (fun remaining env -> (

let uu____27 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____61 = (FStar_Universal.tc_one_file env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____61) with
| (uu____84, env1) -> begin
((((FStar_Pervasives_Native.Some (intf)), (impl))), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____108 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____108) with
| (uu____131, env1) -> begin
((((FStar_Pervasives_Native.None), (intf_or_impl))), (env1), (remaining1))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____27) with
| ((intf, impl), env1, remaining1) -> begin
((((intf), (impl))), (env1), (remaining1))
end)))


let tc_prims : Prims.unit  ->  FStar_TypeChecker_Env.env = (fun uu____210 -> (

let uu____211 = (

let uu____220 = (FStar_Universal.init_env ())
in (FStar_Universal.tc_prims uu____220))
in (match (uu____211) with
| (uu____221, env) -> begin
env
end)))


type env_t =
FStar_TypeChecker_Env.env


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let pop : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((FStar_Universal.pop_context env msg);
(FStar_Options.pop ());
))


let push_with_kind : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env lax1 restore_cmd_line_options1 msg -> (

let env1 = (

let uu___275_265 = env
in {FStar_TypeChecker_Env.solver = uu___275_265.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___275_265.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___275_265.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___275_265.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___275_265.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___275_265.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___275_265.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___275_265.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___275_265.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___275_265.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___275_265.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___275_265.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___275_265.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___275_265.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___275_265.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___275_265.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___275_265.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___275_265.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___275_265.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___275_265.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___275_265.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___275_265.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___275_265.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___275_265.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___275_265.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___275_265.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___275_265.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___275_265.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___275_265.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___275_265.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___275_265.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___275_265.FStar_TypeChecker_Env.dsenv})
in (

let res = (FStar_Universal.push_context env1 msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____269 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____269 FStar_Pervasives.ignore))
end
| uu____270 -> begin
()
end);
res;
))))


let check_frag : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env * Prims.int) FStar_Pervasives_Native.option = (fun env curmod frag -> (FStar_All.try_with (fun uu___277_320 -> (match (()) with
| () -> begin
(

let uu____331 = (FStar_Universal.tc_one_fragment curmod env frag)
in (match (uu____331) with
| (m, env1) -> begin
(

let uu____354 = (

let uu____363 = (FStar_Errors.get_err_count ())
in ((m), (env1), (uu____363)))
in FStar_Pervasives_Native.Some (uu____354))
end))
end)) (fun uu___276_378 -> (match (uu___276_378) with
| FStar_Errors.Error (msg, r) when (

let uu____391 = (FStar_Options.trace_error ())
in (not (uu____391))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____410 = (FStar_Options.trace_error ())
in (not (uu____410))) -> begin
((

let uu____412 = (

let uu____419 = (

let uu____424 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____424)))
in (uu____419)::[])
in (FStar_TypeChecker_Err.add_errors env uu____412));
FStar_Pervasives_Native.None;
)
end))))


let report_fail : Prims.unit  ->  Prims.unit = (fun uu____444 -> ((

let uu____446 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____446 FStar_Pervasives.ignore));
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
| uu____512 -> begin
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
| uu____544 -> begin
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
| uu____566 -> begin
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
| uu____618 -> begin
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
| uu____674 -> begin
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

let uu____917 = (FStar_Util.new_string_builder ())
in (

let uu____918 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____925 = (FStar_Util.mk_ref [])
in (

let uu____932 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {chunk = uu____917; stdin = uu____918; buffer = uu____925; log = uu____932}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun uu____984 -> (

let s = the_interactive_state
in (

let log1 = (

let uu____989 = (FStar_Options.debug_any ())
in (match (uu____989) with
| true -> begin
(

let transcript = (

let uu____993 = (FStar_ST.op_Bang s.log)
in (match (uu____993) with
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
| uu____1101 -> begin
(fun uu____1102 -> ())
end))
in (

let stdin = (

let uu____1104 = (FStar_ST.op_Bang s.stdin)
in (match (uu____1104) with
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

let uu____1211 = (FStar_Util.read_line stdin)
in (match (uu____1211) with
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
| (uu____1226)::(ok)::(fail4)::[] -> begin
((ok), (fail4))
end
| uu____1229 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____1238 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____1240 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____1243 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____1243))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l1)::(c)::("#lax")::[] -> begin
(

let uu____1259 = (FStar_Util.int_of_string l1)
in (

let uu____1260 = (FStar_Util.int_of_string c)
in ((true), (uu____1259), (uu____1260))))
end
| (l1)::(c)::[] -> begin
(

let uu____1263 = (FStar_Util.int_of_string l1)
in (

let uu____1264 = (FStar_Util.int_of_string c)
in ((false), (uu____1263), (uu____1264))))
end
| uu____1265 -> begin
((FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____1269 -> begin
(match ((FStar_Util.starts_with l "#info ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1270)::(symbol)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Info (((symbol), (true), (FStar_Pervasives_Native.None)));
)
end
| (uu____1287)::(symbol)::(file)::(row)::(col)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let uu____1293 = (

let uu____1308 = (

let uu____1317 = (

let uu____1324 = (FStar_Util.int_of_string row)
in (

let uu____1325 = (FStar_Util.int_of_string col)
in ((file), (uu____1324), (uu____1325))))
in FStar_Pervasives_Native.Some (uu____1317))
in ((symbol), (false), (uu____1308)))
in Info (uu____1293));
)
end
| uu____1340 -> begin
((FStar_Util.print_error (Prims.strcat "Unrecognized \"#info\" request: " l));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1344 -> begin
(match ((FStar_Util.starts_with l "#completions ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1345)::(prefix1)::("#")::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Completions (prefix1);
)
end
| uu____1348 -> begin
((FStar_Util.print_error (Prims.strcat "Unrecognized \"#completions\" request: " l));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1352 -> begin
(match ((Prims.op_Equality l "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____1353 -> begin
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


let shift_chunk : Prims.unit  ->  input_chunks = (fun uu____1359 -> (

let s = the_interactive_state
in (

let uu____1361 = (FStar_ST.op_Bang s.buffer)
in (match (uu____1361) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.op_Colon_Equals s.buffer chunks);
chunk;
)
end))))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun uu____1472 -> (

let s = the_interactive_state
in (

let uu____1474 = (

let uu____1477 = (FStar_ST.op_Bang s.buffer)
in (

let uu____1530 = (

let uu____1533 = (read_chunk ())
in (uu____1533)::[])
in (FStar_List.append uu____1477 uu____1530)))
in (FStar_ST.op_Colon_Equals s.buffer uu____1474))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____1599 = (FStar_List.partition (fun x -> (

let uu____1612 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____1613 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____1612 uu____1613)))) deps)
in (match (uu____1599) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____1640 = ((

let uu____1643 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____1643))) || (

let uu____1645 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____1645))))
in (match (uu____1640) with
| true -> begin
(

let uu____1646 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____1646))
end
| uu____1647 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____1649 -> begin
((

let uu____1653 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____1653));
FStar_Pervasives_Native.None;
)
end)
in ((deps1), (maybe_intf)))
end))))


type m_timestamps =
(Prims.string FStar_Pervasives_Native.option * Prims.string * FStar_Util.time FStar_Pervasives_Native.option * FStar_Util.time) Prims.list


let rec tc_deps : modul_t  ->  stack_t  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  m_timestamps  ->  (stack_t * FStar_TypeChecker_Env.env * m_timestamps) = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| uu____1708 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____1723 = (FStar_Options.lax ())
in (push_with_kind env uu____1723 true "typecheck_modul"))
in (

let uu____1724 = (tc_one_file remaining env1)
in (match (uu____1724) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____1763 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____1776 = (FStar_Parser_ParseIt.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____1776))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Parser_ParseIt.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____1763) with
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
| (uu____1880, uu____1881) -> begin
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
| uu____1973 -> begin
((false), (depnames1))
end)
end
| uu____1976 -> begin
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
| uu____2001 -> begin
((false), (depnames1))
end)
end
| uu____2004 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____2071)::ts3 -> begin
((pop env1 "");
(

let uu____2112 = (

let uu____2127 = (FStar_List.hd stack)
in (

let uu____2136 = (FStar_List.tl stack)
in ((uu____2127), (uu____2136))))
in (match (uu____2112) with
| ((env2, uu____2158), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____2222 = ts_elt
in (match (uu____2222) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____2253 = (match_dep depnames intf impl)
in (match (uu____2253) with
| (b, depnames') -> begin
(

let uu____2272 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____2272) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____2288 -> begin
(

let uu____2289 = (

let uu____2304 = (FStar_List.hd st)
in (

let uu____2313 = (FStar_List.tl st)
in ((uu____2304), (uu____2313))))
in (match (uu____2289) with
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

let uu____2390 = (deps_of_our_file filename)
in (match (uu____2390) with
| (filenames, uu____2406) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let format_info : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun env name typ range doc1 -> (

let uu____2487 = (FStar_Range.string_of_range range)
in (

let uu____2488 = (FStar_TypeChecker_Normalize.term_to_string env typ)
in (

let uu____2489 = (match (doc1) with
| FStar_Pervasives_Native.Some (docstring) -> begin
(FStar_Util.format1 "#doc %s" docstring)
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2487 name uu____2488 uu____2489)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  Prims.unit = (fun line_col filename stack curmod env ts -> (

let uu____2523 = (shift_chunk ())
in (match (uu____2523) with
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
| FStar_Pervasives_Native.Some (uu____2618) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2671 -> begin
(

let lid = (

let uu____2673 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split symbol "."))
in (FStar_Ident.lid_of_ids uu____2673))
in (

let lid1 = (match (fqn_only) with
| true -> begin
lid
end
| uu____2677 -> begin
(

let uu____2678 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____2678) with
| FStar_Pervasives_Native.None -> begin
lid
end
| FStar_Pervasives_Native.Some (lid1) -> begin
lid1
end))
end)
in (

let uu____2682 = (FStar_TypeChecker_Env.try_lookup_lid env lid1)
in (FStar_All.pipe_right uu____2682 (FStar_Util.map_option (fun uu____2737 -> (match (uu____2737) with
| ((uu____2756, typ), r) -> begin
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

let uu____2799 = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
((name), (FStar_Pervasives_Native.None))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____2816 = (FStar_Ident.string_of_lid lid)
in (

let uu____2817 = (

let uu____2820 = (FStar_ToSyntax_Env.try_lookup_doc env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____2820 (FStar_Util.map_option FStar_Pervasives_Native.fst)))
in ((uu____2816), (uu____2817))))
end)
in (match (uu____2799) with
| (name, doc1) -> begin
(

let uu____2851 = (format_info env name typ rng doc1)
in (FStar_Util.print1 "%s\n#done-ok\n" uu____2851))
end))
end);
(go line_col filename stack curmod env ts);
)))
end
| Completions (search_term) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____2888) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____2903, []) -> begin
FStar_Pervasives_Native.None
end
| ((hs)::ts1, (hc)::tc) -> begin
(

let hc_text = (FStar_Ident.text_of_id hc)
in (match ((FStar_Util.starts_with hc_text hs)) with
| true -> begin
(match (ts1) with
| [] -> begin
FStar_Pervasives_Native.Some (((candidate), ((FStar_String.length hs))))
end
| uu____2953 -> begin
(

let uu____2956 = (measure_anchored_match ts1 tc)
in (FStar_All.pipe_right uu____2956 (FStar_Util.map_option (fun uu____2996 -> (match (uu____2996) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____3017 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____3051 = (measure_anchored_match needle candidate)
in (match (uu____3051) with
| FStar_Pervasives_Native.Some (matched, n1) -> begin
FStar_Pervasives_Native.Some ((([]), (matched), (n1)))
end
| FStar_Pervasives_Native.None -> begin
(match (candidate) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (hc)::tc -> begin
(

let uu____3130 = (locate_match needle tc)
in (FStar_All.pipe_right uu____3130 (FStar_Util.map_option (fun uu____3191 -> (match (uu____3191) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____3235 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____3235)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____3282 -> (match (uu____3282) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____3313)::[] -> begin
true
end
| uu____3314 -> begin
false
end)
in (

let uu____3317 = (FStar_ToSyntax_Env.shorten_module_path env.FStar_TypeChecker_Env.dsenv prefix1 naked_match)
in (match (uu____3317) with
| (stripped_ns, shortened) -> begin
(

let uu____3344 = (str_of_ids shortened)
in (

let uu____3345 = (str_of_ids matched)
in (

let uu____3346 = (str_of_ids stripped_ns)
in ((uu____3344), (uu____3345), (uu____3346), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____3364 -> (match (uu____3364) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((Prims.op_Equality prefix1 "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____3389 -> begin
(((Prims.strcat prefix1 (Prims.strcat "." matched))), (stripped_ns), ((((FStar_String.length prefix1) + match_len) + (Prims.parse_int "1"))))
end)
end))
in (

let needle = (FStar_Util.split search_term ".")
in (

let all_lidents_in_env = (FStar_TypeChecker_Env.lidents env)
in (

let matches = (

let case_a_find_transitive_includes = (fun orig_ns m id -> (

let exported_names = (FStar_ToSyntax_Env.transitive_exported_ids env.FStar_TypeChecker_Env.dsenv m)
in (

let matched_length = (FStar_List.fold_left (fun out s -> (((FStar_String.length s) + out) + (Prims.parse_int "1"))) (FStar_String.length id) orig_ns)
in (FStar_All.pipe_right exported_names (FStar_List.filter_map (fun n1 -> (match ((FStar_Util.starts_with n1 id)) with
| true -> begin
(

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m) (FStar_Ident.id_of_text n1))
in (

let uu____3492 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____3508 = (

let uu____3511 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____3511 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____3508), (matched_length)))) uu____3492)))
end
| uu____3518 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____3544 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____3619 -> (match (uu____3619) with
| (ns, id, uu____3632) -> begin
(

let uu____3641 = (

let uu____3644 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv uu____3644))
in (match (uu____3641) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3646 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____3646))
end))
end))))))
in (

let uu____3647 = (FStar_Util.prefix needle)
in (match (uu____3647) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____3693 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____3697 = (FStar_ToSyntax_Env.resolve_module_name env.FStar_TypeChecker_Env.dsenv l true)
in (match (uu____3697) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____3762 = (shorten_namespace x)
in (prepare_candidate uu____3762))))))
end))))
in ((

let uu____3772 = (FStar_Util.sort_with (fun uu____3795 uu____3796 -> (match (((uu____3795), (uu____3796))) with
| ((cd1, ns1, uu____3823), (cd2, ns2, uu____3826)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_53 when (_0_53 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.iter (fun uu____3851 -> (match (uu____3851) with
| (candidate, ns, match_len) -> begin
(

let uu____3861 = (FStar_Util.string_of_int match_len)
in (FStar_Util.print3 "%s %s %s \n" uu____3861 ns candidate))
end)) uu____3772));
(FStar_Util.print_string "#done-ok\n");
(go line_col filename stack curmod env ts);
))))))))))
end
| Pop (msg) -> begin
((pop env msg);
(

let uu____3865 = (match (stack) with
| [] -> begin
((FStar_Util.print_error "too many pops");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd1)::tl1 -> begin
((hd1), (tl1))
end)
in (match (uu____3865) with
| ((env1, curmod1), stack1) -> begin
(go line_col filename stack1 curmod1 env1 ts)
end));
)
end
| Push (lax1, l, c) -> begin
(

let uu____3961 = (match ((Prims.op_Equality (FStar_List.length stack) (FStar_List.length ts))) with
| true -> begin
(

let uu____3998 = (update_deps filename curmod stack env ts)
in ((true), (uu____3998)))
end
| uu____4011 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____3961) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (curmod)))::stack1
in (

let env2 = (push_with_kind env1 lax1 restore_cmd_line_options1 "#push")
in (go ((l), (c)) filename stack2 curmod env2 ts1)))
end))
end
| Code (text1, (ok, fail4)) -> begin
(

let fail5 = (fun curmod1 tcenv -> ((report_fail ());
(FStar_Util.print1 "%s\n" fail4);
(go line_col filename stack curmod1 tcenv ts);
))
in (

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = (FStar_Pervasives_Native.fst line_col); FStar_Parser_ParseIt.frag_col = (FStar_Pervasives_Native.snd line_col)}
in (

let res = (check_frag env curmod ((frag), (false)))
in (match (res) with
| FStar_Pervasives_Native.Some (curmod1, env1, n_errs) -> begin
(match ((Prims.op_Equality n_errs (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print1 "\n%s\n" ok);
(go line_col filename stack curmod1 env1 ts);
)
end
| uu____4084 -> begin
(fail5 curmod1 env1)
end)
end
| uu____4085 -> begin
(fail5 curmod env)
end))))
end)))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((

let uu____4101 = (

let uu____4102 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____4102))
in (match (uu____4101) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____4105 -> begin
()
end));
(

let uu____4106 = (deps_of_our_file filename)
in (match (uu____4106) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____4126 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____4126) with
| (stack, env1, ts) -> begin
(

let initial_range1 = (

let uu____4153 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____4154 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____4153 uu____4154)))
in (

let env2 = (FStar_TypeChecker_Env.set_range env1 initial_range1)
in (

let env3 = (match (maybe_intf) with
| FStar_Pervasives_Native.Some (intf) -> begin
(FStar_Universal.load_interface_decls env2 intf)
end
| FStar_Pervasives_Native.None -> begin
env2
end)
in (

let uu____4158 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____4158) with
| true -> begin
(

let uu____4159 = (

let uu____4160 = (FStar_Options.file_list ())
in (FStar_List.hd uu____4160))
in (FStar_SMTEncoding_Solver.with_hints_db uu____4159 (fun uu____4164 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts))))
end
| uu____4165 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts)
end)))))
end)))
end));
))




