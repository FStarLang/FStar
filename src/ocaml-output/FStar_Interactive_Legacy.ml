
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


let pop : FStar_TypeChecker_Env.env  ->  Prims.string  ->  unit = (fun env msg -> ((

let uu____246 = (FStar_TypeChecker_Tc.pop_context env msg)
in ());
(FStar_Options.pop ());
))


let push_with_kind : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env lax1 restore_cmd_line_options1 msg -> (

let env1 = (

let uu___423_268 = env
in {FStar_TypeChecker_Env.solver = uu___423_268.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___423_268.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___423_268.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___423_268.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___423_268.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___423_268.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___423_268.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___423_268.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___423_268.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___423_268.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___423_268.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___423_268.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___423_268.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___423_268.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___423_268.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___423_268.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___423_268.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___423_268.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___423_268.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___423_268.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___423_268.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___423_268.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___423_268.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___423_268.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___423_268.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___423_268.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___423_268.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___423_268.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___423_268.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___423_268.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___423_268.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___423_268.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___423_268.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___423_268.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___423_268.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___423_268.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___423_268.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___423_268.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___423_268.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___423_268.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___423_268.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___423_268.FStar_TypeChecker_Env.nbe})
in (

let res = (FStar_TypeChecker_Tc.push_context env1 msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____272 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____272 (fun a1 -> ())))
end
| uu____273 -> begin
()
end);
res;
))))


let check_frag : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env * Prims.int) FStar_Pervasives_Native.option = (fun env curmod frag -> (FStar_All.try_with (fun uu___425_318 -> (match (()) with
| () -> begin
(

let uu____329 = (FStar_Universal.tc_one_fragment curmod env frag)
in (match (uu____329) with
| (m, env1) -> begin
(

let uu____352 = (

let uu____361 = (FStar_Errors.get_err_count ())
in ((m), (env1), (uu____361)))
in FStar_Pervasives_Native.Some (uu____352))
end))
end)) (fun uu___424_377 -> (match (uu___424_377) with
| FStar_Errors.Error (e, msg, r) when (

let uu____391 = (FStar_Options.trace_error ())
in (not (uu____391))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((e), (msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (e, msg) when (

let uu____415 = (FStar_Options.trace_error ())
in (not (uu____415))) -> begin
((

let uu____417 = (

let uu____426 = (

let uu____433 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____433)))
in (uu____426)::[])
in (FStar_TypeChecker_Err.add_errors env uu____417));
FStar_Pervasives_Native.None;
)
end))))


let report_fail : unit  ->  unit = (fun uu____458 -> ((

let uu____460 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____460 (fun a2 -> ())));
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
| uu____530 -> begin
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
| uu____562 -> begin
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
| uu____584 -> begin
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
| uu____636 -> begin
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
| uu____692 -> begin
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

let uu____1002 = (FStar_Util.new_string_builder ())
in (

let uu____1003 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____1010 = (FStar_Util.mk_ref [])
in (

let uu____1017 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {chunk = uu____1002; stdin = uu____1003; buffer = uu____1010; log = uu____1017}))))


let rec read_chunk : unit  ->  input_chunks = (fun uu____1094 -> (

let s = the_interactive_state
in (

let log1 = (

let uu____1101 = (FStar_Options.debug_any ())
in (match (uu____1101) with
| true -> begin
(

let transcript = (

let uu____1106 = (FStar_ST.op_Bang s.log)
in (match (uu____1106) with
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
| uu____1160 -> begin
(fun uu____1161 -> ())
end))
in (

let stdin = (

let uu____1163 = (FStar_ST.op_Bang s.stdin)
in (match (uu____1163) with
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

let uu____1216 = (FStar_Util.read_line stdin)
in (match (uu____1216) with
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
| (uu____1231)::(ok)::(fail1)::[] -> begin
((ok), (fail1))
end
| uu____1234 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____1243 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____1245 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____1248 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____1248))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l1)::(c)::("#lax")::[] -> begin
(

let uu____1264 = (FStar_Util.int_of_string l1)
in (

let uu____1265 = (FStar_Util.int_of_string c)
in ((true), (uu____1264), (uu____1265))))
end
| (l1)::(c)::[] -> begin
(

let uu____1268 = (FStar_Util.int_of_string l1)
in (

let uu____1269 = (FStar_Util.int_of_string c)
in ((false), (uu____1268), (uu____1269))))
end
| uu____1270 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_WrongErrorLocation), ((Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax))));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____1274 -> begin
(match ((FStar_Util.starts_with l "#info ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1275)::(symbol)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Info (((symbol), (true), (FStar_Pervasives_Native.None)));
)
end
| (uu____1292)::(symbol)::(file)::(row)::(col)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let uu____1298 = (

let uu____1313 = (

let uu____1322 = (

let uu____1329 = (FStar_Util.int_of_string row)
in (

let uu____1330 = (FStar_Util.int_of_string col)
in ((file), (uu____1329), (uu____1330))))
in FStar_Pervasives_Native.Some (uu____1322))
in ((symbol), (false), (uu____1313)))
in Info (uu____1298));
)
end
| uu____1345 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDEUnrecognized), ((Prims.strcat "Unrecognized \"#info\" request: " l))));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1349 -> begin
(match ((FStar_Util.starts_with l "#completions ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____1350)::(prefix1)::("#")::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Completions (prefix1);
)
end
| uu____1353 -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDEUnrecognized), ((Prims.strcat "Unrecognized \"#completions\" request: " l))));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____1357 -> begin
(match ((Prims.op_Equality l "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____1358 -> begin
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


let shift_chunk : unit  ->  input_chunks = (fun uu____1365 -> (

let s = the_interactive_state
in (

let uu____1367 = (FStar_ST.op_Bang s.buffer)
in (match (uu____1367) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.op_Colon_Equals s.buffer chunks);
chunk;
)
end))))


let fill_buffer : unit  ->  unit = (fun uu____1425 -> (

let s = the_interactive_state
in (

let uu____1427 = (

let uu____1430 = (FStar_ST.op_Bang s.buffer)
in (

let uu____1456 = (

let uu____1459 = (read_chunk ())
in (uu____1459)::[])
in (FStar_List.append uu____1430 uu____1456)))
in (FStar_ST.op_Colon_Equals s.buffer uu____1427))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option * FStar_Parser_Dep.deps) = (fun filename -> (

let uu____1498 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____1498) with
| (deps, dep_graph1) -> begin
(

let uu____1521 = (FStar_List.partition (fun x -> (

let uu____1534 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____1535 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____1534 uu____1535)))) deps)
in (match (uu____1521) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____1564 = ((

let uu____1567 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____1567))) || (

let uu____1569 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____1569))))
in (match (uu____1564) with
| true -> begin
(

let uu____1570 = (

let uu____1575 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in ((FStar_Errors.Warning_MissingInterfaceOrImplementation), (uu____1575)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1570))
end
| uu____1576 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____1578 -> begin
((

let uu____1582 = (

let uu____1587 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in ((FStar_Errors.Warning_UnexpectedFile), (uu____1587)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1582));
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
| uu____1647 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____1662 = (FStar_Options.lax ())
in (push_with_kind env uu____1662 true "typecheck_modul"))
in (

let uu____1663 = (tc_one_file remaining env1)
in (match (uu____1663) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____1702 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____1715 = (FStar_Parser_ParseIt.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____1715))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Parser_ParseIt.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____1702) with
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
| (uu____1832, uu____1833) -> begin
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
| uu____1943 -> begin
((false), (depnames1))
end)
end
| uu____1946 -> begin
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
| uu____1971 -> begin
((false), (depnames1))
end)
end
| uu____1974 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____2047)::ts3 -> begin
((pop env1 "");
(

let uu____2088 = (

let uu____2103 = (FStar_List.hd stack)
in (

let uu____2112 = (FStar_List.tl stack)
in ((uu____2103), (uu____2112))))
in (match (uu____2088) with
| ((env2, uu____2134), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____2198 = ts_elt
in (match (uu____2198) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____2229 = (match_dep depnames intf impl)
in (match (uu____2229) with
| (b, depnames') -> begin
(

let uu____2248 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____2248) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____2264 -> begin
(

let uu____2265 = (

let uu____2274 = (FStar_List.hd st)
in (

let uu____2283 = (FStar_List.tl st)
in ((uu____2274), (uu____2283))))
in (match (uu____2265) with
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

let uu____2336 = (deps_of_our_file filename)
in (match (uu____2336) with
| (filenames, uu____2354, dep_graph1) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let format_info : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun env name typ range doc1 -> (

let uu____2441 = (FStar_Range.string_of_range range)
in (

let uu____2442 = (FStar_TypeChecker_Normalize.term_to_string env typ)
in (

let uu____2443 = (match (doc1) with
| FStar_Pervasives_Native.Some (docstring) -> begin
(FStar_Util.format1 "#doc %s" docstring)
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (FStar_Util.format4 "(defined at %s) %s: %s%s" uu____2441 name uu____2442 uu____2443)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  unit = (fun line_col filename stack curmod env ts -> (

let uu____2483 = (shift_chunk ())
in (match (uu____2483) with
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
| FStar_Pervasives_Native.Some (uu____2578) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2631 -> begin
(

let lid = (

let uu____2633 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split symbol "."))
in (FStar_Ident.lid_of_ids uu____2633))
in (

let lid1 = (match (fqn_only) with
| true -> begin
lid
end
| uu____2637 -> begin
(

let uu____2638 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____2638) with
| FStar_Pervasives_Native.None -> begin
lid
end
| FStar_Pervasives_Native.Some (lid1) -> begin
lid1
end))
end)
in (

let uu____2642 = (FStar_TypeChecker_Env.try_lookup_lid env lid1)
in (FStar_All.pipe_right uu____2642 (FStar_Util.map_option (fun uu____2697 -> (match (uu____2697) with
| ((uu____2716, typ), r) -> begin
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

let uu____2759 = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
((name), (FStar_Pervasives_Native.None))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____2776 = (FStar_Ident.string_of_lid lid)
in (

let uu____2777 = (

let uu____2780 = (FStar_Syntax_DsEnv.try_lookup_doc env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____2780 (FStar_Util.map_option FStar_Pervasives_Native.fst)))
in ((uu____2776), (uu____2777))))
end)
in (match (uu____2759) with
| (name, doc1) -> begin
(

let uu____2831 = (format_info env name typ rng doc1)
in (FStar_Util.print1 "%s\n#done-ok\n" uu____2831))
end))
end);
(go line_col filename stack curmod env ts);
)))
end
| Completions (search_term) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____2872) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____2887, []) -> begin
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
| uu____2937 -> begin
(

let uu____2940 = (measure_anchored_match ts1 tc1)
in (FStar_All.pipe_right uu____2940 (FStar_Util.map_option (fun uu____2980 -> (match (uu____2980) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____3001 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____3039 = (measure_anchored_match needle candidate)
in (match (uu____3039) with
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

let uu____3118 = (locate_match needle tc1)
in (FStar_All.pipe_right uu____3118 (FStar_Util.map_option (fun uu____3179 -> (match (uu____3179) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____3225 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____3225)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____3278 -> (match (uu____3278) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____3309)::[] -> begin
true
end
| uu____3310 -> begin
false
end)
in (

let uu____3313 = (FStar_Syntax_DsEnv.shorten_module_path env.FStar_TypeChecker_Env.dsenv prefix1 naked_match)
in (match (uu____3313) with
| (stripped_ns, shortened) -> begin
(

let uu____3340 = (str_of_ids shortened)
in (

let uu____3341 = (str_of_ids matched)
in (

let uu____3342 = (str_of_ids stripped_ns)
in ((uu____3340), (uu____3341), (uu____3342), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____3362 -> (match (uu____3362) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((Prims.op_Equality prefix1 "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____3387 -> begin
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

let uu____3496 = (FStar_Ident.ids_of_lid m)
in (

let uu____3499 = (FStar_Ident.id_of_text n1)
in (FStar_Ident.lid_of_ns_and_id uu____3496 uu____3499)))
in (

let uu____3500 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____3516 = (

let uu____3519 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____3519 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____3516), (matched_length)))) uu____3500)))
end
| uu____3526 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____3554 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____3629 -> (match (uu____3629) with
| (ns, id1, uu____3642) -> begin
(

let uu____3651 = (

let uu____3654 = (FStar_Ident.lid_of_ids id1)
in (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env.FStar_TypeChecker_Env.dsenv uu____3654))
in (match (uu____3651) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3656 = (FStar_Ident.lid_of_ids (FStar_List.append ns id1))
in (FStar_Ident.lid_equals l uu____3656))
end))
end))))))
in (

let uu____3657 = (FStar_Util.prefix needle)
in (match (uu____3657) with
| (ns, id1) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____3703 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____3707 = (FStar_Syntax_DsEnv.resolve_module_name env.FStar_TypeChecker_Env.dsenv l true)
in (match (uu____3707) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id1)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____3772 = (shorten_namespace x)
in (prepare_candidate uu____3772))))))
end))))
in ((

let uu____3782 = (FStar_Util.sort_with (fun uu____3805 uu____3806 -> (match (((uu____3805), (uu____3806))) with
| ((cd1, ns1, uu____3833), (cd2, ns2, uu____3836)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_1 when (_0_1 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.iter (fun uu____3861 -> (match (uu____3861) with
| (candidate, ns, match_len) -> begin
(

let uu____3871 = (FStar_Util.string_of_int match_len)
in (FStar_Util.print3 "%s %s %s \n" uu____3871 ns candidate))
end)) uu____3782));
(FStar_Util.print_string "#done-ok\n");
(go line_col filename stack curmod env ts);
))))))))))
end
| Pop (msg) -> begin
((pop env msg);
(

let uu____3875 = (match (stack) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_IDETooManyPops), ("too many pops")));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd1)::tl1 -> begin
((hd1), (tl1))
end)
in (match (uu____3875) with
| ((env1, curmod1), stack1) -> begin
(go line_col filename stack1 curmod1 env1 ts)
end));
)
end
| Push (lax1, l, c) -> begin
(

let uu____3935 = (match ((Prims.op_Equality (FStar_List.length stack) (FStar_List.length ts))) with
| true -> begin
(

let uu____3972 = (update_deps filename curmod stack env ts)
in ((true), (uu____3972)))
end
| uu____3985 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____3935) with
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
| uu____4062 -> begin
(fail2 curmod1 env1)
end)
end
| uu____4063 -> begin
(fail2 curmod env)
end))))
end)))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((

let uu____4080 = (

let uu____4081 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____4081))
in (match (uu____4080) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("code-generation is not supported in interactive mode, ignoring the codegen flag")))
end
| uu____4084 -> begin
()
end));
(

let uu____4085 = (deps_of_our_file filename)
in (match (uu____4085) with
| (filenames, maybe_intf, dep_graph1) -> begin
(

let env = (FStar_Universal.init_env dep_graph1)
in (

let uu____4108 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____4108) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____4135 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____4136 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____4135 uu____4136)))
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

let uu____4140 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____4140) with
| true -> begin
(

let uu____4141 = (

let uu____4142 = (FStar_Options.file_list ())
in (FStar_List.hd uu____4142))
in (FStar_SMTEncoding_Solver.with_hints_db uu____4141 (fun uu____4146 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts))))
end
| uu____4147 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts)
end)))))
end)))
end));
))




