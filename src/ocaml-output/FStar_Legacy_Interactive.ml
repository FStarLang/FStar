
open Prims
open FStar_Pervasives

let tc_one_file : Prims.string Prims.list  ->  FStar_Universal.uenv  ->  ((Prims.string FStar_Pervasives_Native.option * Prims.string) * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.string Prims.list) = (fun remaining uenv -> (

let uu____20 = uenv
in (match (uu____20) with
| (dsenv, env) -> begin
(

let uu____32 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____53 = (FStar_Universal.tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____53) with
| (uu____68, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.Some (intf)), (impl))), (dsenv1), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____85 = (FStar_Universal.tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____85) with
| (uu____100, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.None), (intf_or_impl))), (dsenv1), (env1), (remaining1))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____32) with
| ((intf, impl), dsenv1, env1, remaining1) -> begin
((((intf), (impl))), (((dsenv1), (env1))), (remaining1))
end))
end)))


let tc_prims : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____155 -> (

let uu____156 = (FStar_Universal.tc_prims ())
in (match (uu____156) with
| (uu____164, dsenv, env) -> begin
((dsenv), (env))
end)))


type env_t =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let pop = (fun uu____192 msg -> (match (uu____192) with
| (uu____196, env) -> begin
((FStar_Universal.pop_context env msg);
(FStar_Options.pop ());
)
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____215 lax1 restore_cmd_line_options1 msg -> (match (uu____215) with
| (dsenv, env) -> begin
(

let env1 = (

let uu___210_226 = env
in {FStar_TypeChecker_Env.solver = uu___210_226.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___210_226.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___210_226.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___210_226.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___210_226.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___210_226.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___210_226.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___210_226.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___210_226.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___210_226.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___210_226.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___210_226.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___210_226.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___210_226.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___210_226.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___210_226.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___210_226.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___210_226.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___210_226.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___210_226.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___210_226.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___210_226.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___210_226.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___210_226.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___210_226.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___210_226.FStar_TypeChecker_Env.is_native_tactic})
in (

let res = (FStar_Universal.push_context ((dsenv), (env1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____232 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____232 FStar_Pervasives.ignore))
end
| uu____233 -> begin
()
end);
res;
)))
end))


let mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____241 -> (match (uu____241) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv1), (env1));
)))
end))


let reset_mark = (fun uu____263 -> (match (uu____263) with
| (uu____266, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark ())
in (

let env1 = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env1));
)))
end))


let cleanup = (fun uu____281 -> (match (uu____281) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____293 -> (match (uu____293) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv1), (env1))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____323 curmod frag -> (match (uu____323) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____361 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____361) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____383 = (

let uu____390 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____390)))
in FStar_Pervasives_Native.Some (uu____383))
end
| uu____400 -> begin
FStar_Pervasives_Native.None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____426 = (FStar_Options.trace_error ())
in (not (uu____426))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____439 = (FStar_Options.trace_error ())
in (not (uu____439))) -> begin
((

let uu____441 = (

let uu____445 = (

let uu____448 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____448)))
in (uu____445)::[])
in (FStar_TypeChecker_Err.add_errors env uu____441));
FStar_Pervasives_Native.None;
)
end
end))


let report_fail : Prims.unit  ->  Prims.unit = (fun uu____462 -> ((

let uu____464 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____464 FStar_Pervasives.ignore));
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
| uu____510 -> begin
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
| uu____533 -> begin
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
| uu____551 -> begin
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
| uu____584 -> begin
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
| uu____619 -> begin
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

let uu____730 = (FStar_Util.new_string_builder ())
in (

let uu____731 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____736 = (FStar_Util.mk_ref [])
in (

let uu____741 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {chunk = uu____730; stdin = uu____731; buffer = uu____736; log = uu____741}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun uu____755 -> (

let s = the_interactive_state
in (

let log1 = (

let uu____760 = (FStar_Options.debug_any ())
in (match (uu____760) with
| true -> begin
(

let transcript = (

let uu____764 = (FStar_ST.read s.log)
in (match (uu____764) with
| FStar_Pervasives_Native.Some (transcript) -> begin
transcript
end
| FStar_Pervasives_Native.None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in ((FStar_ST.write s.log (FStar_Pervasives_Native.Some (transcript)));
transcript;
))
end))
in (fun line -> ((FStar_Util.append_to_file transcript line);
(FStar_Util.flush_file transcript);
)))
end
| uu____777 -> begin
(fun uu____778 -> ())
end))
in (

let stdin = (

let uu____780 = (FStar_ST.read s.stdin)
in (match (uu____780) with
| FStar_Pervasives_Native.Some (i) -> begin
i
end
| FStar_Pervasives_Native.None -> begin
(

let i = (FStar_Util.open_stdin ())
in ((FStar_ST.write s.stdin (FStar_Pervasives_Native.Some (i)));
i;
))
end))
in (

let line = (

let uu____792 = (FStar_Util.read_line stdin)
in (match (uu____792) with
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
| (uu____802)::(ok)::(fail4)::[] -> begin
((ok), (fail4))
end
| uu____805 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____811 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____813 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____816 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____816))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l1)::(c)::("#lax")::[] -> begin
(

let uu____830 = (FStar_Util.int_of_string l1)
in (

let uu____831 = (FStar_Util.int_of_string c)
in ((true), (uu____830), (uu____831))))
end
| (l1)::(c)::[] -> begin
(

let uu____834 = (FStar_Util.int_of_string l1)
in (

let uu____835 = (FStar_Util.int_of_string c)
in ((false), (uu____834), (uu____835))))
end
| uu____836 -> begin
((FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____839 -> begin
(match ((FStar_Util.starts_with l "#info ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____840)::(symbol)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Info (((symbol), (true), (FStar_Pervasives_Native.None)));
)
end
| (uu____850)::(symbol)::(file)::(row)::(col)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let uu____856 = (

let uu____864 = (

let uu____869 = (

let uu____873 = (FStar_Util.int_of_string row)
in (

let uu____874 = (FStar_Util.int_of_string col)
in ((file), (uu____873), (uu____874))))
in FStar_Pervasives_Native.Some (uu____869))
in ((symbol), (false), (uu____864)))
in Info (uu____856));
)
end
| uu____882 -> begin
((FStar_Util.print_error (Prims.strcat "Unrecognized \"#info\" request: " l));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____885 -> begin
(match ((FStar_Util.starts_with l "#completions ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____886)::(prefix1)::("#")::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Completions (prefix1);
)
end
| uu____889 -> begin
((FStar_Util.print_error (Prims.strcat "Unrecognized \"#completions\" request: " l));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____892 -> begin
(match ((l = "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____893 -> begin
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


let shift_chunk : Prims.unit  ->  input_chunks = (fun uu____899 -> (

let s = the_interactive_state
in (

let uu____901 = (FStar_ST.read s.buffer)
in (match (uu____901) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.write s.buffer chunks);
chunk;
)
end))))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun uu____916 -> (

let s = the_interactive_state
in (

let uu____918 = (

let uu____920 = (FStar_ST.read s.buffer)
in (

let uu____925 = (

let uu____927 = (read_chunk ())
in (uu____927)::[])
in (FStar_List.append uu____920 uu____925)))
in (FStar_ST.write s.buffer uu____918))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____941 = (FStar_List.partition (fun x -> (

let uu____950 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____951 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____950 <> uu____951)))) deps)
in (match (uu____941) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____968 = ((

let uu____971 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____971))) || (

let uu____973 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____973))))
in (match (uu____968) with
| true -> begin
(

let uu____974 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____974))
end
| uu____975 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____977 -> begin
((

let uu____980 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____980));
FStar_Pervasives_Native.None;
)
end)
in ((deps1), (maybe_intf)))
end))))


type m_timestamps =
(Prims.string FStar_Pervasives_Native.option * Prims.string * FStar_Util.time FStar_Pervasives_Native.option * FStar_Util.time) Prims.list


let rec tc_deps : modul_t  ->  stack_t  ->  env_t  ->  Prims.string Prims.list  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| uu____1018 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____1029 = (FStar_Options.lax ())
in (push env uu____1029 true "typecheck_modul"))
in (

let uu____1030 = (tc_one_file remaining env1)
in (match (uu____1030) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____1058 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____1066 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____1066))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____1058) with
| (intf_t, impl_t) -> begin
(tc_deps m stack1 env2 remaining1 ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))


let update_deps : Prims.string  ->  modul_t  ->  stack_t  ->  env_t  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun filename m stk env ts -> (

let is_stale = (fun intf impl intf_t impl_t -> (

let impl_mt = (FStar_Util.get_file_last_modification_time impl)
in ((FStar_Util.is_before impl_t impl_mt) || (match (((intf), (intf_t))) with
| (FStar_Pervasives_Native.Some (intf1), FStar_Pervasives_Native.Some (intf_t1)) -> begin
(

let intf_mt = (FStar_Util.get_file_last_modification_time intf1)
in (FStar_Util.is_before intf_t1 intf_mt))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
false
end
| (uu____1140, uu____1141) -> begin
(failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts1 good_stack good_ts -> (

let match_dep = (fun depnames1 intf impl -> (match (intf) with
| FStar_Pervasives_Native.None -> begin
(match (depnames1) with
| (dep1)::depnames' -> begin
(match ((dep1 = impl)) with
| true -> begin
((true), (depnames'))
end
| uu____1203 -> begin
((false), (depnames1))
end)
end
| uu____1205 -> begin
((false), (depnames1))
end)
end
| FStar_Pervasives_Native.Some (intf1) -> begin
(match (depnames1) with
| (depintf)::(dep1)::depnames' -> begin
(match (((depintf = intf1) && (dep1 = impl))) with
| true -> begin
((true), (depnames'))
end
| uu____1220 -> begin
((false), (depnames1))
end)
end
| uu____1222 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____1269)::ts3 -> begin
((pop env1 "");
(

let uu____1291 = (

let uu____1299 = (FStar_List.hd stack)
in (

let uu____1304 = (FStar_List.tl stack)
in ((uu____1299), (uu____1304))))
in (match (uu____1291) with
| ((env2, uu____1318), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____1352 = ts_elt
in (match (uu____1352) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1370 = (match_dep depnames intf impl)
in (match (uu____1370) with
| (b, depnames') -> begin
(

let uu____1381 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1381) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____1392 -> begin
(

let uu____1393 = (

let uu____1401 = (FStar_List.hd st)
in (

let uu____1406 = (FStar_List.tl st)
in ((uu____1401), (uu____1406))))
in (match (uu____1393) with
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

let uu____1446 = (deps_of_our_file filename)
in (match (uu____1446) with
| (filenames, uu____1455) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let format_info : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.term  ->  FStar_Range.range  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string = (fun env name typ range doc1 -> (

let uu____1506 = (FStar_Range.string_of_range range)
in (

let uu____1507 = (FStar_TypeChecker_Normalize.term_to_string env typ)
in (

let uu____1508 = (match (doc1) with
| FStar_Pervasives_Native.Some (docstring) -> begin
(FStar_Util.format1 "#doc %s" docstring)
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (FStar_Util.format4 "(defined at %s) %s: %s%s" uu____1506 name uu____1507 uu____1508)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  Prims.unit = (fun line_col filename stack curmod env ts -> (

let uu____1538 = (shift_chunk ())
in (match (uu____1538) with
| Info (symbol, fqn_only, pos_opt) -> begin
(

let uu____1550 = env
in (match (uu____1550) with
| (dsenv, tcenv) -> begin
(

let info_at_pos_opt = (match (pos_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos (FStar_Pervasives_Native.snd env) file row col)
end)
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____1593) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((symbol = "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____1620 -> begin
(

let lid = (

let uu____1622 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split symbol "."))
in (FStar_Ident.lid_of_ids uu____1622))
in (

let lid1 = (match (fqn_only) with
| true -> begin
lid
end
| uu____1625 -> begin
(

let uu____1626 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____1626) with
| FStar_Pervasives_Native.None -> begin
lid
end
| FStar_Pervasives_Native.Some (lid1) -> begin
lid1
end))
end)
in (

let uu____1629 = (FStar_TypeChecker_Env.try_lookup_lid (FStar_Pervasives_Native.snd env) lid1)
in (FStar_All.pipe_right uu____1629 (FStar_Util.map_option (fun uu____1659 -> (match (uu____1659) with
| ((uu____1669, typ), r) -> begin
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

let uu____1694 = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
((name), (FStar_Pervasives_Native.None))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____1704 = (FStar_Ident.string_of_lid lid)
in (

let uu____1705 = (

let uu____1707 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____1707 (FStar_Util.map_option FStar_Pervasives_Native.fst)))
in ((uu____1704), (uu____1705))))
end)
in (match (uu____1694) with
| (name, doc1) -> begin
(

let uu____1724 = (format_info (FStar_Pervasives_Native.snd env) name typ rng doc1)
in (FStar_Util.print1 "%s\n#done-ok\n" uu____1724))
end))
end);
(go line_col filename stack curmod env ts);
)))
end))
end
| Completions (search_term) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____1747) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____1755, []) -> begin
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
| uu____1787 -> begin
(

let uu____1789 = (measure_anchored_match ts1 tc)
in (FStar_All.pipe_right uu____1789 (FStar_Util.map_option (fun uu____1811 -> (match (uu____1811) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____1829 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____1850 = (measure_anchored_match needle candidate)
in (match (uu____1850) with
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

let uu____1892 = (locate_match needle tc)
in (FStar_All.pipe_right uu____1892 (FStar_Util.map_option (fun uu____1925 -> (match (uu____1925) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____1951 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____1951)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____1980 -> (match (uu____1980) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____1998)::[] -> begin
true
end
| uu____1999 -> begin
false
end)
in (

let uu____2001 = (FStar_ToSyntax_Env.shorten_module_path (FStar_Pervasives_Native.fst env) prefix1 naked_match)
in (match (uu____2001) with
| (stripped_ns, shortened) -> begin
(

let uu____2016 = (str_of_ids shortened)
in (

let uu____2017 = (str_of_ids matched)
in (

let uu____2018 = (str_of_ids stripped_ns)
in ((uu____2016), (uu____2017), (uu____2018), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____2029 -> (match (uu____2029) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((prefix1 = "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____2044 -> begin
(((Prims.strcat prefix1 (Prims.strcat "." matched))), (stripped_ns), ((((FStar_String.length prefix1) + match_len) + (Prims.parse_int "1"))))
end)
end))
in (

let needle = (FStar_Util.split search_term ".")
in (

let all_lidents_in_env = (FStar_TypeChecker_Env.lidents (FStar_Pervasives_Native.snd env))
in (

let matches = (

let case_a_find_transitive_includes = (fun orig_ns m id -> (

let dsenv = (FStar_Pervasives_Native.fst env)
in (

let exported_names = (FStar_ToSyntax_Env.transitive_exported_ids dsenv m)
in (

let matched_length = (FStar_List.fold_left (fun out s -> (((FStar_String.length s) + out) + (Prims.parse_int "1"))) (FStar_String.length id) orig_ns)
in (FStar_All.pipe_right exported_names (FStar_List.filter_map (fun n1 -> (match ((FStar_Util.starts_with n1 id)) with
| true -> begin
(

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m) (FStar_Ident.id_of_text n1))
in (

let uu____2125 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____2135 = (

let uu____2137 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____2137 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____2135), (matched_length)))) uu____2125)))
end
| uu____2141 -> begin
FStar_Pervasives_Native.None
end))))))))
in (

let case_b_find_matches_in_env = (fun uu____2156 -> (

let uu____2163 = env
in (match (uu____2163) with
| (dsenv, uu____2171) -> begin
(

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____2206 -> (match (uu____2206) with
| (ns, id, uu____2214) -> begin
(

let uu____2219 = (

let uu____2221 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____2221))
in (match (uu____2219) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____2223 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____2223))
end))
end)))))
end)))
in (

let uu____2224 = (FStar_Util.prefix needle)
in (match (uu____2224) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____2249 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____2252 = (FStar_ToSyntax_Env.resolve_module_name (FStar_Pervasives_Native.fst env) l true)
in (match (uu____2252) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____2287 = (shorten_namespace x)
in (prepare_candidate uu____2287))))))
end))))
in ((

let uu____2293 = (FStar_Util.sort_with (fun uu____2309 uu____2310 -> (match (((uu____2309), (uu____2310))) with
| ((cd1, ns1, uu____2325), (cd2, ns2, uu____2328)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_48 when (_0_48 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.iter (fun uu____2344 -> (match (uu____2344) with
| (candidate, ns, match_len) -> begin
(

let uu____2351 = (FStar_Util.string_of_int match_len)
in (FStar_Util.print3 "%s %s %s \n" uu____2351 ns candidate))
end)) uu____2293));
(FStar_Util.print_string "#done-ok\n");
(go line_col filename stack curmod env ts);
))))))))))
end
| Pop (msg) -> begin
((pop env msg);
(

let uu____2355 = (match (stack) with
| [] -> begin
((FStar_Util.print_error "too many pops");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd1)::tl1 -> begin
((hd1), (tl1))
end)
in (match (uu____2355) with
| ((env1, curmod1), stack1) -> begin
((match (((FStar_List.length stack1) = (FStar_List.length ts))) with
| true -> begin
(cleanup env1)
end
| uu____2422 -> begin
()
end);
(go line_col filename stack1 curmod1 env1 ts);
)
end));
)
end
| Push (lax1, l, c) -> begin
(

let uu____2426 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(

let uu____2453 = (update_deps filename curmod stack env ts)
in ((true), (uu____2453)))
end
| uu____2460 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____2426) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (curmod)))::stack1
in (

let env2 = (push env1 lax1 restore_cmd_line_options1 "#push")
in (go ((l), (c)) filename stack2 curmod env2 ts1)))
end))
end
| Code (text1, (ok, fail4)) -> begin
(

let fail5 = (fun curmod1 env_mark -> ((report_fail ());
(FStar_Util.print1 "%s\n" fail4);
(

let env1 = (reset_mark env_mark)
in (go line_col filename stack curmod1 env1 ts));
))
in (

let env_mark = (mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = (FStar_Pervasives_Native.fst line_col); FStar_Parser_ParseIt.frag_col = (FStar_Pervasives_Native.snd line_col)}
in (

let res = (check_frag env_mark curmod ((frag), (false)))
in (match (res) with
| FStar_Pervasives_Native.Some (curmod1, env1, n_errs) -> begin
(match ((n_errs = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print1 "\n%s\n" ok);
(

let env2 = (commit_mark env1)
in (go line_col filename stack curmod1 env2 ts));
)
end
| uu____2532 -> begin
(fail5 curmod1 env_mark)
end)
end
| uu____2533 -> begin
(fail5 curmod env_mark)
end)))))
end)))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((

let uu____2546 = (

let uu____2547 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____2547))
in (match (uu____2546) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____2549 -> begin
()
end));
(

let uu____2550 = (deps_of_our_file filename)
in (match (uu____2550) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____2564 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____2564) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____2580 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____2581 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____2580 uu____2581)))
in (

let env2 = (

let uu____2585 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env1) initial_range)
in (((FStar_Pervasives_Native.fst env1)), (uu____2585)))
in (

let env3 = (match (maybe_intf) with
| FStar_Pervasives_Native.Some (intf) -> begin
(FStar_Universal.load_interface_decls env2 intf)
end
| FStar_Pervasives_Native.None -> begin
env2
end)
in (

let uu____2592 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____2592) with
| true -> begin
(

let uu____2593 = (

let uu____2594 = (FStar_Options.file_list ())
in (FStar_List.hd uu____2594))
in (FStar_SMTEncoding_Solver.with_hints_db uu____2593 (fun uu____2597 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts))))
end
| uu____2598 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack FStar_Pervasives_Native.None env3 ts)
end)))))
end)))
end));
))




