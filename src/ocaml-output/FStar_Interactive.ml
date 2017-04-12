
open Prims

let tc_one_file = (fun remaining uenv -> (

let uu____26 = uenv
in (match (uu____26) with
| (dsenv, env) -> begin
(

let uu____40 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____61 = (FStar_Universal.tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (uu____61) with
| (uu____76, dsenv1, env1) -> begin
((((Some (intf)), (impl))), (dsenv1), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____93 = (FStar_Universal.tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (uu____93) with
| (uu____108, dsenv1, env1) -> begin
((((None), (intf_or_impl))), (dsenv1), (env1), (remaining1))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____40) with
| ((intf, impl), dsenv1, env1, remaining1) -> begin
((((intf), (impl))), (((dsenv1), (env1))), (None), (remaining1))
end))
end)))


let tc_prims : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____165 -> (

let uu____166 = (FStar_Universal.tc_prims ())
in (match (uu____166) with
| (uu____174, dsenv, env) -> begin
((dsenv), (env))
end)))


type env_t =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


type modul_t =
FStar_Syntax_Syntax.modul Prims.option


type stack_t =
(env_t * modul_t) Prims.list


let pop = (fun uu____199 msg -> (match (uu____199) with
| (uu____203, env) -> begin
((FStar_Universal.pop_context env msg);
(FStar_Options.pop ());
)
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____218 lax1 restore_cmd_line_options1 msg -> (match (uu____218) with
| (dsenv, env) -> begin
(

let env1 = (

let uu___217_229 = env
in {FStar_TypeChecker_Env.solver = uu___217_229.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___217_229.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___217_229.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___217_229.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___217_229.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___217_229.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___217_229.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___217_229.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___217_229.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___217_229.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___217_229.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___217_229.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___217_229.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___217_229.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___217_229.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___217_229.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___217_229.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___217_229.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___217_229.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___217_229.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___217_229.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___217_229.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___217_229.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (FStar_Universal.push_context ((dsenv), (env1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____235 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____235 Prims.ignore))
end
| uu____236 -> begin
()
end);
res;
)))
end))


let mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____243 -> (match (uu____243) with
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


let cleanup = (fun uu____279 -> (match (uu____279) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____290 -> (match (uu____290) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv1), (env1))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) Prims.option = (fun uu____315 curmod text1 -> (match (uu____315) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____345 = (FStar_Universal.tc_one_fragment curmod dsenv env text1)
in (match (uu____345) with
| Some (m, dsenv1, env1) -> begin
(

let uu____367 = (

let uu____374 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____374)))
in Some (uu____367))
end
| uu____384 -> begin
None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____406 = (FStar_Options.trace_error ())
in (not (uu____406))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____419 = (FStar_Options.trace_error ())
in (not (uu____419))) -> begin
((

let uu____421 = (

let uu____425 = (

let uu____428 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____428)))
in (uu____425)::[])
in (FStar_TypeChecker_Err.add_errors env uu____421));
None;
)
end
end))


let report_fail : Prims.unit  ->  Prims.unit = (fun uu____441 -> ((

let uu____443 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____443 Prims.ignore));
(FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0"));
))

type input_chunks =
| Push of (Prims.bool * Prims.int * Prims.int)
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))
| Info of (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int) Prims.option)
| Completions of Prims.string


let uu___is_Push : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____485 -> begin
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
| uu____506 -> begin
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
| uu____522 -> begin
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
| uu____553 -> begin
false
end))


let __proj__Info__item___0 : input_chunks  ->  (Prims.string * Prims.bool * (Prims.string * Prims.int * Prims.int) Prims.option) = (fun projectee -> (match (projectee) with
| Info (_0) -> begin
_0
end))


let uu___is_Completions : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Completions (_0) -> begin
true
end
| uu____586 -> begin
false
end))


let __proj__Completions__item___0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Completions (_0) -> begin
_0
end))

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let the_interactive_state : interactive_state = (

let uu____649 = (FStar_Util.new_string_builder ())
in (

let uu____650 = (FStar_Util.mk_ref None)
in (

let uu____655 = (FStar_Util.mk_ref [])
in (

let uu____660 = (FStar_Util.mk_ref None)
in {chunk = uu____649; stdin = uu____650; buffer = uu____655; log = uu____660}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun uu____673 -> (

let s = the_interactive_state
in (

let log = (

let uu____678 = (FStar_Options.debug_any ())
in (match (uu____678) with
| true -> begin
(

let transcript = (

let uu____682 = (FStar_ST.read s.log)
in (match (uu____682) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in ((FStar_ST.write s.log (Some (transcript)));
transcript;
))
end))
in (fun line -> ((FStar_Util.append_to_file transcript line);
(FStar_Util.flush_file transcript);
)))
end
| uu____695 -> begin
(fun uu____696 -> ())
end))
in (

let stdin = (

let uu____698 = (FStar_ST.read s.stdin)
in (match (uu____698) with
| Some (i) -> begin
i
end
| None -> begin
(

let i = (FStar_Util.open_stdin ())
in ((FStar_ST.write s.stdin (Some (i)));
i;
))
end))
in (

let line = (

let uu____710 = (FStar_Util.read_line stdin)
in (match (uu____710) with
| None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| Some (l) -> begin
l
end))
in ((log line);
(

let l = (FStar_Util.trim_string line)
in (match ((FStar_Util.starts_with l "#end")) with
| true -> begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (uu____720)::(ok)::(fail1)::[] -> begin
((ok), (fail1))
end
| uu____723 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____729 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____731 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____734 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____734))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l1)::(c)::("#lax")::[] -> begin
(

let uu____746 = (FStar_Util.int_of_string l1)
in (

let uu____747 = (FStar_Util.int_of_string c)
in ((true), (uu____746), (uu____747))))
end
| (l1)::(c)::[] -> begin
(

let uu____750 = (FStar_Util.int_of_string l1)
in (

let uu____751 = (FStar_Util.int_of_string c)
in ((false), (uu____750), (uu____751))))
end
| uu____752 -> begin
((FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____755 -> begin
(match ((FStar_Util.starts_with l "#info ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____756)::(symbol)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Info (((symbol), (true), (None)));
)
end
| (uu____766)::(symbol)::(file)::(row)::(col)::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let uu____772 = (

let uu____780 = (

let uu____785 = (

let uu____789 = (FStar_Util.int_of_string row)
in (

let uu____790 = (FStar_Util.int_of_string col)
in ((file), (uu____789), (uu____790))))
in Some (uu____785))
in ((symbol), (false), (uu____780)))
in Info (uu____772));
)
end
| uu____798 -> begin
((FStar_Util.print_error (Prims.strcat "Unrecognized \"#info\" request: " l));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____801 -> begin
(match ((FStar_Util.starts_with l "#completions ")) with
| true -> begin
(match ((FStar_Util.split l " ")) with
| (uu____802)::(prefix1)::("#")::[] -> begin
((FStar_Util.clear_string_builder s.chunk);
Completions (prefix1);
)
end
| uu____805 -> begin
((FStar_Util.print_error (Prims.strcat "Unrecognized \"#completions\" request: " l));
(FStar_All.exit (Prims.parse_int "1"));
)
end)
end
| uu____808 -> begin
(match ((l = "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____809 -> begin
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


let shift_chunk : Prims.unit  ->  input_chunks = (fun uu____814 -> (

let s = the_interactive_state
in (

let uu____816 = (FStar_ST.read s.buffer)
in (match (uu____816) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.write s.buffer chunks);
chunk;
)
end))))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun uu____830 -> (

let s = the_interactive_state
in (

let uu____832 = (

let uu____834 = (FStar_ST.read s.buffer)
in (

let uu____839 = (

let uu____841 = (read_chunk ())
in (uu____841)::[])
in (FStar_List.append uu____834 uu____839)))
in (FStar_ST.write s.buffer uu____832))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string Prims.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____854 = (FStar_List.partition (fun x -> (

let uu____860 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____861 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____860 <> uu____861)))) deps)
in (match (uu____854) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____878 = ((

let uu____879 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____879))) || (

let uu____880 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____880))))
in (match (uu____878) with
| true -> begin
(

let uu____881 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____881))
end
| uu____882 -> begin
()
end));
Some (intf);
)
end
| (impl)::[] -> begin
None
end
| uu____884 -> begin
((

let uu____887 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____887));
None;
)
end)
in ((deps1), (maybe_intf)))
end))))


type m_timestamps =
(Prims.string Prims.option * Prims.string * FStar_Util.time Prims.option * FStar_Util.time) Prims.list


let rec tc_deps : modul_t  ->  stack_t  ->  env_t  ->  Prims.string Prims.list  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| uu____920 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____931 = (FStar_Options.lax ())
in (push env uu____931 true "typecheck_modul"))
in (

let uu____932 = (tc_one_file remaining env1)
in (match (uu____932) with
| ((intf, impl), env2, modl, remaining1) -> begin
(

let uu____965 = (

let intf_t = (match (intf) with
| Some (intf1) -> begin
(

let uu____973 = (FStar_Util.get_file_last_modification_time intf1)
in Some (uu____973))
end
| None -> begin
None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____965) with
| (intf_t, impl_t) -> begin
(tc_deps m stack1 env2 remaining1 ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))


let update_deps : Prims.string  ->  modul_t  ->  stack_t  ->  env_t  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun filename m stk env ts -> (

let is_stale = (fun intf impl intf_t impl_t -> (

let impl_mt = (FStar_Util.get_file_last_modification_time impl)
in ((FStar_Util.is_before impl_t impl_mt) || (match (((intf), (intf_t))) with
| (Some (intf1), Some (intf_t1)) -> begin
(

let intf_mt = (FStar_Util.get_file_last_modification_time intf1)
in (FStar_Util.is_before intf_t1 intf_mt))
end
| (None, None) -> begin
false
end
| (uu____1039, uu____1040) -> begin
(failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts1 good_stack good_ts -> (

let match_dep = (fun depnames1 intf impl -> (match (intf) with
| None -> begin
(match (depnames1) with
| (dep1)::depnames' -> begin
(match ((dep1 = impl)) with
| true -> begin
((true), (depnames'))
end
| uu____1102 -> begin
((false), (depnames1))
end)
end
| uu____1104 -> begin
((false), (depnames1))
end)
end
| Some (intf1) -> begin
(match (depnames1) with
| (depintf)::(dep1)::depnames' -> begin
(match (((depintf = intf1) && (dep1 = impl))) with
| true -> begin
((true), (depnames'))
end
| uu____1119 -> begin
((false), (depnames1))
end)
end
| uu____1121 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____1168)::ts3 -> begin
((pop env1 "");
(

let uu____1190 = (

let uu____1198 = (FStar_List.hd stack)
in (

let uu____1203 = (FStar_List.tl stack)
in ((uu____1198), (uu____1203))))
in (match (uu____1190) with
| ((env2, uu____1217), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____1251 = ts_elt
in (match (uu____1251) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1269 = (match_dep depnames intf impl)
in (match (uu____1269) with
| (b, depnames') -> begin
(

let uu____1280 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1280) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____1291 -> begin
(

let uu____1292 = (

let uu____1300 = (FStar_List.hd st)
in (

let uu____1305 = (FStar_List.tl st)
in ((uu____1300), (uu____1305))))
in (match (uu____1292) with
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

let uu____1345 = (deps_of_our_file filename)
in (match (uu____1345) with
| (filenames, uu____1354) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  Prims.unit = (fun line_col filename stack curmod env ts -> (

let uu____1405 = (shift_chunk ())
in (match (uu____1405) with
| Info (symbol, fqn_only, pos_opt) -> begin
(

let uu____1417 = env
in (match (uu____1417) with
| (dsenv, tcenv) -> begin
(

let info_at_pos_opt = (match (pos_opt) with
| None -> begin
None
end
| Some (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos (Prims.snd env) file row col)
end)
in (

let info_opt = (match (info_at_pos_opt) with
| Some (uu____1460) -> begin
info_at_pos_opt
end
| None -> begin
(match ((symbol = "")) with
| true -> begin
None
end
| uu____1487 -> begin
(

let lid = (

let uu____1489 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split symbol "."))
in (FStar_Ident.lid_of_ids uu____1489))
in (

let lid1 = (match (fqn_only) with
| true -> begin
lid
end
| uu____1492 -> begin
(

let uu____1493 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____1493) with
| None -> begin
lid
end
| Some (lid1) -> begin
lid1
end))
end)
in (

let uu____1496 = (FStar_TypeChecker_Env.try_lookup_lid (Prims.snd env) lid1)
in (FStar_All.pipe_right uu____1496 (FStar_Util.map_option (fun uu____1522 -> (match (uu____1522) with
| ((uu____1532, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end)))))))
end)
end)
in ((match (info_opt) with
| None -> begin
(FStar_Util.print_string "\n#done-nok\n")
end
| Some (name_or_lid, typ, rng) -> begin
(

let uu____1557 = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
((name), (None))
end
| FStar_Util.Inr (lid) -> begin
(

let uu____1567 = (FStar_Ident.string_of_lid lid)
in (

let uu____1568 = (

let uu____1570 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____1570 (FStar_Util.map_option Prims.fst)))
in ((uu____1567), (uu____1568))))
end)
in (match (uu____1557) with
| (name, doc1) -> begin
(

let uu____1587 = (FStar_TypeChecker_Err.format_info (Prims.snd env) name typ rng doc1)
in (FStar_Util.print1 "%s\n#done-ok\n" uu____1587))
end))
end);
(go line_col filename stack curmod env ts);
)))
end))
end
| Completions (search_term) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____1610) -> begin
Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____1618, []) -> begin
None
end
| ((hs)::ts1, (hc)::tc) -> begin
(

let hc_text = (FStar_Ident.text_of_id hc)
in (match ((FStar_Util.starts_with hc_text hs)) with
| true -> begin
(match (ts1) with
| [] -> begin
Some (((candidate), ((FStar_String.length hs))))
end
| uu____1648 -> begin
(

let uu____1650 = (measure_anchored_match ts1 tc)
in (FStar_All.pipe_right uu____1650 (FStar_Util.map_option (fun uu____1669 -> (match (uu____1669) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____1684 -> begin
None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____1705 = (measure_anchored_match needle candidate)
in (match (uu____1705) with
| Some (matched, n1) -> begin
Some ((([]), (matched), (n1)))
end
| None -> begin
(match (candidate) with
| [] -> begin
None
end
| (hc)::tc -> begin
(

let uu____1747 = (locate_match needle tc)
in (FStar_All.pipe_right uu____1747 (FStar_Util.map_option (fun uu____1776 -> (match (uu____1776) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____1802 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____1802)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____1831 -> (match (uu____1831) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____1849)::[] -> begin
true
end
| uu____1850 -> begin
false
end)
in (

let uu____1852 = (FStar_ToSyntax_Env.shorten_module_path (Prims.fst env) prefix1 naked_match)
in (match (uu____1852) with
| (stripped_ns, shortened) -> begin
(

let uu____1867 = (str_of_ids shortened)
in (

let uu____1868 = (str_of_ids matched)
in (

let uu____1869 = (str_of_ids stripped_ns)
in ((uu____1867), (uu____1868), (uu____1869), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____1880 -> (match (uu____1880) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((prefix1 = "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____1895 -> begin
(((Prims.strcat prefix1 (Prims.strcat "." matched))), (stripped_ns), ((((FStar_String.length prefix1) + match_len) + (Prims.parse_int "1"))))
end)
end))
in (

let needle = (FStar_Util.split search_term ".")
in (

let all_lidents_in_env = (FStar_TypeChecker_Env.lidents (Prims.snd env))
in (

let matches = (

let case_a_find_transitive_includes = (fun orig_ns m id -> (

let dsenv = (Prims.fst env)
in (

let exported_names = (FStar_ToSyntax_Env.transitive_exported_ids dsenv m)
in (

let matched_length = (FStar_List.fold_left (fun out s -> (((FStar_String.length s) + out) + (Prims.parse_int "1"))) (FStar_String.length id) orig_ns)
in (FStar_All.pipe_right exported_names (FStar_List.filter_map (fun n1 -> (match ((FStar_Util.starts_with n1 id)) with
| true -> begin
(

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m) (FStar_Ident.id_of_text n1))
in (

let uu____1963 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____1971 = (

let uu____1973 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____1973 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____1971), (matched_length)))) uu____1963)))
end
| uu____1977 -> begin
None
end))))))))
in (

let case_b_find_matches_in_env = (fun uu____1992 -> (

let uu____1999 = env
in (match (uu____1999) with
| (dsenv, uu____2007) -> begin
(

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____2037 -> (match (uu____2037) with
| (ns, id, uu____2045) -> begin
(

let uu____2050 = (

let uu____2052 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____2052))
in (match (uu____2050) with
| None -> begin
false
end
| Some (l) -> begin
(

let uu____2054 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____2054))
end))
end)))))
end)))
in (

let uu____2055 = (FStar_Util.prefix needle)
in (match (uu____2055) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____2080 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____2083 = (FStar_ToSyntax_Env.resolve_module_name (Prims.fst env) l true)
in (match (uu____2083) with
| None -> begin
(case_b_find_matches_in_env ())
end
| Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____2116 = (shorten_namespace x)
in (prepare_candidate uu____2116))))))
end))))
in ((

let uu____2122 = (FStar_Util.sort_with (fun uu____2130 uu____2131 -> (match (((uu____2130), (uu____2131))) with
| ((cd1, ns1, uu____2146), (cd2, ns2, uu____2149)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_32 when (_0_32 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.iter (fun uu____2160 -> (match (uu____2160) with
| (candidate, ns, match_len) -> begin
(

let uu____2167 = (FStar_Util.string_of_int match_len)
in (FStar_Util.print3 "%s %s %s \n" uu____2167 ns candidate))
end)) uu____2122));
(FStar_Util.print_string "#done-ok\n");
(go line_col filename stack curmod env ts);
))))))))))
end
| Pop (msg) -> begin
((pop env msg);
(

let uu____2171 = (match (stack) with
| [] -> begin
((FStar_Util.print_error "too many pops");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd1)::tl1 -> begin
((hd1), (tl1))
end)
in (match (uu____2171) with
| ((env1, curmod1), stack1) -> begin
((match (((FStar_List.length stack1) = (FStar_List.length ts))) with
| true -> begin
(cleanup env1)
end
| uu____2234 -> begin
()
end);
(go line_col filename stack1 curmod1 env1 ts);
)
end));
)
end
| Push (lax1, l, c) -> begin
(

let uu____2238 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(

let uu____2261 = (update_deps filename curmod stack env ts)
in ((true), (uu____2261)))
end
| uu____2268 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____2238) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (curmod)))::stack1
in (

let env2 = (push env1 lax1 restore_cmd_line_options1 "#push")
in (go ((l), (c)) filename stack2 curmod env2 ts1)))
end))
end
| Code (text1, (ok, fail1)) -> begin
(

let fail2 = (fun curmod1 env_mark -> ((report_fail ());
(FStar_Util.print1 "%s\n" fail1);
(

let env1 = (reset_mark env_mark)
in (go line_col filename stack curmod1 env1 ts));
))
in (

let env_mark = (mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = (Prims.fst line_col); FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)}
in (

let res = (check_frag env_mark curmod frag)
in (match (res) with
| Some (curmod1, env1, n_errs) -> begin
(match ((n_errs = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print1 "\n%s\n" ok);
(

let env2 = (commit_mark env1)
in (go line_col filename stack curmod1 env2 ts));
)
end
| uu____2340 -> begin
(fail2 curmod1 env_mark)
end)
end
| uu____2341 -> begin
(fail2 curmod env_mark)
end)))))
end)))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((

let uu____2353 = (

let uu____2354 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____2354))
in (match (uu____2353) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____2356 -> begin
()
end));
(

let uu____2357 = (deps_of_our_file filename)
in (match (uu____2357) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____2371 = (tc_deps None [] env filenames [])
in (match (uu____2371) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____2387 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____2388 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____2387 uu____2388)))
in (

let env2 = (

let uu____2392 = (FStar_TypeChecker_Env.set_range (Prims.snd env1) initial_range)
in (((Prims.fst env1)), (uu____2392)))
in (

let uu____2393 = (match (maybe_intf) with
| Some (intf) -> begin
(

let frag = (

let uu____2406 = (FStar_Util.file_get_contents intf)
in {FStar_Parser_ParseIt.frag_text = uu____2406; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")})
in (

let uu____2407 = (check_frag env2 None frag)
in (match (uu____2407) with
| Some (curmod, env3, n_errs) -> begin
((match ((n_errs <> (Prims.parse_int "0"))) with
| true -> begin
((

let uu____2437 = (FStar_Util.format1 "Found the interface %s but it has errors!" intf)
in (FStar_Util.print_warning uu____2437));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____2438 -> begin
()
end);
(FStar_Util.print_string "Reminder: fst+fsti in interactive mode is unsound.\n");
((curmod), (env3));
)
end
| None -> begin
((

let uu____2450 = (FStar_Util.format1 "Found the interface %s but could not parse it first!" intf)
in (FStar_Util.print_warning uu____2450));
(FStar_All.exit (Prims.parse_int "1"));
)
end)))
end
| None -> begin
((None), (env2))
end)
in (match (uu____2393) with
| (initial_mod, env3) -> begin
(

let uu____2467 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____2467) with
| true -> begin
(

let uu____2468 = (

let uu____2469 = (FStar_Options.file_list ())
in (FStar_List.hd uu____2469))
in (FStar_SMTEncoding_Solver.with_hints_db uu____2468 (fun uu____2471 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack initial_mod env3 ts))))
end
| uu____2472 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack initial_mod env3 ts)
end))
end))))
end)))
end));
))




