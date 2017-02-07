
open Prims

let tc_one_file = (fun remaining uenv -> (

let uu____26 = uenv
in (match (uu____26) with
| (dsenv, env) -> begin
(

let uu____40 = (match (remaining) with
| (intf)::(impl)::remaining when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____61 = (FStar_Universal.tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (uu____61) with
| (uu____76, dsenv, env) -> begin
((((Some (intf)), (impl))), (dsenv), (env), (remaining))
end))
end
| (intf_or_impl)::remaining -> begin
(

let uu____93 = (FStar_Universal.tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (uu____93) with
| (uu____108, dsenv, env) -> begin
((((None), (intf_or_impl))), (dsenv), (env), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____40) with
| ((intf, impl), dsenv, env, remaining) -> begin
((((intf), (impl))), (((dsenv), (env))), (None), (remaining))
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


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____218 lax restore_cmd_line_options msg -> (match (uu____218) with
| (dsenv, env) -> begin
(

let env = (

let uu___164_229 = env
in {FStar_TypeChecker_Env.solver = uu___164_229.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___164_229.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___164_229.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___164_229.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___164_229.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___164_229.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___164_229.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___164_229.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___164_229.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___164_229.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___164_229.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___164_229.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___164_229.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___164_229.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___164_229.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___164_229.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___164_229.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___164_229.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___164_229.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___164_229.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___164_229.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___164_229.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___164_229.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (FStar_Universal.push_context ((dsenv), (env)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options) with
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

let dsenv = (FStar_ToSyntax_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv), (env));
)))
end))


let reset_mark = (fun uu____263 -> (match (uu____263) with
| (uu____266, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark ())
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env));
)))
end))


let cleanup = (fun uu____279 -> (match (uu____279) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____290 -> (match (uu____290) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) Prims.option = (fun uu____315 curmod text -> (match (uu____315) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____345 = (FStar_Universal.tc_one_fragment curmod dsenv env text)
in (match (uu____345) with
| Some (m, dsenv, env) -> begin
(

let uu____367 = (

let uu____374 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (uu____374)))
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


let uu___is_Push : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____472 -> begin
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
| uu____493 -> begin
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
| uu____509 -> begin
false
end))


let __proj__Code__item___0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_0) -> begin
_0
end))

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let the_interactive_state : interactive_state = (

let uu____584 = (FStar_Util.new_string_builder ())
in (

let uu____585 = (FStar_Util.mk_ref None)
in (

let uu____590 = (FStar_Util.mk_ref [])
in (

let uu____595 = (FStar_Util.mk_ref None)
in {chunk = uu____584; stdin = uu____585; buffer = uu____590; log = uu____595}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun uu____608 -> (

let s = the_interactive_state
in (

let log = (

let uu____613 = (FStar_Options.debug_any ())
in (match (uu____613) with
| true -> begin
(

let transcript = (

let uu____617 = (FStar_ST.read s.log)
in (match (uu____617) with
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
| uu____630 -> begin
(fun uu____631 -> ())
end))
in (

let stdin = (

let uu____633 = (FStar_ST.read s.stdin)
in (match (uu____633) with
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

let uu____645 = (FStar_Util.read_line stdin)
in (match (uu____645) with
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
| (uu____655)::(ok)::(fail)::[] -> begin
((ok), (fail))
end
| uu____658 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____664 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____666 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (

let uu____669 = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (FStar_Util.trim_string uu____669))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l)::(c)::("#lax")::[] -> begin
(

let uu____681 = (FStar_Util.int_of_string l)
in (

let uu____682 = (FStar_Util.int_of_string c)
in ((true), (uu____681), (uu____682))))
end
| (l)::(c)::[] -> begin
(

let uu____685 = (FStar_Util.int_of_string l)
in (

let uu____686 = (FStar_Util.int_of_string c)
in ((false), (uu____685), (uu____686))))
end
| uu____687 -> begin
((FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____690 -> begin
(match ((l = "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____691 -> begin
((FStar_Util.string_builder_append s.chunk line);
(FStar_Util.string_builder_append s.chunk "\n");
(read_chunk ());
)
end)
end)
end)
end));
))))))


let shift_chunk : Prims.unit  ->  input_chunks = (fun uu____696 -> (

let s = the_interactive_state
in (

let uu____698 = (FStar_ST.read s.buffer)
in (match (uu____698) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.write s.buffer chunks);
chunk;
)
end))))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun uu____712 -> (

let s = the_interactive_state
in (

let uu____714 = (

let uu____716 = (FStar_ST.read s.buffer)
in (

let uu____721 = (

let uu____723 = (read_chunk ())
in (uu____723)::[])
in (FStar_List.append uu____716 uu____721)))
in (FStar_ST.write s.buffer uu____714))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string Prims.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____736 = (FStar_List.partition (fun x -> (

let uu____742 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____743 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____742 <> uu____743)))) deps)
in (match (uu____736) with
| (deps, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____760 = ((

let uu____761 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____761))) || (

let uu____762 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____762))))
in (match (uu____760) with
| true -> begin
(

let uu____763 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____763))
end
| uu____764 -> begin
()
end));
Some (intf);
)
end
| (impl)::[] -> begin
None
end
| uu____766 -> begin
((

let uu____769 = (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____769));
None;
)
end)
in ((deps), (maybe_intf)))
end))))


type m_timestamps =
(Prims.string Prims.option * Prims.string * FStar_Util.time Prims.option * FStar_Util.time) Prims.list


let rec tc_deps : modul_t  ->  stack_t  ->  env_t  ->  Prims.string Prims.list  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| uu____802 -> begin
(

let stack = (((env), (m)))::stack
in (

let env = (

let uu____813 = (FStar_Options.lax ())
in (push env uu____813 true "typecheck_modul"))
in (

let uu____814 = (tc_one_file remaining env)
in (match (uu____814) with
| ((intf, impl), env, modl, remaining) -> begin
(

let uu____847 = (

let intf_t = (match (intf) with
| Some (intf) -> begin
(

let uu____855 = (FStar_Util.get_file_last_modification_time intf)
in Some (uu____855))
end
| None -> begin
None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____847) with
| (intf_t, impl_t) -> begin
(tc_deps m stack env remaining ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))


let update_deps : Prims.string  ->  modul_t  ->  stack_t  ->  env_t  ->  m_timestamps  ->  (stack_t * env_t * m_timestamps) = (fun filename m stk env ts -> (

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
| (uu____921, uu____922) -> begin
(failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts good_stack good_ts -> (

let match_dep = (fun depnames intf impl -> (match (intf) with
| None -> begin
(match (depnames) with
| (dep)::depnames' -> begin
(match ((dep = impl)) with
| true -> begin
((true), (depnames'))
end
| uu____984 -> begin
((false), (depnames))
end)
end
| uu____986 -> begin
((false), (depnames))
end)
end
| Some (intf) -> begin
(match (depnames) with
| (depintf)::(dep)::depnames' -> begin
(match (((depintf = intf) && (dep = impl))) with
| true -> begin
((true), (depnames'))
end
| uu____1001 -> begin
((false), (depnames))
end)
end
| uu____1003 -> begin
((false), (depnames))
end)
end))
in (

let rec pop_tc_and_stack = (fun env stack ts -> (match (ts) with
| [] -> begin
env
end
| (uu____1050)::ts -> begin
((pop env "");
(

let uu____1072 = (

let uu____1080 = (FStar_List.hd stack)
in (

let uu____1085 = (FStar_List.tl stack)
in ((uu____1080), (uu____1085))))
in (match (uu____1072) with
| ((env, uu____1099), stack) -> begin
(pop_tc_and_stack env stack ts)
end));
)
end))
in (match (ts) with
| (ts_elt)::ts' -> begin
(

let uu____1133 = ts_elt
in (match (uu____1133) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1151 = (match_dep depnames intf impl)
in (match (uu____1151) with
| (b, depnames') -> begin
(

let uu____1162 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1162) with
| true -> begin
(

let env = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts)
in (tc_deps m good_stack env depnames good_ts))
end
| uu____1173 -> begin
(

let uu____1174 = (

let uu____1182 = (FStar_List.hd st)
in (

let uu____1187 = (FStar_List.tl st)
in ((uu____1182), (uu____1187))))
in (match (uu____1174) with
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

let uu____1227 = (deps_of_our_file filename)
in (match (uu____1227) with
| (filenames, uu____1236) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let rec go : (Prims.int * Prims.int)  ->  Prims.string  ->  stack_t  ->  modul_t  ->  env_t  ->  m_timestamps  ->  Prims.unit = (fun line_col filename stack curmod env ts -> (

let uu____1287 = (shift_chunk ())
in (match (uu____1287) with
| Pop (msg) -> begin
((pop env msg);
(

let uu____1290 = (match (stack) with
| [] -> begin
((FStar_Util.print_error "too many pops");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd)::tl -> begin
((hd), (tl))
end)
in (match (uu____1290) with
| ((env, curmod), stack) -> begin
((match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(cleanup env)
end
| uu____1353 -> begin
()
end);
(go line_col filename stack curmod env ts);
)
end));
)
end
| Push (lax, l, c) -> begin
(

let uu____1357 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(

let uu____1380 = (update_deps filename curmod stack env ts)
in ((true), (uu____1380)))
end
| uu____1387 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____1357) with
| (restore_cmd_line_options, (stack, env, ts)) -> begin
(

let stack = (((env), (curmod)))::stack
in (

let env = (push env lax restore_cmd_line_options "#push")
in (go ((l), (c)) filename stack curmod env ts)))
end))
end
| Code (text, (ok, fail)) -> begin
(

let fail = (fun curmod env_mark -> ((report_fail ());
(FStar_Util.print1 "%s\n" fail);
(

let env = (reset_mark env_mark)
in (go line_col filename stack curmod env ts));
))
in (

let env_mark = (mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (Prims.fst line_col); FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)}
in (

let res = (check_frag env_mark curmod frag)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
(match ((n_errs = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print1 "\n%s\n" ok);
(

let env = (commit_mark env)
in (go line_col filename stack curmod env ts));
)
end
| uu____1459 -> begin
(fail curmod env_mark)
end)
end
| uu____1460 -> begin
(fail curmod env_mark)
end)))))
end)))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((

let uu____1472 = (

let uu____1473 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____1473))
in (match (uu____1472) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____1475 -> begin
()
end));
(

let uu____1476 = (deps_of_our_file filename)
in (match (uu____1476) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____1490 = (tc_deps None [] env filenames [])
in (match (uu____1490) with
| (stack, env, ts) -> begin
(

let uu____1505 = (match (maybe_intf) with
| Some (intf) -> begin
(

let frag = (

let uu____1518 = (FStar_Util.file_get_contents intf)
in {FStar_Parser_ParseIt.frag_text = uu____1518; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")})
in (

let uu____1519 = (check_frag env None frag)
in (match (uu____1519) with
| Some (curmod, env, n_errs) -> begin
((match ((n_errs <> (Prims.parse_int "0"))) with
| true -> begin
((

let uu____1549 = (FStar_Util.format1 "Found the interface %s but it has errors!" intf)
in (FStar_Util.print_warning uu____1549));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____1550 -> begin
()
end);
(FStar_Util.print_string "Reminder: fst+fsti in interactive mode is unsound.\n");
((curmod), (env));
)
end
| None -> begin
((

let uu____1562 = (FStar_Util.format1 "Found the interface %s but could not parse it first!" intf)
in (FStar_Util.print_warning uu____1562));
(FStar_All.exit (Prims.parse_int "1"));
)
end)))
end
| None -> begin
((None), (env))
end)
in (match (uu____1505) with
| (initial_mod, env) -> begin
(

let uu____1577 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____1577) with
| true -> begin
(

let uu____1578 = (

let uu____1579 = (FStar_Options.file_list ())
in (FStar_List.hd uu____1579))
in (FStar_SMTEncoding_Solver.with_hints_db uu____1578 (fun uu____1581 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack initial_mod env ts))))
end
| uu____1582 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename stack initial_mod env ts)
end))
end))
end)))
end));
))




