
open Prims
open FStar_Pervasives

let tc_one_file : Prims.string Prims.list  ->  FStar_Universal.uenv  ->  ((Prims.string FStar_Pervasives_Native.option * Prims.string) * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.string Prims.list) = (fun remaining uenv -> (

let uu____31 = uenv
in (match (uu____31) with
| (dsenv, env) -> begin
(

let uu____52 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____90 = (FStar_Universal.tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____90) with
| (uu____117, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.Some (intf)), (impl))), (dsenv1), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____142 = (FStar_Universal.tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____142) with
| (uu____169, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.None), (intf_or_impl))), (dsenv1), (env1), (remaining1))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____52) with
| ((intf, impl), dsenv1, env1, remaining1) -> begin
((((intf), (impl))), (((dsenv1), (env1))), (remaining1))
end))
end)))


let tc_prims : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____264 -> (

let uu____265 = (FStar_Universal.tc_prims ())
in (match (uu____265) with
| (uu____280, dsenv, env) -> begin
((dsenv), (env))
end)))


type env_t =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun env msg -> (

let res = (FStar_Universal.push_context env msg)
in ((FStar_Options.push ());
res;
)))


let pop : 'Auu____335 . ('Auu____335 * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((FStar_Universal.pop_context (FStar_Pervasives_Native.snd env) msg);
(FStar_Options.pop ());
))

type push_kind =
| SyntaxCheck
| LaxCheck
| FullCheck


let uu___is_SyntaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SyntaxCheck -> begin
true
end
| uu____357 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____362 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____367 -> begin
false
end))


let push_with_kind : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____388 kind restore_cmd_line_options1 msg -> (match (uu____388) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___213_403 = tcenv
in {FStar_TypeChecker_Env.solver = uu___213_403.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___213_403.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___213_403.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___213_403.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___213_403.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___213_403.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___213_403.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___213_403.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___213_403.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___213_403.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___213_403.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___213_403.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___213_403.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___213_403.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___213_403.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___213_403.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___213_403.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___213_403.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___213_403.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___213_403.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___213_403.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___213_403.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___213_403.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___213_403.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___213_403.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___213_403.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___213_403.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___213_403.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___213_403.FStar_TypeChecker_Env.identifier_info})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (Prims.op_Equality kind SyntaxCheck))
in (

let res = (push ((dsenv1), (tcenv1)) msg)
in ((match (restore_cmd_line_options1) with
| true -> begin
(

let uu____411 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____411 FStar_Pervasives.ignore))
end
| uu____412 -> begin
()
end);
res;
))))
end))


let cleanup : 'Auu____417 . ('Auu____417 * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____425 -> (match (uu____425) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____465 curmod frag -> (match (uu____465) with
| (dsenv, env) -> begin
(FStar_All.try_with (fun uu___215_514 -> (match (()) with
| () -> begin
(

let uu____529 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____529) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____569 = (

let uu____582 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____582)))
in FStar_Pervasives_Native.Some (uu____569))
end
| uu____601 -> begin
FStar_Pervasives_Native.None
end))
end)) (fun uu___214_629 -> (match (uu___214_629) with
| FStar_All.Failure (msg) when (

let uu____645 = (FStar_Options.trace_error ())
in (not (uu____645))) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____648 = (

let uu____655 = (

let uu____660 = (FStar_TypeChecker_Env.get_range env)
in ((msg1), (uu____660)))
in (uu____655)::[])
in (FStar_TypeChecker_Err.add_errors env uu____648));
(FStar_Util.print_error msg1);
FStar_Pervasives_Native.None;
))
end
| FStar_Errors.Error (msg, r) when (

let uu____684 = (FStar_Options.trace_error ())
in (not (uu____684))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____707 = (FStar_Options.trace_error ())
in (not (uu____707))) -> begin
((

let uu____709 = (

let uu____716 = (

let uu____721 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____721)))
in (uu____716)::[])
in (FStar_TypeChecker_Err.add_errors env uu____709));
FStar_Pervasives_Native.None;
)
end)))
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____757 = (FStar_List.partition (fun x -> (

let uu____770 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____771 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____770 uu____771)))) deps)
in (match (uu____757) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____798 = ((

let uu____801 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____801))) || (

let uu____803 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____803))))
in (match (uu____798) with
| true -> begin
(

let uu____804 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____804))
end
| uu____805 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____807 -> begin
((

let uu____811 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____811));
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
| uu____866 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____885 = (

let uu____886 = (FStar_Options.lax ())
in (match (uu____886) with
| true -> begin
LaxCheck
end
| uu____887 -> begin
FullCheck
end))
in (push_with_kind env uu____885 true "typecheck_modul"))
in (

let uu____888 = (tc_one_file remaining env1)
in (match (uu____888) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____939 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____952 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____952))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____939) with
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
| (uu____1056, uu____1057) -> begin
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
| uu____1149 -> begin
((false), (depnames1))
end)
end
| uu____1152 -> begin
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
| uu____1177 -> begin
((false), (depnames1))
end)
end
| uu____1180 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____1263)::ts3 -> begin
((pop env1 "");
(

let uu____1304 = (

let uu____1319 = (FStar_List.hd stack)
in (

let uu____1328 = (FStar_List.tl stack)
in ((uu____1319), (uu____1328))))
in (match (uu____1304) with
| ((env2, uu____1354), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____1418 = ts_elt
in (match (uu____1418) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1449 = (match_dep depnames intf impl)
in (match (uu____1449) with
| (b, depnames') -> begin
(

let uu____1468 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1468) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____1488 -> begin
(

let uu____1489 = (

let uu____1504 = (FStar_List.hd st)
in (

let uu____1513 = (FStar_List.tl st)
in ((uu____1504), (uu____1513))))
in (match (uu____1489) with
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

let uu____1590 = (deps_of_our_file filename)
in (match (uu____1590) with
| (filenames, uu____1606) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___203_1666 -> (match (uu___203_1666) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____1668 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____1670 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____1670))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____1672) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____1675) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1693) -> begin
true
end
| uu____1698 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1714) -> begin
uu____1714
end))


let js_fail : 'Auu____1725 . Prims.string  ->  FStar_Util.json  ->  'Auu____1725 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___204_1737 -> (match (uu___204_1737) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___205_1743 -> (match (uu___205_1743) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____1752 . (FStar_Util.json  ->  'Auu____1752)  ->  FStar_Util.json  ->  'Auu____1752 Prims.list = (fun k uu___206_1765 -> (match (uu___206_1765) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___207_1783 -> (match (uu___207_1783) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1808 = (js_str s)
in (match (uu____1808) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1809 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1814 = (js_str s)
in (match (uu____1814) with
| "beta" -> begin
FStar_TypeChecker_Normalize.Beta
end
| "delta" -> begin
FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant)
end
| "iota" -> begin
FStar_TypeChecker_Normalize.Iota
end
| "zeta" -> begin
FStar_TypeChecker_Normalize.Zeta
end
| "reify" -> begin
FStar_TypeChecker_Normalize.Reify
end
| "pure-subterms" -> begin
FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
end
| uu____1815 -> begin
(js_fail "reduction rule" s)
end)))

type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Pop
| Push of (push_kind * Prims.string * Prims.int * Prims.int * Prims.bool)
| AutoComplete of Prims.string
| Lookup of (Prims.string * (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option * Prims.string Prims.list)
| Compute of (Prims.string * FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option)
| Search of Prims.string
| MissingCurrentModule
| ProtocolViolation of Prims.string 
 and query =
{qq : query'; qid : Prims.string}


let uu___is_Exit : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1886 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1891 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1896 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1901 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1917 -> begin
false
end))


let __proj__Push__item___0 : query'  ->  (push_kind * Prims.string * Prims.int * Prims.int * Prims.bool) = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
_0
end))


let uu___is_AutoComplete : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AutoComplete (_0) -> begin
true
end
| uu____1961 -> begin
false
end))


let __proj__AutoComplete__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| AutoComplete (_0) -> begin
_0
end))


let uu___is_Lookup : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lookup (_0) -> begin
true
end
| uu____1991 -> begin
false
end))


let __proj__Lookup__item___0 : query'  ->  (Prims.string * (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option * Prims.string Prims.list) = (fun projectee -> (match (projectee) with
| Lookup (_0) -> begin
_0
end))


let uu___is_Compute : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Compute (_0) -> begin
true
end
| uu____2061 -> begin
false
end))


let __proj__Compute__item___0 : query'  ->  (Prims.string * FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Compute (_0) -> begin
_0
end))


let uu___is_Search : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Search (_0) -> begin
true
end
| uu____2099 -> begin
false
end))


let __proj__Search__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Search (_0) -> begin
_0
end))


let uu___is_MissingCurrentModule : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MissingCurrentModule -> begin
true
end
| uu____2112 -> begin
false
end))


let uu___is_ProtocolViolation : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
true
end
| uu____2118 -> begin
false
end))


let __proj__ProtocolViolation__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
_0
end))


let __proj__Mkquery__item__qq : query  ->  query' = (fun projectee -> (match (projectee) with
| {qq = __fname__qq; qid = __fname__qid} -> begin
__fname__qq
end))


let __proj__Mkquery__item__qid : query  ->  Prims.string = (fun projectee -> (match (projectee) with
| {qq = __fname__qq; qid = __fname__qid} -> begin
__fname__qid
end))


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___208_2142 -> (match (uu___208_2142) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Pop -> begin
false
end
| Push (uu____2143) -> begin
false
end
| MissingCurrentModule -> begin
false
end
| ProtocolViolation (uu____2154) -> begin
false
end
| AutoComplete (uu____2155) -> begin
true
end
| Lookup (uu____2156) -> begin
true
end
| Compute (uu____2173) -> begin
true
end
| Search (uu____2182) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2192) -> begin
true
end
| uu____2193 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2201) -> begin
uu____2201
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____2206 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____2211 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____2216 -> begin
false
end))


let try_assoc : 'Auu____2225 'Auu____2226 . 'Auu____2226  ->  ('Auu____2226 * 'Auu____2225) Prims.list  ->  'Auu____2225 FStar_Pervasives_Native.option = (fun key a -> (

let uu____2249 = (FStar_Util.try_find (fun uu____2263 -> (match (uu____2263) with
| (k, uu____2269) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____2249)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____2286 = (

let uu____2287 = (

let uu____2288 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____2288))
in ProtocolViolation (uu____2287))
in {qq = uu____2286; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____2315 = (try_assoc key a)
in (match (uu____2315) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2319 = (

let uu____2320 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____2320))
in (FStar_Exn.raise uu____2319))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____2335 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____2335 js_str))
in (FStar_All.try_with (fun uu___217_2342 -> (match (()) with
| () -> begin
(

let query = (

let uu____2344 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____2344 js_str))
in (

let args = (

let uu____2352 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____2352 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____2369 = (try_assoc k args)
in (match (uu____2369) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____2377 = (match (query) with
| "exit" -> begin
Exit
end
| "pop" -> begin
Pop
end
| "describe-protocol" -> begin
DescribeProtocol
end
| "describe-repl" -> begin
DescribeRepl
end
| "peek" -> begin
(

let uu____2378 = (

let uu____2389 = (

let uu____2390 = (arg "kind")
in (FStar_All.pipe_right uu____2390 js_pushkind))
in (

let uu____2391 = (

let uu____2392 = (arg "code")
in (FStar_All.pipe_right uu____2392 js_str))
in (

let uu____2393 = (

let uu____2394 = (arg "line")
in (FStar_All.pipe_right uu____2394 js_int))
in (

let uu____2395 = (

let uu____2396 = (arg "column")
in (FStar_All.pipe_right uu____2396 js_int))
in ((uu____2389), (uu____2391), (uu____2393), (uu____2395), ((Prims.op_Equality query "peek")))))))
in Push (uu____2378))
end
| "push" -> begin
(

let uu____2397 = (

let uu____2408 = (

let uu____2409 = (arg "kind")
in (FStar_All.pipe_right uu____2409 js_pushkind))
in (

let uu____2410 = (

let uu____2411 = (arg "code")
in (FStar_All.pipe_right uu____2411 js_str))
in (

let uu____2412 = (

let uu____2413 = (arg "line")
in (FStar_All.pipe_right uu____2413 js_int))
in (

let uu____2414 = (

let uu____2415 = (arg "column")
in (FStar_All.pipe_right uu____2415 js_int))
in ((uu____2408), (uu____2410), (uu____2412), (uu____2414), ((Prims.op_Equality query "peek")))))))
in Push (uu____2397))
end
| "autocomplete" -> begin
(

let uu____2416 = (

let uu____2417 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____2417 js_str))
in AutoComplete (uu____2416))
end
| "lookup" -> begin
(

let uu____2418 = (

let uu____2435 = (

let uu____2436 = (arg "symbol")
in (FStar_All.pipe_right uu____2436 js_str))
in (

let uu____2437 = (

let uu____2446 = (

let uu____2455 = (try_arg "location")
in (FStar_All.pipe_right uu____2455 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____2446 (FStar_Util.map_option (fun loc -> (

let uu____2513 = (

let uu____2514 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____2514 js_str))
in (

let uu____2515 = (

let uu____2516 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____2516 js_int))
in (

let uu____2517 = (

let uu____2518 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____2518 js_int))
in ((uu____2513), (uu____2515), (uu____2517)))))))))
in (

let uu____2519 = (

let uu____2522 = (arg "requested-info")
in (FStar_All.pipe_right uu____2522 (js_list js_str)))
in ((uu____2435), (uu____2437), (uu____2519)))))
in Lookup (uu____2418))
end
| "compute" -> begin
(

let uu____2535 = (

let uu____2544 = (

let uu____2545 = (arg "term")
in (FStar_All.pipe_right uu____2545 js_str))
in (

let uu____2546 = (

let uu____2551 = (try_arg "rules")
in (FStar_All.pipe_right uu____2551 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____2544), (uu____2546))))
in Compute (uu____2535))
end
| "search" -> begin
(

let uu____2566 = (

let uu____2567 = (arg "terms")
in (FStar_All.pipe_right uu____2567 js_str))
in Search (uu____2566))
end
| uu____2568 -> begin
(

let uu____2569 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____2569))
end)
in {qq = uu____2377; qid = qid})))))
end)) (fun uu___216_2572 -> (match (uu___216_2572) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (FStar_All.try_with (fun uu___219_2582 -> (match (()) with
| () -> begin
(

let uu____2583 = (FStar_Util.read_line stream)
in (match (uu____2583) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____2587 = (FStar_Util.json_of_string line)
in (match (uu____2587) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(unpack_interactive_query request)
end))
end))
end)) (fun uu___218_2593 -> (match (uu___218_2593) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let rec json_of_fstar_option : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___209_2600 -> (match (uu___209_2600) with
| FStar_Options.Bool (b) -> begin
FStar_Util.JsonBool (b)
end
| FStar_Options.String (s) -> begin
FStar_Util.JsonStr (s)
end
| FStar_Options.Path (s) -> begin
FStar_Util.JsonStr (s)
end
| FStar_Options.Int (n1) -> begin
FStar_Util.JsonInt (n1)
end
| FStar_Options.List (vs) -> begin
(

let uu____2608 = (FStar_List.map json_of_fstar_option vs)
in FStar_Util.JsonList (uu____2608))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let json_of_opt : 'Auu____2617 . ('Auu____2617  ->  FStar_Util.json)  ->  'Auu____2617 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____2635 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____2635)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____2642 = (

let uu____2645 = (

let uu____2646 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____2646))
in (

let uu____2647 = (

let uu____2650 = (

let uu____2651 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____2651))
in (uu____2650)::[])
in (uu____2645)::uu____2647))
in FStar_Util.JsonList (uu____2642)))


let json_of_range_fields : Prims.string  ->  FStar_Range.pos  ->  FStar_Range.pos  ->  FStar_Util.json = (fun file b e -> (

let uu____2664 = (

let uu____2671 = (

let uu____2678 = (

let uu____2683 = (json_of_pos b)
in (("beg"), (uu____2683)))
in (

let uu____2684 = (

let uu____2691 = (

let uu____2696 = (json_of_pos e)
in (("end"), (uu____2696)))
in (uu____2691)::[])
in (uu____2678)::uu____2684))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____2671)
in FStar_Util.JsonAssoc (uu____2664)))


let json_of_use_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2717 = (FStar_Range.file_of_use_range r)
in (

let uu____2718 = (FStar_Range.start_of_use_range r)
in (

let uu____2719 = (FStar_Range.end_of_use_range r)
in (json_of_range_fields uu____2717 uu____2718 uu____2719)))))


let json_of_def_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2724 = (FStar_Range.file_of_range r)
in (

let uu____2725 = (FStar_Range.start_of_range r)
in (

let uu____2726 = (FStar_Range.end_of_range r)
in (json_of_range_fields uu____2724 uu____2725 uu____2726)))))


let json_of_issue_level : FStar_Errors.issue_level  ->  FStar_Util.json = (fun i -> FStar_Util.JsonStr ((match (i) with
| FStar_Errors.ENotImplemented -> begin
"not-implemented"
end
| FStar_Errors.EInfo -> begin
"info"
end
| FStar_Errors.EWarning -> begin
"warning"
end
| FStar_Errors.EError -> begin
"error"
end)))


let json_of_issue : FStar_Errors.issue  ->  FStar_Util.json = (fun issue -> (

let uu____2735 = (

let uu____2742 = (

let uu____2749 = (

let uu____2756 = (

let uu____2761 = (

let uu____2762 = (

let uu____2765 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____2771 = (json_of_use_range r)
in (uu____2771)::[])
end)
in (

let uu____2772 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (Prims.op_disEquality r.FStar_Range.def_range r.FStar_Range.use_range) -> begin
(

let uu____2778 = (json_of_def_range r)
in (uu____2778)::[])
end
| uu____2779 -> begin
[]
end)
in (FStar_List.append uu____2765 uu____2772)))
in FStar_Util.JsonList (uu____2762))
in (("ranges"), (uu____2761)))
in (uu____2756)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____2749)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____2742)
in FStar_Util.JsonAssoc (uu____2735)))

type lookup_result =
{lr_name : Prims.string; lr_def_range : FStar_Range.range FStar_Pervasives_Native.option; lr_typ : Prims.string FStar_Pervasives_Native.option; lr_doc : Prims.string FStar_Pervasives_Native.option; lr_def : Prims.string FStar_Pervasives_Native.option}


let __proj__Mklookup_result__item__lr_name : lookup_result  ->  Prims.string = (fun projectee -> (match (projectee) with
| {lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range; lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc; lr_def = __fname__lr_def} -> begin
__fname__lr_name
end))


let __proj__Mklookup_result__item__lr_def_range : lookup_result  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range; lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc; lr_def = __fname__lr_def} -> begin
__fname__lr_def_range
end))


let __proj__Mklookup_result__item__lr_typ : lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range; lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc; lr_def = __fname__lr_def} -> begin
__fname__lr_typ
end))


let __proj__Mklookup_result__item__lr_doc : lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range; lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc; lr_def = __fname__lr_def} -> begin
__fname__lr_doc
end))


let __proj__Mklookup_result__item__lr_def : lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {lr_name = __fname__lr_name; lr_def_range = __fname__lr_def_range; lr_typ = __fname__lr_typ; lr_doc = __fname__lr_doc; lr_def = __fname__lr_def} -> begin
__fname__lr_def
end))


let json_of_lookup_result : lookup_result  ->  FStar_Util.json = (fun lr -> (

let uu____2931 = (

let uu____2938 = (

let uu____2945 = (

let uu____2950 = (json_of_opt json_of_def_range lr.lr_def_range)
in (("defined-at"), (uu____2950)))
in (

let uu____2951 = (

let uu____2958 = (

let uu____2963 = (json_of_opt (fun _0_42 -> FStar_Util.JsonStr (_0_42)) lr.lr_typ)
in (("type"), (uu____2963)))
in (

let uu____2964 = (

let uu____2971 = (

let uu____2976 = (json_of_opt (fun _0_43 -> FStar_Util.JsonStr (_0_43)) lr.lr_doc)
in (("documentation"), (uu____2976)))
in (

let uu____2977 = (

let uu____2984 = (

let uu____2989 = (json_of_opt (fun _0_44 -> FStar_Util.JsonStr (_0_44)) lr.lr_def)
in (("definition"), (uu____2989)))
in (uu____2984)::[])
in (uu____2971)::uu____2977))
in (uu____2958)::uu____2964))
in (uu____2945)::uu____2951))
in ((("name"), (FStar_Util.JsonStr (lr.lr_name))))::uu____2938)
in FStar_Util.JsonAssoc (uu____2931)))


let json_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3022 = (FStar_List.map (fun _0_45 -> FStar_Util.JsonStr (_0_45)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_46 -> FStar_Util.JsonList (_0_46)) uu____3022))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____3044 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____3044));
(FStar_Util.print_raw "\n");
))


let write_response : Prims.string  ->  query_status  ->  FStar_Util.json  ->  Prims.unit = (fun qid status response -> (

let qid1 = FStar_Util.JsonStr (qid)
in (

let status1 = (match (status) with
| QueryOK -> begin
FStar_Util.JsonStr ("success")
end
| QueryNOK -> begin
FStar_Util.JsonStr ("failure")
end
| QueryViolatesProtocol -> begin
FStar_Util.JsonStr ("protocol-violation")
end)
in (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("response"))))::((("query-id"), (qid1)))::((("status"), (status1)))::((("response"), (response)))::[]))))))


let write_message : Prims.string  ->  FStar_Util.json  ->  Prims.unit = (fun level contents -> (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("message"))))::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (contents)))::[]))))


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____3106 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3109 = (FStar_List.map (fun _0_47 -> FStar_Util.JsonStr (_0_47)) interactive_protocol_features)
in FStar_Util.JsonList (uu____3109))
in (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::json_of_protocol_info))))))

type repl_state =
{repl_line : Prims.int; repl_column : Prims.int; repl_fname : Prims.string; repl_stack : stack_t; repl_curmod : modul_t; repl_env : env_t; repl_ts : m_timestamps; repl_stdin : FStar_Util.stream_reader}


let __proj__Mkrepl_state__item__repl_line : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_line
end))


let __proj__Mkrepl_state__item__repl_column : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_column
end))


let __proj__Mkrepl_state__item__repl_fname : repl_state  ->  Prims.string = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_fname
end))


let __proj__Mkrepl_state__item__repl_stack : repl_state  ->  stack_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_stack
end))


let __proj__Mkrepl_state__item__repl_curmod : repl_state  ->  modul_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_curmod
end))


let __proj__Mkrepl_state__item__repl_env : repl_state  ->  env_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_env
end))


let __proj__Mkrepl_state__item__repl_ts : repl_state  ->  m_timestamps = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_ts
end))


let __proj__Mkrepl_state__item__repl_stdin : repl_state  ->  FStar_Util.stream_reader = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_stack = __fname__repl_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_ts = __fname__repl_ts; repl_stdin = __fname__repl_stdin} -> begin
__fname__repl_stdin
end))


let json_of_repl_state : repl_state  ->  (Prims.string * FStar_Util.json) Prims.list = (fun st -> (

let opts_and_defaults = (

let opt_docs = (

let uu____3270 = (FStar_Options.docs ())
in (FStar_Util.smap_of_list uu____3270))
in (

let get_doc = (fun k -> (FStar_Util.smap_try_find opt_docs k))
in (FStar_List.map (fun uu____3302 -> (match (uu____3302) with
| (k, v1) -> begin
(

let uu____3319 = (FStar_Options.get_option k)
in (

let uu____3320 = (get_doc k)
in ((k), (uu____3319), (uu____3320), (v1))))
end)) FStar_Options.defaults)))
in (

let uu____3325 = (

let uu____3330 = (

let uu____3331 = (FStar_List.map (fun uu____3351 -> (match (uu____3351) with
| (uu____3364, fstname, uu____3366, uu____3367) -> begin
FStar_Util.JsonStr (fstname)
end)) st.repl_ts)
in FStar_Util.JsonList (uu____3331))
in (("loaded-dependencies"), (uu____3330)))
in (

let uu____3376 = (

let uu____3383 = (

let uu____3388 = (

let uu____3389 = (FStar_List.map (fun uu____3408 -> (match (uu____3408) with
| (name, value, doc1, dflt1) -> begin
(

let uu____3427 = (

let uu____3434 = (

let uu____3441 = (

let uu____3446 = (json_of_fstar_option value)
in (("value"), (uu____3446)))
in (

let uu____3447 = (

let uu____3454 = (

let uu____3459 = (json_of_fstar_option dflt1)
in (("default"), (uu____3459)))
in (

let uu____3460 = (

let uu____3467 = (

let uu____3472 = (json_of_opt (fun _0_48 -> FStar_Util.JsonStr (_0_48)) doc1)
in (("documentation"), (uu____3472)))
in (uu____3467)::[])
in (uu____3454)::uu____3460))
in (uu____3441)::uu____3447))
in ((("name"), (FStar_Util.JsonStr (name))))::uu____3434)
in FStar_Util.JsonAssoc (uu____3427))
end)) opts_and_defaults)
in FStar_Util.JsonList (uu____3389))
in (("options"), (uu____3388)))
in (uu____3383)::[])
in (uu____3325)::uu____3376))))


let with_printed_effect_args : 'Auu____3509 . (Prims.unit  ->  'Auu____3509)  ->  'Auu____3509 = (fun k -> (FStar_Options.with_saved_options (fun uu____3521 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____3532 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____3538 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____3545 'Auu____3546 . 'Auu____3546  ->  ((query_status * FStar_Util.json) * ('Auu____3545, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____3577 'Auu____3578 . 'Auu____3578  ->  ((query_status * FStar_Util.json) * ('Auu____3578, 'Auu____3577) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (json_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____3607 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3607) FStar_Util.either) = (fun st -> (

let uu____3624 = (

let uu____3629 = (

let uu____3630 = (json_of_repl_state st)
in FStar_Util.JsonAssoc (uu____3630))
in ((QueryOK), (uu____3629)))
in ((uu____3624), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____3653 'Auu____3654 . 'Auu____3654  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____3654, 'Auu____3653) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_missing_current_module : 'Auu____3693 'Auu____3694 'Auu____3695 . 'Auu____3695  ->  'Auu____3694  ->  ((query_status * FStar_Util.json) * ('Auu____3695, 'Auu____3693) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))), (FStar_Util.Inl (st))))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> ((FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)))


let run_pop : 'Auu____3748 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3748) FStar_Util.either) = (fun st -> (match ((nothing_left_to_pop st)) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____3773 -> begin
(match (st.repl_stack) with
| [] -> begin
(failwith "impossible")
end
| ((env, curmod))::stack -> begin
((pop st.repl_env "#pop");
(

let st' = (

let uu___220_3817 = st
in {repl_line = uu___220_3817.repl_line; repl_column = uu___220_3817.repl_column; repl_fname = uu___220_3817.repl_fname; repl_stack = stack; repl_curmod = curmod; repl_env = env; repl_ts = uu___220_3817.repl_ts; repl_stdin = uu___220_3817.repl_stdin})
in ((match ((nothing_left_to_pop st')) with
| true -> begin
(cleanup env)
end
| uu____3819 -> begin
()
end);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st')));
));
)
end)
end))


let run_push : 'Auu____3842 . repl_state  ->  push_kind  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3842) FStar_Util.either) = (fun st kind text1 line column peek_only -> (

let uu____3879 = ((st.repl_stack), (st.repl_env), (st.repl_ts))
in (match (uu____3879) with
| (stack, env, ts) -> begin
(

let uu____3901 = (match ((nothing_left_to_pop st)) with
| true -> begin
(

let uu____3922 = (update_deps st.repl_fname st.repl_curmod stack env ts)
in ((true), (uu____3922)))
end
| uu____3935 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____3901) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (st.repl_curmod)))::stack1
in (

let env2 = (push_with_kind env1 kind restore_cmd_line_options1 "#push")
in (

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in (

let res = (check_frag env2 st.repl_curmod ((frag), (false)))
in (

let errors = (

let uu____3999 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____3999 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___221_4008 = st
in {repl_line = line; repl_column = column; repl_fname = uu___221_4008.repl_fname; repl_stack = stack2; repl_curmod = uu___221_4008.repl_curmod; repl_env = uu___221_4008.repl_env; repl_ts = ts1; repl_stdin = uu___221_4008.repl_stdin})
in (match (res) with
| FStar_Pervasives_Native.Some (curmod, env3, nerrs) when ((Prims.op_Equality nerrs (Prims.parse_int "0")) && (Prims.op_Equality peek_only false)) -> begin
((((QueryOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl ((

let uu___222_4057 = st'
in {repl_line = uu___222_4057.repl_line; repl_column = uu___222_4057.repl_column; repl_fname = uu___222_4057.repl_fname; repl_stack = uu___222_4057.repl_stack; repl_curmod = curmod; repl_env = env3; repl_ts = uu___222_4057.repl_ts; repl_stdin = uu___222_4057.repl_stdin}))))
end
| uu____4058 -> begin
(

let uu____4073 = (run_pop (

let uu___223_4087 = st'
in {repl_line = uu___223_4087.repl_line; repl_column = uu___223_4087.repl_column; repl_fname = uu___223_4087.repl_fname; repl_stack = uu___223_4087.repl_stack; repl_curmod = uu___223_4087.repl_curmod; repl_env = env2; repl_ts = uu___223_4087.repl_ts; repl_stdin = uu___223_4087.repl_stdin}))
in (match (uu____4073) with
| (uu____4100, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____4119 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end))
end));
))))))
end))
end)))


let run_lookup : 'Auu____4138 . repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4138) FStar_Util.either) = (fun st symbol pos_opt requested_info -> (

let uu____4187 = st.repl_env
in (match (uu____4187) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____4219 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____4219))
in (

let lid1 = (

let uu____4223 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____4223))
in (

let uu____4228 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____4228 (FStar_Util.map_option (fun uu____4283 -> (match (uu____4283) with
| ((uu____4302, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____4319 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____4319 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____4348 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____4348 (fun uu___210_4392 -> (match (uu___210_4392) with
| (FStar_Util.Inr (se, uu____4414), uu____4415) -> begin
(

let uu____4444 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____4444))
end
| uu____4445 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____4497 -> (match (uu____4497) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____4544) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4597 -> begin
(info_of_lid_str symbol)
end)
end)
in (

let response = (match (info_opt) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonNull))
end
| FStar_Pervasives_Native.Some (name_or_lid, typ, rng) -> begin
(

let name = (match (name_or_lid) with
| FStar_Util.Inl (name) -> begin
name
end
| FStar_Util.Inr (lid) -> begin
(FStar_Ident.string_of_lid lid)
end)
in (

let typ_str = (match ((FStar_List.mem "type" requested_info)) with
| true -> begin
(

let uu____4646 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____4646))
end
| uu____4647 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____4654 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____4665 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____4675 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {lr_name = name; lr_def_range = def_range; lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str}
in (

let uu____4677 = (json_of_lookup_result result)
in ((QueryOK), (uu____4677)))))))))
end)
in ((response), (FStar_Util.Inl (st)))))))))
end)))


let run_completions : 'Auu____4692 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4692) FStar_Util.either) = (fun st search_term -> (

let uu____4713 = st.repl_env
in (match (uu____4713) with
| (dsenv, tcenv) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____4763) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____4778, []) -> begin
FStar_Pervasives_Native.None
end
| ((hs)::ts, (hc)::tc) -> begin
(

let hc_text = (FStar_Ident.text_of_id hc)
in (match ((FStar_Util.starts_with hc_text hs)) with
| true -> begin
(match (ts) with
| [] -> begin
FStar_Pervasives_Native.Some (((candidate), ((FStar_String.length hs))))
end
| uu____4828 -> begin
(

let uu____4831 = (measure_anchored_match ts tc)
in (FStar_All.pipe_right uu____4831 (FStar_Util.map_option (fun uu____4871 -> (match (uu____4871) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____4892 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____4926 = (measure_anchored_match needle candidate)
in (match (uu____4926) with
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

let uu____5005 = (locate_match needle tc)
in (FStar_All.pipe_right uu____5005 (FStar_Util.map_option (fun uu____5066 -> (match (uu____5066) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____5110 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____5110)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____5157 -> (match (uu____5157) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____5188)::[] -> begin
true
end
| uu____5189 -> begin
false
end)
in (

let uu____5192 = (FStar_ToSyntax_Env.shorten_module_path dsenv prefix1 naked_match)
in (match (uu____5192) with
| (stripped_ns, shortened) -> begin
(

let uu____5219 = (str_of_ids shortened)
in (

let uu____5220 = (str_of_ids matched)
in (

let uu____5221 = (str_of_ids stripped_ns)
in ((uu____5219), (uu____5220), (uu____5221), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____5239 -> (match (uu____5239) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((Prims.op_Equality prefix1 "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____5264 -> begin
(((Prims.strcat prefix1 (Prims.strcat "." matched))), (stripped_ns), ((((FStar_String.length prefix1) + match_len) + (Prims.parse_int "1"))))
end)
end))
in (

let needle = (FStar_Util.split search_term ".")
in (

let all_lidents_in_env = (FStar_TypeChecker_Env.lidents tcenv)
in (

let matches = (

let case_a_find_transitive_includes = (fun orig_ns m id -> (

let exported_names = (FStar_ToSyntax_Env.transitive_exported_ids dsenv m)
in (

let matched_length = (FStar_List.fold_left (fun out s -> (((FStar_String.length s) + out) + (Prims.parse_int "1"))) (FStar_String.length id) orig_ns)
in (FStar_All.pipe_right exported_names (FStar_List.filter_map (fun n1 -> (match ((FStar_Util.starts_with n1 id)) with
| true -> begin
(

let lid = (FStar_Ident.lid_of_ns_and_id (FStar_Ident.ids_of_lid m) (FStar_Ident.id_of_text n1))
in (

let uu____5367 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____5383 = (

let uu____5386 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____5386 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____5383), (matched_length)))) uu____5367)))
end
| uu____5393 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____5419 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____5494 -> (match (uu____5494) with
| (ns, id, uu____5507) -> begin
(

let uu____5516 = (

let uu____5519 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____5519))
in (match (uu____5516) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____5521 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____5521))
end))
end))))))
in (

let uu____5522 = (FStar_Util.prefix needle)
in (match (uu____5522) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____5568 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____5572 = (FStar_ToSyntax_Env.resolve_module_name dsenv l true)
in (match (uu____5572) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____5637 = (shorten_namespace x)
in (prepare_candidate uu____5637))))))
end))))
in (

let json_candidates = (

let uu____5649 = (FStar_Util.sort_with (fun uu____5672 uu____5673 -> (match (((uu____5672), (uu____5673))) with
| ((cd1, ns1, uu____5700), (cd2, ns2, uu____5703)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_49 when (_0_49 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.map (fun uu____5727 -> (match (uu____5727) with
| (candidate, ns, match_len) -> begin
FStar_Util.JsonList ((FStar_Util.JsonInt (match_len))::(FStar_Util.JsonStr (ns))::(FStar_Util.JsonStr (candidate))::[])
end)) uu____5649))
in ((((QueryOK), (FStar_Util.JsonList (json_candidates)))), (FStar_Util.Inl (st)))))))))))))
end)))


let run_compute : 'Auu____5753 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5753) FStar_Util.either) = (fun st term rules -> (

let run_and_rewind = (fun st1 task -> (

let env' = (push st1.repl_env "#compute")
in (

let results = (task st1)
in ((pop env' "#compute");
((results), (FStar_Util.Inl (st1)));
))))
in (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let normalize_term1 = (fun tcenv rules1 t -> (FStar_TypeChecker_Normalize.normalize rules1 tcenv t))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5880, ({FStar_Syntax_Syntax.lbname = uu____5881; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____5883; FStar_Syntax_Syntax.lbeff = uu____5884; FStar_Syntax_Syntax.lbdef = def})::[]), uu____5886); FStar_Syntax_Syntax.sigrng = uu____5887; FStar_Syntax_Syntax.sigquals = uu____5888; FStar_Syntax_Syntax.sigmeta = uu____5889; FStar_Syntax_Syntax.sigattrs = uu____5890})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____5929 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____5948 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____5948) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____5972) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____6017 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____6049 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (FStar_Pervasives_Native.snd uu____6049)))
in (

let typecheck = (fun tcenv decls -> (

let uu____6067 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____6067) with
| (ses, uu____6081, uu____6082) -> begin
ses
end)))
in (

let rules1 = (FStar_List.append (match (rules) with
| FStar_Pervasives_Native.Some (rules1) -> begin
rules1
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end) ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Primops)::[]))
in (run_and_rewind st (fun st1 -> (

let uu____6110 = st1.repl_env
in (match (uu____6110) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____6122 -> begin
(

let uu____6123 = (parse1 frag)
in (match (uu____6123) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____6146 -> (

let decls1 = (desugar dsenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____6181 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____6181) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (

let normalized = (normalize_term1 tcenv1 rules1 def1)
in (

let uu____6194 = (

let uu____6195 = (term_to_string tcenv1 normalized)
in FStar_Util.JsonStr (uu____6195))
in ((QueryOK), (uu____6194)))))
end))
end))))
in (

let uu____6196 = (FStar_Options.trace_error ())
in (match (uu____6196) with
| true -> begin
(aux ())
end
| uu____6201 -> begin
(FStar_All.try_with (fun uu___225_6207 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___224_6215 -> (match (uu___224_6215) with
| e -> begin
(

let uu____6221 = (

let uu____6222 = (FStar_Errors.issue_of_exn e)
in (match (uu____6222) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____6226 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____6226))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise e)
end))
in ((QueryNOK), (uu____6221)))
end)))
end)))
end))
end))
end)))))))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____6248 -> begin
false
end))


let __proj__NameContainsStr__item___0 : search_term'  ->  Prims.string = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
_0
end))


let uu___is_TypeContainsLid : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TypeContainsLid (_0) -> begin
true
end
| uu____6262 -> begin
false
end))


let __proj__TypeContainsLid__item___0 : search_term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| TypeContainsLid (_0) -> begin
_0
end))


let __proj__Mksearch_term__item__st_negate : search_term  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {st_negate = __fname__st_negate; st_term = __fname__st_term} -> begin
__fname__st_negate
end))


let __proj__Mksearch_term__item__st_term : search_term  ->  search_term' = (fun projectee -> (match (projectee) with
| {st_negate = __fname__st_negate; st_term = __fname__st_term} -> begin
__fname__st_term
end))


let st_cost : search_term'  ->  Prims.int = (fun uu___211_6286 -> (match (uu___211_6286) with
| NameContainsStr (str) -> begin
(~- ((FStar_String.length str)))
end
| TypeContainsLid (lid) -> begin
(Prims.parse_int "1")
end))

type search_candidate =
{sc_lid : FStar_Ident.lid; sc_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref; sc_fvars : FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option FStar_ST.ref}


let __proj__Mksearch_candidate__item__sc_lid : search_candidate  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ; sc_fvars = __fname__sc_fvars} -> begin
__fname__sc_lid
end))


let __proj__Mksearch_candidate__item__sc_typ : search_candidate  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ; sc_fvars = __fname__sc_fvars} -> begin
__fname__sc_typ
end))


let __proj__Mksearch_candidate__item__sc_fvars : search_candidate  ->  FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ; sc_fvars = __fname__sc_fvars} -> begin
__fname__sc_fvars
end))


let sc_of_lid : FStar_Ident.lid  ->  search_candidate = (fun lid -> (

let uu____6454 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____6461 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____6454; sc_fvars = uu____6461})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____6510 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____6510) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____6535 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____6535) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____6556, typ), uu____6558) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____6602 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____6602) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____6645 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____6645))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____6688 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____6688))
in (

let uu____6689 = (

let uu____6696 = (

let uu____6701 = (

let uu____6702 = (

let uu____6703 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____6703.FStar_Ident.str)
in FStar_Util.JsonStr (uu____6702))
in (("lid"), (uu____6701)))
in (uu____6696)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____6689))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____6723) -> begin
true
end
| uu____6724 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____6732) -> begin
uu____6732
end))


let run_search : 'Auu____6739 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6739) FStar_Util.either) = (fun st search_str -> (

let uu____6760 = st.repl_env
in (match (uu____6760) with
| (dsenv, tcenv) -> begin
(

let empty_fv_set = (FStar_Syntax_Syntax.new_fv_set ())
in (

let st_matches = (fun candidate term -> (

let found = (match (term.st_term) with
| NameContainsStr (str) -> begin
(FStar_Util.contains candidate.sc_lid.FStar_Ident.str str)
end
| TypeContainsLid (lid) -> begin
(

let uu____6788 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____6788))
end)
in (Prims.op_disEquality found term.st_negate)))
in (

let parse1 = (fun search_str1 -> (

let parse_one = (fun term -> (

let negate = (FStar_Util.starts_with term "-")
in (

let term1 = (match (negate) with
| true -> begin
(FStar_Util.substring_from term (Prims.parse_int "1"))
end
| uu____6803 -> begin
term
end)
in (

let beg_quote = (FStar_Util.starts_with term1 "\"")
in (

let end_quote = (FStar_Util.ends_with term1 "\"")
in (

let strip_quotes = (fun str -> (match (((FStar_String.length str) < (Prims.parse_int "2"))) with
| true -> begin
(FStar_Exn.raise (InvalidSearch ("Empty search term")))
end
| uu____6810 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____6812 = (

let uu____6813 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____6813))
in (FStar_Exn.raise uu____6812))
end
| uu____6814 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____6815 = (strip_quotes term1)
in NameContainsStr (uu____6815))
end
| uu____6816 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____6818 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____6818) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6821 = (

let uu____6822 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____6822))
in (FStar_Exn.raise uu____6821))
end
| FStar_Pervasives_Native.Some (lid1) -> begin
TypeContainsLid (lid1)
end)))
end)
end)
in {st_negate = negate; st_term = parsed})))))))
in (

let terms = (FStar_List.map parse_one (FStar_Util.split search_str1 " "))
in (

let cmp = (fun x y -> ((st_cost x.st_term) - (st_cost y.st_term)))
in (FStar_Util.sort_with cmp terms)))))
in (

let pprint_one = (fun term -> (

let uu____6838 = (match (term.st_term) with
| NameContainsStr (s) -> begin
(FStar_Util.format1 "\"%s\"" s)
end
| TypeContainsLid (l) -> begin
(FStar_Util.format1 "%s" l.FStar_Ident.str)
end)
in (Prims.strcat (match (term.st_negate) with
| true -> begin
"-"
end
| uu____6841 -> begin
""
end) uu____6838)))
in (

let results = (FStar_All.try_with (fun uu___227_6862 -> (match (()) with
| () -> begin
(

let terms = (parse1 search_str)
in (

let all_lidents = (FStar_TypeChecker_Env.lidents tcenv)
in (

let all_candidates = (FStar_List.map sc_of_lid all_lidents)
in (

let matches_all = (fun candidate -> (FStar_List.for_all (st_matches candidate) terms))
in (

let cmp = (fun r1 r2 -> (FStar_Util.compare r1.sc_lid.FStar_Ident.str r2.sc_lid.FStar_Ident.str))
in (

let results = (FStar_List.filter matches_all all_candidates)
in (

let sorted1 = (FStar_Util.sort_with cmp results)
in (

let js = (FStar_List.map (json_of_search_result dsenv tcenv) sorted1)
in (match (results) with
| [] -> begin
(

let kwds = (

let uu____6901 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____6901))
in (

let uu____6904 = (

let uu____6905 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____6905))
in (FStar_Exn.raise uu____6904)))
end
| uu____6910 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___226_6915 -> (match (uu___226_6915) with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end)))
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___212_6961 -> (match (uu___212_6961) with
| Exit -> begin
(run_exit st)
end
| DescribeProtocol -> begin
(run_describe_protocol st)
end
| DescribeRepl -> begin
(run_describe_repl st)
end
| Pop -> begin
(run_pop st)
end
| Push (kind, text1, l, c, peek1) -> begin
(run_push st kind text1 l c peek1)
end
| AutoComplete (search_term) -> begin
(run_completions st search_term)
end
| Lookup (symbol, pos_opt, rqi) -> begin
(run_lookup st symbol pos_opt rqi)
end
| Compute (term, rules) -> begin
(run_compute st term rules)
end
| Search (term) -> begin
(run_search st term)
end
| MissingCurrentModule -> begin
(run_missing_current_module st (Obj.magic (())))
end
| ProtocolViolation (query) -> begin
(run_protocol_violation st query)
end))


let validate_query : repl_state  ->  query  ->  query = (fun st q -> (match (q.qq) with
| Push (SyntaxCheck, uu____7023, uu____7024, uu____7025, false) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____7026 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = MissingCurrentModule; qid = q.qid}
end
| uu____7027 -> begin
q
end)
end))


let rec go : repl_state  ->  Prims.unit = (fun st -> (

let query = (

let uu____7033 = (read_interactive_query st.repl_stdin)
in (validate_query st uu____7033))
in (

let uu____7034 = (

let uu____7047 = (run_query st)
in (uu____7047 query.qq))
in (match (uu____7034) with
| ((status, response), state_opt) -> begin
((write_response query.qid status response);
(match (state_opt) with
| FStar_Util.Inl (st') -> begin
(go st')
end
| FStar_Util.Inr (exitcode) -> begin
(FStar_All.exit exitcode)
end);
)
end))))


let interactive_error_handler : FStar_Errors.error_handler = (

let issues = (FStar_Util.mk_ref [])
in (

let add_one1 = (fun e -> (

let uu____7091 = (

let uu____7094 = (FStar_ST.op_Bang issues)
in (e)::uu____7094)
in (FStar_ST.op_Colon_Equals issues uu____7091)))
in (

let count_errors = (fun uu____7164 -> (

let uu____7165 = (

let uu____7168 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____7168))
in (FStar_List.length uu____7165)))
in (

let report1 = (fun uu____7210 -> (

let uu____7211 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____7211)))
in (

let clear1 = (fun uu____7249 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (fun s -> (write_message "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (write_message "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (write_message "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label1 get_string get_json -> (

let uu____7304 = (get_json ())
in (write_message label1 uu____7304)))}


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let uu____7310 = (deps_of_our_file filename)
in (match (uu____7310) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____7334 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____7334) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____7361 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____7362 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____7361 uu____7362)))
in (

let env2 = (

let uu____7368 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env1) initial_range)
in (((FStar_Pervasives_Native.fst env1)), (uu____7368)))
in (

let env3 = (match (maybe_intf) with
| FStar_Pervasives_Native.Some (intf) -> begin
(FStar_Universal.load_interface_decls env2 intf)
end
| FStar_Pervasives_Native.None -> begin
env2
end)
in ((FStar_TypeChecker_Env.toggle_id_info (FStar_Pervasives_Native.snd env3) true);
(

let init_st = (

let uu____7381 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_stack = stack; repl_curmod = FStar_Pervasives_Native.None; repl_env = env3; repl_ts = ts; repl_stdin = uu____7381})
in (

let uu____7382 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____7382) with
| true -> begin
(

let uu____7383 = (

let uu____7384 = (FStar_Options.file_list ())
in (FStar_List.hd uu____7384))
in (FStar_SMTEncoding_Solver.with_hints_db uu____7383 (fun uu____7388 -> (go init_st))))
end
| uu____7389 -> begin
(go init_st)
end)));
))))
end)))
end));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(

let uu____7396 = (

let uu____7397 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____7397))
in (match (uu____7396) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____7400 -> begin
()
end));
(

let uu____7401 = (FStar_Options.trace_error ())
in (match (uu____7401) with
| true -> begin
(interactive_mode' filename)
end
| uu____7402 -> begin
(FStar_All.try_with (fun uu___229_7405 -> (match (()) with
| () -> begin
((FStar_Errors.set_handler interactive_error_handler);
(interactive_mode' filename);
)
end)) (fun uu___228_7410 -> (match (uu___228_7410) with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise e);
)
end)))
end));
))




