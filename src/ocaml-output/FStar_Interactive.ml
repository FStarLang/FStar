
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


let pop : 'Auu____309 . ('Auu____309 * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____320 msg -> (match (uu____320) with
| (uu____326, env) -> begin
((FStar_Universal.pop_context env msg);
(FStar_Options.pop ());
)
end))

type push_kind =
| SyntaxCheck
| LaxCheck
| FullCheck


let uu___is_SyntaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SyntaxCheck -> begin
true
end
| uu____333 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____338 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____343 -> begin
false
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____364 kind restore_cmd_line_options1 msg -> (match (uu____364) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___213_379 = tcenv
in {FStar_TypeChecker_Env.solver = uu___213_379.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___213_379.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___213_379.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___213_379.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___213_379.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___213_379.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___213_379.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___213_379.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___213_379.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___213_379.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___213_379.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___213_379.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___213_379.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___213_379.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___213_379.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___213_379.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___213_379.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___213_379.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___213_379.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___213_379.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___213_379.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___213_379.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___213_379.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___213_379.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___213_379.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___213_379.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___213_379.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___213_379.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___213_379.FStar_TypeChecker_Env.identifier_info})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (Prims.op_Equality kind SyntaxCheck))
in (

let res = (FStar_Universal.push_context ((dsenv1), (tcenv1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____388 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____388 FStar_Pervasives.ignore))
end
| uu____389 -> begin
()
end);
res;
))))
end))


let mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____401 -> (match (uu____401) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv1), (env1));
)))
end))


let reset_mark : 'Auu____419 . ('Auu____419 * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____431 -> (match (uu____431) with
| (uu____436, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark ())
in (

let env1 = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env1));
)))
end))


let cleanup : 'Auu____445 . ('Auu____445 * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____453 -> (match (uu____453) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____471 -> (match (uu____471) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv1), (env1))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____517 curmod frag -> (match (uu____517) with
| (dsenv, env) -> begin
(FStar_All.try_with (fun uu___215_566 -> (match (()) with
| () -> begin
(

let uu____581 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____581) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____621 = (

let uu____634 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____634)))
in FStar_Pervasives_Native.Some (uu____621))
end
| uu____653 -> begin
FStar_Pervasives_Native.None
end))
end)) (fun uu___214_681 -> (match (uu___214_681) with
| FStar_All.Failure (msg) when (

let uu____697 = (FStar_Options.trace_error ())
in (not (uu____697))) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____700 = (

let uu____707 = (

let uu____712 = (FStar_TypeChecker_Env.get_range env)
in ((msg1), (uu____712)))
in (uu____707)::[])
in (FStar_TypeChecker_Err.add_errors env uu____700));
(FStar_Util.print_error msg1);
FStar_Pervasives_Native.None;
))
end
| FStar_Errors.Error (msg, r) when (

let uu____736 = (FStar_Options.trace_error ())
in (not (uu____736))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____759 = (FStar_Options.trace_error ())
in (not (uu____759))) -> begin
((

let uu____761 = (

let uu____768 = (

let uu____773 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____773)))
in (uu____768)::[])
in (FStar_TypeChecker_Err.add_errors env uu____761));
FStar_Pervasives_Native.None;
)
end)))
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____809 = (FStar_List.partition (fun x -> (

let uu____822 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____823 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____822 uu____823)))) deps)
in (match (uu____809) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____850 = ((

let uu____853 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____853))) || (

let uu____855 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____855))))
in (match (uu____850) with
| true -> begin
(

let uu____856 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____856))
end
| uu____857 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____859 -> begin
((

let uu____863 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____863));
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
| uu____918 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____937 = (

let uu____938 = (FStar_Options.lax ())
in (match (uu____938) with
| true -> begin
LaxCheck
end
| uu____939 -> begin
FullCheck
end))
in (push env uu____937 true "typecheck_modul"))
in (

let uu____940 = (tc_one_file remaining env1)
in (match (uu____940) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____991 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____1004 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____1004))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____991) with
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
| (uu____1108, uu____1109) -> begin
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
| uu____1201 -> begin
((false), (depnames1))
end)
end
| uu____1204 -> begin
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
| uu____1229 -> begin
((false), (depnames1))
end)
end
| uu____1232 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____1315)::ts3 -> begin
((pop env1 "");
(

let uu____1356 = (

let uu____1371 = (FStar_List.hd stack)
in (

let uu____1380 = (FStar_List.tl stack)
in ((uu____1371), (uu____1380))))
in (match (uu____1356) with
| ((env2, uu____1406), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____1470 = ts_elt
in (match (uu____1470) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1501 = (match_dep depnames intf impl)
in (match (uu____1501) with
| (b, depnames') -> begin
(

let uu____1520 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1520) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____1540 -> begin
(

let uu____1541 = (

let uu____1556 = (FStar_List.hd st)
in (

let uu____1565 = (FStar_List.tl st)
in ((uu____1556), (uu____1565))))
in (match (uu____1541) with
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

let uu____1642 = (deps_of_our_file filename)
in (match (uu____1642) with
| (filenames, uu____1658) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___203_1718 -> (match (uu___203_1718) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____1720 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____1722 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____1722))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____1724) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____1727) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1745) -> begin
true
end
| uu____1750 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1766) -> begin
uu____1766
end))


let js_fail : 'Auu____1777 . Prims.string  ->  FStar_Util.json  ->  'Auu____1777 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___204_1789 -> (match (uu___204_1789) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___205_1795 -> (match (uu___205_1795) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____1804 . (FStar_Util.json  ->  'Auu____1804)  ->  FStar_Util.json  ->  'Auu____1804 Prims.list = (fun k uu___206_1817 -> (match (uu___206_1817) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___207_1835 -> (match (uu___207_1835) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1860 = (js_str s)
in (match (uu____1860) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1861 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1866 = (js_str s)
in (match (uu____1866) with
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
| uu____1867 -> begin
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
| uu____1938 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1943 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1948 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1953 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1969 -> begin
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
| uu____2013 -> begin
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
| uu____2043 -> begin
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
| uu____2113 -> begin
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
| uu____2151 -> begin
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
| uu____2164 -> begin
false
end))


let uu___is_ProtocolViolation : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
true
end
| uu____2170 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___208_2194 -> (match (uu___208_2194) with
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
| Push (uu____2195) -> begin
false
end
| MissingCurrentModule -> begin
false
end
| ProtocolViolation (uu____2206) -> begin
false
end
| AutoComplete (uu____2207) -> begin
true
end
| Lookup (uu____2208) -> begin
true
end
| Compute (uu____2225) -> begin
true
end
| Search (uu____2234) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2244) -> begin
true
end
| uu____2245 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2253) -> begin
uu____2253
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____2258 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____2263 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____2268 -> begin
false
end))


let try_assoc : 'Auu____2277 'Auu____2278 . 'Auu____2278  ->  ('Auu____2278 * 'Auu____2277) Prims.list  ->  'Auu____2277 FStar_Pervasives_Native.option = (fun key a -> (

let uu____2301 = (FStar_Util.try_find (fun uu____2315 -> (match (uu____2315) with
| (k, uu____2321) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____2301)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____2338 = (

let uu____2339 = (

let uu____2340 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____2340))
in ProtocolViolation (uu____2339))
in {qq = uu____2338; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____2367 = (try_assoc key a)
in (match (uu____2367) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2371 = (

let uu____2372 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____2372))
in (FStar_Exn.raise uu____2371))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____2387 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____2387 js_str))
in (FStar_All.try_with (fun uu___217_2394 -> (match (()) with
| () -> begin
(

let query = (

let uu____2396 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____2396 js_str))
in (

let args = (

let uu____2404 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____2404 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____2421 = (try_assoc k args)
in (match (uu____2421) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____2429 = (match (query) with
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

let uu____2430 = (

let uu____2441 = (

let uu____2442 = (arg "kind")
in (FStar_All.pipe_right uu____2442 js_pushkind))
in (

let uu____2443 = (

let uu____2444 = (arg "code")
in (FStar_All.pipe_right uu____2444 js_str))
in (

let uu____2445 = (

let uu____2446 = (arg "line")
in (FStar_All.pipe_right uu____2446 js_int))
in (

let uu____2447 = (

let uu____2448 = (arg "column")
in (FStar_All.pipe_right uu____2448 js_int))
in ((uu____2441), (uu____2443), (uu____2445), (uu____2447), ((Prims.op_Equality query "peek")))))))
in Push (uu____2430))
end
| "push" -> begin
(

let uu____2449 = (

let uu____2460 = (

let uu____2461 = (arg "kind")
in (FStar_All.pipe_right uu____2461 js_pushkind))
in (

let uu____2462 = (

let uu____2463 = (arg "code")
in (FStar_All.pipe_right uu____2463 js_str))
in (

let uu____2464 = (

let uu____2465 = (arg "line")
in (FStar_All.pipe_right uu____2465 js_int))
in (

let uu____2466 = (

let uu____2467 = (arg "column")
in (FStar_All.pipe_right uu____2467 js_int))
in ((uu____2460), (uu____2462), (uu____2464), (uu____2466), ((Prims.op_Equality query "peek")))))))
in Push (uu____2449))
end
| "autocomplete" -> begin
(

let uu____2468 = (

let uu____2469 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____2469 js_str))
in AutoComplete (uu____2468))
end
| "lookup" -> begin
(

let uu____2470 = (

let uu____2487 = (

let uu____2488 = (arg "symbol")
in (FStar_All.pipe_right uu____2488 js_str))
in (

let uu____2489 = (

let uu____2498 = (

let uu____2507 = (try_arg "location")
in (FStar_All.pipe_right uu____2507 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____2498 (FStar_Util.map_option (fun loc -> (

let uu____2565 = (

let uu____2566 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____2566 js_str))
in (

let uu____2567 = (

let uu____2568 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____2568 js_int))
in (

let uu____2569 = (

let uu____2570 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____2570 js_int))
in ((uu____2565), (uu____2567), (uu____2569)))))))))
in (

let uu____2571 = (

let uu____2574 = (arg "requested-info")
in (FStar_All.pipe_right uu____2574 (js_list js_str)))
in ((uu____2487), (uu____2489), (uu____2571)))))
in Lookup (uu____2470))
end
| "compute" -> begin
(

let uu____2587 = (

let uu____2596 = (

let uu____2597 = (arg "term")
in (FStar_All.pipe_right uu____2597 js_str))
in (

let uu____2598 = (

let uu____2603 = (try_arg "rules")
in (FStar_All.pipe_right uu____2603 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____2596), (uu____2598))))
in Compute (uu____2587))
end
| "search" -> begin
(

let uu____2618 = (

let uu____2619 = (arg "terms")
in (FStar_All.pipe_right uu____2619 js_str))
in Search (uu____2618))
end
| uu____2620 -> begin
(

let uu____2621 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____2621))
end)
in {qq = uu____2429; qid = qid})))))
end)) (fun uu___216_2624 -> (match (uu___216_2624) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (FStar_All.try_with (fun uu___219_2634 -> (match (()) with
| () -> begin
(

let uu____2635 = (FStar_Util.read_line stream)
in (match (uu____2635) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____2639 = (FStar_Util.json_of_string line)
in (match (uu____2639) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(unpack_interactive_query request)
end))
end))
end)) (fun uu___218_2645 -> (match (uu___218_2645) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let rec json_of_fstar_option : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___209_2652 -> (match (uu___209_2652) with
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

let uu____2660 = (FStar_List.map json_of_fstar_option vs)
in FStar_Util.JsonList (uu____2660))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let json_of_opt : 'Auu____2669 . ('Auu____2669  ->  FStar_Util.json)  ->  'Auu____2669 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____2687 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____2687)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____2694 = (

let uu____2697 = (

let uu____2698 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____2698))
in (

let uu____2699 = (

let uu____2702 = (

let uu____2703 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____2703))
in (uu____2702)::[])
in (uu____2697)::uu____2699))
in FStar_Util.JsonList (uu____2694)))


let json_of_range_fields : Prims.string  ->  FStar_Range.pos  ->  FStar_Range.pos  ->  FStar_Util.json = (fun file b e -> (

let uu____2716 = (

let uu____2723 = (

let uu____2730 = (

let uu____2735 = (json_of_pos b)
in (("beg"), (uu____2735)))
in (

let uu____2736 = (

let uu____2743 = (

let uu____2748 = (json_of_pos e)
in (("end"), (uu____2748)))
in (uu____2743)::[])
in (uu____2730)::uu____2736))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____2723)
in FStar_Util.JsonAssoc (uu____2716)))


let json_of_use_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2769 = (FStar_Range.file_of_use_range r)
in (

let uu____2770 = (FStar_Range.start_of_use_range r)
in (

let uu____2771 = (FStar_Range.end_of_use_range r)
in (json_of_range_fields uu____2769 uu____2770 uu____2771)))))


let json_of_def_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2776 = (FStar_Range.file_of_range r)
in (

let uu____2777 = (FStar_Range.start_of_range r)
in (

let uu____2778 = (FStar_Range.end_of_range r)
in (json_of_range_fields uu____2776 uu____2777 uu____2778)))))


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

let uu____2787 = (

let uu____2794 = (

let uu____2801 = (

let uu____2808 = (

let uu____2813 = (

let uu____2814 = (

let uu____2817 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____2823 = (json_of_use_range r)
in (uu____2823)::[])
end)
in (

let uu____2824 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (Prims.op_disEquality r.FStar_Range.def_range r.FStar_Range.use_range) -> begin
(

let uu____2830 = (json_of_def_range r)
in (uu____2830)::[])
end
| uu____2831 -> begin
[]
end)
in (FStar_List.append uu____2817 uu____2824)))
in FStar_Util.JsonList (uu____2814))
in (("ranges"), (uu____2813)))
in (uu____2808)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____2801)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____2794)
in FStar_Util.JsonAssoc (uu____2787)))

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

let uu____2983 = (

let uu____2990 = (

let uu____2997 = (

let uu____3002 = (json_of_opt json_of_def_range lr.lr_def_range)
in (("defined-at"), (uu____3002)))
in (

let uu____3003 = (

let uu____3010 = (

let uu____3015 = (json_of_opt (fun _0_42 -> FStar_Util.JsonStr (_0_42)) lr.lr_typ)
in (("type"), (uu____3015)))
in (

let uu____3016 = (

let uu____3023 = (

let uu____3028 = (json_of_opt (fun _0_43 -> FStar_Util.JsonStr (_0_43)) lr.lr_doc)
in (("documentation"), (uu____3028)))
in (

let uu____3029 = (

let uu____3036 = (

let uu____3041 = (json_of_opt (fun _0_44 -> FStar_Util.JsonStr (_0_44)) lr.lr_def)
in (("definition"), (uu____3041)))
in (uu____3036)::[])
in (uu____3023)::uu____3029))
in (uu____3010)::uu____3016))
in (uu____2997)::uu____3003))
in ((("name"), (FStar_Util.JsonStr (lr.lr_name))))::uu____2990)
in FStar_Util.JsonAssoc (uu____2983)))


let json_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3074 = (FStar_List.map (fun _0_45 -> FStar_Util.JsonStr (_0_45)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_46 -> FStar_Util.JsonList (_0_46)) uu____3074))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____3096 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____3096));
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


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____3158 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3161 = (FStar_List.map (fun _0_47 -> FStar_Util.JsonStr (_0_47)) interactive_protocol_features)
in FStar_Util.JsonList (uu____3161))
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

let uu____3322 = (FStar_Options.docs ())
in (FStar_Util.smap_of_list uu____3322))
in (

let get_doc = (fun k -> (FStar_Util.smap_try_find opt_docs k))
in (FStar_List.map (fun uu____3354 -> (match (uu____3354) with
| (k, v1) -> begin
(

let uu____3371 = (FStar_Options.get_option k)
in (

let uu____3372 = (get_doc k)
in ((k), (uu____3371), (uu____3372), (v1))))
end)) FStar_Options.defaults)))
in (

let uu____3377 = (

let uu____3382 = (

let uu____3383 = (FStar_List.map (fun uu____3403 -> (match (uu____3403) with
| (uu____3416, fstname, uu____3418, uu____3419) -> begin
FStar_Util.JsonStr (fstname)
end)) st.repl_ts)
in FStar_Util.JsonList (uu____3383))
in (("loaded-dependencies"), (uu____3382)))
in (

let uu____3428 = (

let uu____3435 = (

let uu____3440 = (

let uu____3441 = (FStar_List.map (fun uu____3460 -> (match (uu____3460) with
| (name, value, doc1, dflt1) -> begin
(

let uu____3479 = (

let uu____3486 = (

let uu____3493 = (

let uu____3498 = (json_of_fstar_option value)
in (("value"), (uu____3498)))
in (

let uu____3499 = (

let uu____3506 = (

let uu____3511 = (json_of_fstar_option dflt1)
in (("default"), (uu____3511)))
in (

let uu____3512 = (

let uu____3519 = (

let uu____3524 = (json_of_opt (fun _0_48 -> FStar_Util.JsonStr (_0_48)) doc1)
in (("documentation"), (uu____3524)))
in (uu____3519)::[])
in (uu____3506)::uu____3512))
in (uu____3493)::uu____3499))
in ((("name"), (FStar_Util.JsonStr (name))))::uu____3486)
in FStar_Util.JsonAssoc (uu____3479))
end)) opts_and_defaults)
in FStar_Util.JsonList (uu____3441))
in (("options"), (uu____3440)))
in (uu____3435)::[])
in (uu____3377)::uu____3428))))


let with_printed_effect_args : 'Auu____3561 . (Prims.unit  ->  'Auu____3561)  ->  'Auu____3561 = (fun k -> (FStar_Options.with_saved_options (fun uu____3573 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____3584 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____3590 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____3597 'Auu____3598 . 'Auu____3598  ->  ((query_status * FStar_Util.json) * ('Auu____3597, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____3629 'Auu____3630 . 'Auu____3630  ->  ((query_status * FStar_Util.json) * ('Auu____3630, 'Auu____3629) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (json_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____3659 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3659) FStar_Util.either) = (fun st -> (

let uu____3676 = (

let uu____3681 = (

let uu____3682 = (json_of_repl_state st)
in FStar_Util.JsonAssoc (uu____3682))
in ((QueryOK), (uu____3681)))
in ((uu____3676), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____3705 'Auu____3706 . 'Auu____3706  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____3706, 'Auu____3705) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_missing_current_module : 'Auu____3745 'Auu____3746 'Auu____3747 . 'Auu____3747  ->  'Auu____3746  ->  ((query_status * FStar_Util.json) * ('Auu____3747, 'Auu____3745) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))), (FStar_Util.Inl (st))))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> ((FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)))


let run_pop : 'Auu____3800 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3800) FStar_Util.either) = (fun st -> (match ((nothing_left_to_pop st)) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____3825 -> begin
(match (st.repl_stack) with
| [] -> begin
(failwith "impossible")
end
| ((env, curmod))::stack -> begin
((pop st.repl_env "#pop");
(

let st' = (

let uu___220_3869 = st
in {repl_line = uu___220_3869.repl_line; repl_column = uu___220_3869.repl_column; repl_fname = uu___220_3869.repl_fname; repl_stack = stack; repl_curmod = curmod; repl_env = env; repl_ts = uu___220_3869.repl_ts; repl_stdin = uu___220_3869.repl_stdin})
in ((match ((nothing_left_to_pop st')) with
| true -> begin
(cleanup env)
end
| uu____3871 -> begin
()
end);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st')));
));
)
end)
end))


let run_push : 'Auu____3894 . repl_state  ->  push_kind  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3894) FStar_Util.either) = (fun st kind text1 line column peek_only -> (

let uu____3931 = ((st.repl_stack), (st.repl_env), (st.repl_ts))
in (match (uu____3931) with
| (stack, env, ts) -> begin
(

let uu____3953 = (match ((nothing_left_to_pop st)) with
| true -> begin
(

let uu____3974 = (update_deps st.repl_fname st.repl_curmod stack env ts)
in ((true), (uu____3974)))
end
| uu____3987 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____3953) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (st.repl_curmod)))::stack1
in (

let env2 = (push env1 kind restore_cmd_line_options1 "#push")
in (

let env_mark = (mark env2)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in (

let res = (check_frag env_mark st.repl_curmod ((frag), (false)))
in (

let errors = (

let uu____4056 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____4056 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___221_4065 = st
in {repl_line = line; repl_column = column; repl_fname = uu___221_4065.repl_fname; repl_stack = stack2; repl_curmod = uu___221_4065.repl_curmod; repl_env = uu___221_4065.repl_env; repl_ts = ts1; repl_stdin = uu___221_4065.repl_stdin})
in (match (res) with
| FStar_Pervasives_Native.Some (curmod, env3, nerrs) when ((Prims.op_Equality nerrs (Prims.parse_int "0")) && (Prims.op_Equality peek_only false)) -> begin
(

let env4 = (commit_mark env3)
in ((((QueryOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl ((

let uu___222_4119 = st'
in {repl_line = uu___222_4119.repl_line; repl_column = uu___222_4119.repl_column; repl_fname = uu___222_4119.repl_fname; repl_stack = uu___222_4119.repl_stack; repl_curmod = curmod; repl_env = env4; repl_ts = uu___222_4119.repl_ts; repl_stdin = uu___222_4119.repl_stdin})))))
end
| uu____4120 -> begin
(

let env3 = (reset_mark env_mark)
in (

let uu____4140 = (run_pop (

let uu___223_4154 = st'
in {repl_line = uu___223_4154.repl_line; repl_column = uu___223_4154.repl_column; repl_fname = uu___223_4154.repl_fname; repl_stack = uu___223_4154.repl_stack; repl_curmod = uu___223_4154.repl_curmod; repl_env = env3; repl_ts = uu___223_4154.repl_ts; repl_stdin = uu___223_4154.repl_stdin}))
in (match (uu____4140) with
| (uu____4167, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____4186 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end)))
end));
)))))))
end))
end)))


let run_lookup : 'Auu____4205 . repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4205) FStar_Util.either) = (fun st symbol pos_opt requested_info -> (

let uu____4254 = st.repl_env
in (match (uu____4254) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____4286 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____4286))
in (

let lid1 = (

let uu____4290 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____4290))
in (

let uu____4295 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____4295 (FStar_Util.map_option (fun uu____4350 -> (match (uu____4350) with
| ((uu____4369, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____4386 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____4386 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____4415 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____4415 (fun uu___210_4459 -> (match (uu___210_4459) with
| (FStar_Util.Inr (se, uu____4481), uu____4482) -> begin
(

let uu____4511 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____4511))
end
| uu____4512 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____4564 -> (match (uu____4564) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____4611) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4664 -> begin
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

let uu____4713 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____4713))
end
| uu____4714 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____4721 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____4732 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____4742 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {lr_name = name; lr_def_range = def_range; lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str}
in (

let uu____4744 = (json_of_lookup_result result)
in ((QueryOK), (uu____4744)))))))))
end)
in ((response), (FStar_Util.Inl (st)))))))))
end)))


let run_completions : 'Auu____4759 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4759) FStar_Util.either) = (fun st search_term -> (

let uu____4780 = st.repl_env
in (match (uu____4780) with
| (dsenv, tcenv) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____4830) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____4845, []) -> begin
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
| uu____4895 -> begin
(

let uu____4898 = (measure_anchored_match ts tc)
in (FStar_All.pipe_right uu____4898 (FStar_Util.map_option (fun uu____4938 -> (match (uu____4938) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____4959 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____4993 = (measure_anchored_match needle candidate)
in (match (uu____4993) with
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

let uu____5072 = (locate_match needle tc)
in (FStar_All.pipe_right uu____5072 (FStar_Util.map_option (fun uu____5133 -> (match (uu____5133) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____5177 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____5177)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____5224 -> (match (uu____5224) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____5255)::[] -> begin
true
end
| uu____5256 -> begin
false
end)
in (

let uu____5259 = (FStar_ToSyntax_Env.shorten_module_path dsenv prefix1 naked_match)
in (match (uu____5259) with
| (stripped_ns, shortened) -> begin
(

let uu____5286 = (str_of_ids shortened)
in (

let uu____5287 = (str_of_ids matched)
in (

let uu____5288 = (str_of_ids stripped_ns)
in ((uu____5286), (uu____5287), (uu____5288), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____5306 -> (match (uu____5306) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((Prims.op_Equality prefix1 "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____5331 -> begin
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

let uu____5434 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____5450 = (

let uu____5453 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____5453 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____5450), (matched_length)))) uu____5434)))
end
| uu____5460 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____5486 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____5561 -> (match (uu____5561) with
| (ns, id, uu____5574) -> begin
(

let uu____5583 = (

let uu____5586 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____5586))
in (match (uu____5583) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____5588 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____5588))
end))
end))))))
in (

let uu____5589 = (FStar_Util.prefix needle)
in (match (uu____5589) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____5635 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____5639 = (FStar_ToSyntax_Env.resolve_module_name dsenv l true)
in (match (uu____5639) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____5704 = (shorten_namespace x)
in (prepare_candidate uu____5704))))))
end))))
in (

let json_candidates = (

let uu____5716 = (FStar_Util.sort_with (fun uu____5739 uu____5740 -> (match (((uu____5739), (uu____5740))) with
| ((cd1, ns1, uu____5767), (cd2, ns2, uu____5770)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_49 when (_0_49 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.map (fun uu____5794 -> (match (uu____5794) with
| (candidate, ns, match_len) -> begin
FStar_Util.JsonList ((FStar_Util.JsonInt (match_len))::(FStar_Util.JsonStr (ns))::(FStar_Util.JsonStr (candidate))::[])
end)) uu____5716))
in ((((QueryOK), (FStar_Util.JsonList (json_candidates)))), (FStar_Util.Inl (st)))))))))))))
end)))


let run_compute : 'Auu____5820 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5820) FStar_Util.either) = (fun st term rules -> (

let run_and_rewind = (fun st1 task -> (

let env_mark = (mark st1.repl_env)
in (

let results = (task st1)
in (

let env = (reset_mark env_mark)
in (

let st' = (

let uu___224_5901 = st1
in {repl_line = uu___224_5901.repl_line; repl_column = uu___224_5901.repl_column; repl_fname = uu___224_5901.repl_fname; repl_stack = uu___224_5901.repl_stack; repl_curmod = uu___224_5901.repl_curmod; repl_env = env; repl_ts = uu___224_5901.repl_ts; repl_stdin = uu___224_5901.repl_stdin})
in ((results), (FStar_Util.Inl (st'))))))))
in (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let normalize_term1 = (fun tcenv rules1 t -> (FStar_TypeChecker_Normalize.normalize rules1 tcenv t))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5953, ({FStar_Syntax_Syntax.lbname = uu____5954; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____5956; FStar_Syntax_Syntax.lbeff = uu____5957; FStar_Syntax_Syntax.lbdef = def})::[]), uu____5959); FStar_Syntax_Syntax.sigrng = uu____5960; FStar_Syntax_Syntax.sigquals = uu____5961; FStar_Syntax_Syntax.sigmeta = uu____5962; FStar_Syntax_Syntax.sigattrs = uu____5963})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____6002 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____6021 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____6021) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____6045) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____6090 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____6122 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (FStar_Pervasives_Native.snd uu____6122)))
in (

let typecheck = (fun tcenv decls -> (

let uu____6140 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____6140) with
| (ses, uu____6154, uu____6155) -> begin
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

let uu____6183 = st1.repl_env
in (match (uu____6183) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____6195 -> begin
(

let uu____6196 = (parse1 frag)
in (match (uu____6196) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____6219 -> (

let decls1 = (desugar dsenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____6254 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____6254) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (

let normalized = (normalize_term1 tcenv1 rules1 def1)
in (

let uu____6267 = (

let uu____6268 = (term_to_string tcenv1 normalized)
in FStar_Util.JsonStr (uu____6268))
in ((QueryOK), (uu____6267)))))
end))
end))))
in (

let uu____6269 = (FStar_Options.trace_error ())
in (match (uu____6269) with
| true -> begin
(aux ())
end
| uu____6274 -> begin
(FStar_All.try_with (fun uu___226_6280 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___225_6288 -> (match (uu___225_6288) with
| e -> begin
(

let uu____6294 = (

let uu____6295 = (FStar_Errors.issue_of_exn e)
in (match (uu____6295) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____6299 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____6299))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise e)
end))
in ((QueryNOK), (uu____6294)))
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
| uu____6321 -> begin
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
| uu____6335 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___211_6359 -> (match (uu___211_6359) with
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

let uu____6527 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____6534 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____6527; sc_fvars = uu____6534})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____6583 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____6583) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____6608 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____6608) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____6629, typ), uu____6631) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____6675 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____6675) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____6718 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____6718))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____6761 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____6761))
in (

let uu____6762 = (

let uu____6769 = (

let uu____6774 = (

let uu____6775 = (

let uu____6776 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____6776.FStar_Ident.str)
in FStar_Util.JsonStr (uu____6775))
in (("lid"), (uu____6774)))
in (uu____6769)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____6762))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____6796) -> begin
true
end
| uu____6797 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____6805) -> begin
uu____6805
end))


let run_search : 'Auu____6812 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6812) FStar_Util.either) = (fun st search_str -> (

let uu____6833 = st.repl_env
in (match (uu____6833) with
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

let uu____6861 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____6861))
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
| uu____6876 -> begin
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
| uu____6883 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____6885 = (

let uu____6886 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____6886))
in (FStar_Exn.raise uu____6885))
end
| uu____6887 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____6888 = (strip_quotes term1)
in NameContainsStr (uu____6888))
end
| uu____6889 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____6891 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____6891) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6894 = (

let uu____6895 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____6895))
in (FStar_Exn.raise uu____6894))
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

let uu____6911 = (match (term.st_term) with
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
| uu____6914 -> begin
""
end) uu____6911)))
in (

let results = (FStar_All.try_with (fun uu___228_6935 -> (match (()) with
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

let uu____6974 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____6974))
in (

let uu____6977 = (

let uu____6978 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____6978))
in (FStar_Exn.raise uu____6977)))
end
| uu____6983 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___227_6988 -> (match (uu___227_6988) with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end)))
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___212_7034 -> (match (uu___212_7034) with
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
| Push (SyntaxCheck, uu____7096, uu____7097, uu____7098, false) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____7099 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = MissingCurrentModule; qid = q.qid}
end
| uu____7100 -> begin
q
end)
end))


let rec go : repl_state  ->  Prims.unit = (fun st -> (

let query = (

let uu____7106 = (read_interactive_query st.repl_stdin)
in (validate_query st uu____7106))
in (

let uu____7107 = (

let uu____7120 = (run_query st)
in (uu____7120 query.qq))
in (match (uu____7107) with
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

let uu____7164 = (

let uu____7167 = (FStar_ST.op_Bang issues)
in (e)::uu____7167)
in (FStar_ST.op_Colon_Equals issues uu____7164)))
in (

let count_errors = (fun uu____7237 -> (

let uu____7238 = (

let uu____7241 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____7241))
in (FStar_List.length uu____7238)))
in (

let report1 = (fun uu____7283 -> (

let uu____7284 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____7284)))
in (

let clear1 = (fun uu____7322 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (fun s -> (write_message "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (write_message "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (write_message "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label1 get_string get_json -> (

let uu____7377 = (get_json ())
in (write_message label1 uu____7377)))}


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let uu____7383 = (deps_of_our_file filename)
in (match (uu____7383) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____7407 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____7407) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____7434 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____7435 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____7434 uu____7435)))
in (

let env2 = (

let uu____7441 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env1) initial_range)
in (((FStar_Pervasives_Native.fst env1)), (uu____7441)))
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

let uu____7454 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_stack = stack; repl_curmod = FStar_Pervasives_Native.None; repl_env = env3; repl_ts = ts; repl_stdin = uu____7454})
in (

let uu____7455 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____7455) with
| true -> begin
(

let uu____7456 = (

let uu____7457 = (FStar_Options.file_list ())
in (FStar_List.hd uu____7457))
in (FStar_SMTEncoding_Solver.with_hints_db uu____7456 (fun uu____7461 -> (go init_st))))
end
| uu____7462 -> begin
(go init_st)
end)));
))))
end)))
end));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(

let uu____7469 = (

let uu____7470 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____7470))
in (match (uu____7469) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____7473 -> begin
()
end));
(

let uu____7474 = (FStar_Options.trace_error ())
in (match (uu____7474) with
| true -> begin
(interactive_mode' filename)
end
| uu____7475 -> begin
(FStar_All.try_with (fun uu___230_7478 -> (match (()) with
| () -> begin
((FStar_Errors.set_handler interactive_error_handler);
(interactive_mode' filename);
)
end)) (fun uu___229_7483 -> (match (uu___229_7483) with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise e);
)
end)))
end));
))




