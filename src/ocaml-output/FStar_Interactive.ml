
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

type push_kind =
| SyntaxCheck
| LaxCheck
| FullCheck


let uu___is_SyntaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SyntaxCheck -> begin
true
end
| uu____209 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____213 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____217 -> begin
false
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____230 kind restore_cmd_line_options1 msg -> (match (uu____230) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___247_241 = tcenv
in {FStar_TypeChecker_Env.solver = uu___247_241.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___247_241.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___247_241.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___247_241.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___247_241.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___247_241.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___247_241.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___247_241.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___247_241.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___247_241.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___247_241.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___247_241.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___247_241.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___247_241.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___247_241.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___247_241.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___247_241.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___247_241.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (kind = LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___247_241.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___247_241.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___247_241.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___247_241.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___247_241.FStar_TypeChecker_Env.qname_and_index})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck))
in (

let res = (FStar_Universal.push_context ((dsenv1), (tcenv1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____248 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____248 Prims.ignore))
end
| uu____249 -> begin
()
end);
res;
))))
end))


let mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____256 -> (match (uu____256) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv1), (env1));
)))
end))


let reset_mark = (fun uu____276 -> (match (uu____276) with
| (uu____279, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark ())
in (

let env1 = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env1));
)))
end))


let cleanup = (fun uu____292 -> (match (uu____292) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____303 -> (match (uu____303) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv1), (env1))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul Prims.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul Prims.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) Prims.option = (fun uu____330 curmod frag -> (match (uu____330) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____362 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____362) with
| Some (m, dsenv1, env1) -> begin
(

let uu____384 = (

let uu____391 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____391)))
in Some (uu____384))
end
| uu____401 -> begin
None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____423 = (FStar_Options.trace_error ())
in (not (uu____423))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____436 = (FStar_Options.trace_error ())
in (not (uu____436))) -> begin
((

let uu____438 = (

let uu____442 = (

let uu____445 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____445)))
in (uu____442)::[])
in (FStar_TypeChecker_Err.add_errors env uu____438));
None;
)
end
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string Prims.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____465 = (FStar_List.partition (fun x -> (

let uu____471 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____472 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____471 <> uu____472)))) deps)
in (match (uu____465) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____489 = ((

let uu____490 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____490))) || (

let uu____491 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____491))))
in (match (uu____489) with
| true -> begin
(

let uu____492 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____492))
end
| uu____493 -> begin
()
end));
Some (intf);
)
end
| (impl)::[] -> begin
None
end
| uu____495 -> begin
((

let uu____498 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____498));
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
| uu____531 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____542 = (

let uu____543 = (FStar_Options.lax ())
in (match (uu____543) with
| true -> begin
LaxCheck
end
| uu____544 -> begin
FullCheck
end))
in (push env uu____542 true "typecheck_modul"))
in (

let uu____545 = (tc_one_file remaining env1)
in (match (uu____545) with
| ((intf, impl), env2, modl, remaining1) -> begin
(

let uu____578 = (

let intf_t = (match (intf) with
| Some (intf1) -> begin
(

let uu____586 = (FStar_Util.get_file_last_modification_time intf1)
in Some (uu____586))
end
| None -> begin
None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____578) with
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
| (uu____652, uu____653) -> begin
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
| uu____715 -> begin
((false), (depnames1))
end)
end
| uu____717 -> begin
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
| uu____732 -> begin
((false), (depnames1))
end)
end
| uu____734 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____781)::ts3 -> begin
((pop env1 "");
(

let uu____803 = (

let uu____811 = (FStar_List.hd stack)
in (

let uu____816 = (FStar_List.tl stack)
in ((uu____811), (uu____816))))
in (match (uu____803) with
| ((env2, uu____830), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____864 = ts_elt
in (match (uu____864) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____882 = (match_dep depnames intf impl)
in (match (uu____882) with
| (b, depnames') -> begin
(

let uu____893 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____893) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____904 -> begin
(

let uu____905 = (

let uu____913 = (FStar_List.hd st)
in (

let uu____918 = (FStar_List.tl st)
in ((uu____913), (uu____918))))
in (match (uu____905) with
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

let uu____958 = (deps_of_our_file filename)
in (match (uu____958) with
| (filenames, uu____967) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___237_998 -> (match (uu___237_998) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____1000 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____1002 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____1002))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____1004) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____1006) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1017) -> begin
true
end
| uu____1020 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1031) -> begin
uu____1031
end))


let js_fail = (fun expected got -> (Prims.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___238_1048 -> (match (uu___238_1048) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___239_1053 -> (match (uu___239_1053) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list = (fun k uu___240_1071 -> (match (uu___240_1071) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___241_1083 -> (match (uu___241_1083) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1098 = (js_str s)
in (match (uu____1098) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1099 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1103 = (js_str s)
in (match (uu____1103) with
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
| uu____1104 -> begin
(js_fail "reduction rule" s)
end)))

type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Pop
| Push of (push_kind * Prims.string * Prims.int * Prims.int * Prims.bool)
| AutoComplete of Prims.string
| Lookup of (Prims.string * (Prims.string * Prims.int * Prims.int) Prims.option * Prims.string Prims.list)
| Compute of (Prims.string * FStar_TypeChecker_Normalize.step Prims.list Prims.option)
| Search of Prims.string
| ProtocolViolation of Prims.string 
 and query =
{qq : query'; qid : Prims.string}


let uu___is_Exit : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1149 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1153 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1157 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1161 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1171 -> begin
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
| uu____1198 -> begin
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
| uu____1218 -> begin
false
end))


let __proj__Lookup__item___0 : query'  ->  (Prims.string * (Prims.string * Prims.int * Prims.int) Prims.option * Prims.string Prims.list) = (fun projectee -> (match (projectee) with
| Lookup (_0) -> begin
_0
end))


let uu___is_Compute : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Compute (_0) -> begin
true
end
| uu____1258 -> begin
false
end))


let __proj__Compute__item___0 : query'  ->  (Prims.string * FStar_TypeChecker_Normalize.step Prims.list Prims.option) = (fun projectee -> (match (projectee) with
| Compute (_0) -> begin
_0
end))


let uu___is_Search : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Search (_0) -> begin
true
end
| uu____1282 -> begin
false
end))


let __proj__Search__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Search (_0) -> begin
_0
end))


let uu___is_ProtocolViolation : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
true
end
| uu____1294 -> begin
false
end))


let __proj__ProtocolViolation__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
_0
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "1")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("compute")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/documentation")::("lookup/definition")::("pop")::("peek")::("push")::("search")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____1316) -> begin
true
end
| uu____1317 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____1324) -> begin
uu____1324
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____1328 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____1332 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____1336 -> begin
false
end))


let try_assoc = (fun key a -> (

let uu____1358 = (FStar_Util.try_find (fun uu____1364 -> (match (uu____1364) with
| (k, uu____1368) -> begin
(k = key)
end)) a)
in (FStar_Util.map_option Prims.snd uu____1358)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____1380 = (

let uu____1381 = (

let uu____1382 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____1382))
in ProtocolViolation (uu____1381))
in {qq = uu____1380; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____1402 = (try_assoc key a)
in (match (uu____1402) with
| Some (v1) -> begin
v1
end
| None -> begin
(

let uu____1405 = (

let uu____1406 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____1406))
in (Prims.raise uu____1405))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____1415 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____1415 js_str))
in try
(match (()) with
| () -> begin
(

let query = (

let uu____1418 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____1418 js_str))
in (

let args = (

let uu____1423 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____1423 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____1436 = (try_assoc k args)
in (match (uu____1436) with
| Some (FStar_Util.JsonNull) -> begin
None
end
| other -> begin
other
end)))
in (

let uu____1441 = (match (query) with
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
| ("peek") | ("push") -> begin
(

let uu____1442 = (

let uu____1448 = (

let uu____1449 = (arg "kind")
in (FStar_All.pipe_right uu____1449 js_pushkind))
in (

let uu____1450 = (

let uu____1451 = (arg "code")
in (FStar_All.pipe_right uu____1451 js_str))
in (

let uu____1452 = (

let uu____1453 = (arg "line")
in (FStar_All.pipe_right uu____1453 js_int))
in (

let uu____1454 = (

let uu____1455 = (arg "column")
in (FStar_All.pipe_right uu____1455 js_int))
in ((uu____1448), (uu____1450), (uu____1452), (uu____1454), ((query = "peek")))))))
in Push (uu____1442))
end
| "autocomplete" -> begin
(

let uu____1456 = (

let uu____1457 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____1457 js_str))
in AutoComplete (uu____1456))
end
| "lookup" -> begin
(

let uu____1458 = (

let uu____1467 = (

let uu____1468 = (arg "symbol")
in (FStar_All.pipe_right uu____1468 js_str))
in (

let uu____1469 = (

let uu____1474 = (

let uu____1479 = (try_arg "location")
in (FStar_All.pipe_right uu____1479 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____1474 (FStar_Util.map_option (fun loc -> (

let uu____1507 = (

let uu____1508 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____1508 js_str))
in (

let uu____1509 = (

let uu____1510 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____1510 js_int))
in (

let uu____1511 = (

let uu____1512 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____1512 js_int))
in ((uu____1507), (uu____1509), (uu____1511)))))))))
in (

let uu____1513 = (

let uu____1515 = (arg "requested-info")
in (FStar_All.pipe_right uu____1515 (js_list js_str)))
in ((uu____1467), (uu____1469), (uu____1513)))))
in Lookup (uu____1458))
end
| "compute" -> begin
(

let uu____1522 = (

let uu____1527 = (

let uu____1528 = (arg "term")
in (FStar_All.pipe_right uu____1528 js_str))
in (

let uu____1529 = (

let uu____1532 = (try_arg "rules")
in (FStar_All.pipe_right uu____1532 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____1527), (uu____1529))))
in Compute (uu____1522))
end
| "search" -> begin
(

let uu____1540 = (

let uu____1541 = (arg "terms")
in (FStar_All.pipe_right uu____1541 js_str))
in Search (uu____1540))
end
| uu____1542 -> begin
(

let uu____1543 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____1543))
end)
in {qq = uu____1441; qid = qid})))))
end)
with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end))))


let validate_interactive_query : query  ->  query = (fun uu___242_1550 -> (match (uu___242_1550) with
| {qq = Push (SyntaxCheck, uu____1551, uu____1552, uu____1553, false); qid = qid} -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = qid}
end
| other -> begin
other
end))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> try
(match (()) with
| () -> begin
(

let uu____1560 = (FStar_Util.read_line stream)
in (match (uu____1560) with
| None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| Some (line) -> begin
(

let uu____1563 = (FStar_Util.json_of_string line)
in (match (uu____1563) with
| None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| Some (request) -> begin
(

let uu____1566 = (unpack_interactive_query request)
in (validate_interactive_query uu____1566))
end))
end))
end)
with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end)


let rec json_of_fstar_option : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___243_1573 -> (match (uu___243_1573) with
| FStar_Options.Bool (b) -> begin
FStar_Util.JsonBool (b)
end
| (FStar_Options.String (s)) | (FStar_Options.Path (s)) -> begin
FStar_Util.JsonStr (s)
end
| FStar_Options.Int (n1) -> begin
FStar_Util.JsonInt (n1)
end
| FStar_Options.List (vs) -> begin
(

let uu____1579 = (FStar_List.map json_of_fstar_option vs)
in FStar_Util.JsonList (uu____1579))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let json_of_opt = (fun json_of_a opt_a -> (

let uu____1600 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____1600)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____1605 = (

let uu____1607 = (

let uu____1608 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____1608))
in (

let uu____1609 = (

let uu____1611 = (

let uu____1612 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____1612))
in (uu____1611)::[])
in (uu____1607)::uu____1609))
in FStar_Util.JsonList (uu____1605)))


let json_of_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____1616 = (

let uu____1620 = (

let uu____1623 = (

let uu____1624 = (FStar_Range.file_of_range r)
in FStar_Util.JsonStr (uu____1624))
in (("fname"), (uu____1623)))
in (

let uu____1625 = (

let uu____1629 = (

let uu____1632 = (

let uu____1633 = (FStar_Range.start_of_range r)
in (json_of_pos uu____1633))
in (("beg"), (uu____1632)))
in (

let uu____1634 = (

let uu____1638 = (

let uu____1641 = (

let uu____1642 = (FStar_Range.end_of_range r)
in (json_of_pos uu____1642))
in (("end"), (uu____1641)))
in (uu____1638)::[])
in (uu____1629)::uu____1634))
in (uu____1620)::uu____1625))
in FStar_Util.JsonAssoc (uu____1616)))


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

let uu____1657 = (

let uu____1661 = (

let uu____1665 = (

let uu____1669 = (

let uu____1672 = (

let uu____1673 = (match (issue.FStar_Errors.issue_range) with
| None -> begin
[]
end
| Some (r) -> begin
(

let uu____1677 = (json_of_range r)
in (uu____1677)::[])
end)
in FStar_Util.JsonList (uu____1673))
in (("ranges"), (uu____1672)))
in (uu____1669)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____1665)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____1661)
in FStar_Util.JsonAssoc (uu____1657)))

type lookup_result =
{lr_name : Prims.string; lr_def_range : FStar_Range.range Prims.option; lr_typ : Prims.string Prims.option; lr_doc : Prims.string Prims.option; lr_def : Prims.string Prims.option}


let json_of_lookup_result : lookup_result  ->  FStar_Util.json = (fun lr -> (

let uu____1736 = (

let uu____1740 = (

let uu____1744 = (

let uu____1747 = (json_of_opt json_of_range lr.lr_def_range)
in (("defined-at"), (uu____1747)))
in (

let uu____1748 = (

let uu____1752 = (

let uu____1755 = (json_of_opt (fun _0_32 -> FStar_Util.JsonStr (_0_32)) lr.lr_typ)
in (("type"), (uu____1755)))
in (

let uu____1756 = (

let uu____1760 = (

let uu____1763 = (json_of_opt (fun _0_33 -> FStar_Util.JsonStr (_0_33)) lr.lr_doc)
in (("documentation"), (uu____1763)))
in (

let uu____1764 = (

let uu____1768 = (

let uu____1771 = (json_of_opt (fun _0_34 -> FStar_Util.JsonStr (_0_34)) lr.lr_def)
in (("definition"), (uu____1771)))
in (uu____1768)::[])
in (uu____1760)::uu____1764))
in (uu____1752)::uu____1756))
in (uu____1744)::uu____1748))
in ((("name"), (FStar_Util.JsonStr (lr.lr_name))))::uu____1740)
in FStar_Util.JsonAssoc (uu____1736)))


let json_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____1789 = (FStar_List.map (fun _0_35 -> FStar_Util.JsonStr (_0_35)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_36 -> FStar_Util.JsonList (_0_36)) uu____1789))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____1802 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____1802));
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


let write_message : Prims.string  ->  Prims.string  ->  Prims.unit = (fun level contents -> (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("message"))))::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (FStar_Util.JsonStr (contents))))::[]))))


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____1840 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____1843 = (FStar_List.map (fun _0_37 -> FStar_Util.JsonStr (_0_37)) interactive_protocol_features)
in FStar_Util.JsonList (uu____1843))
in (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::json_of_protocol_info))))))

type repl_state =
{repl_line : Prims.int; repl_column : Prims.int; repl_fname : Prims.string; repl_stack : stack_t; repl_curmod : modul_t; repl_env : env_t; repl_ts : m_timestamps; repl_stdin : FStar_Util.stream_reader}


let json_of_repl_state : repl_state  ->  (Prims.string * FStar_Util.json) Prims.list = (fun st -> (

let opts_and_defaults = (

let opt_docs = (

let uu____1918 = (FStar_Options.docs ())
in (FStar_Util.smap_of_list uu____1918))
in (

let get_doc = (fun k -> (FStar_Util.smap_try_find opt_docs k))
in (FStar_List.map (fun uu____1934 -> (match (uu____1934) with
| (k, v1) -> begin
(

let uu____1944 = (FStar_Options.get_option k)
in (

let uu____1945 = (get_doc k)
in ((k), (uu____1944), (uu____1945), (v1))))
end)) FStar_Options.defaults)))
in (

let uu____1948 = (

let uu____1951 = (

let uu____1952 = (FStar_List.map (fun uu____1960 -> (match (uu____1960) with
| (uu____1967, fstname, uu____1969, uu____1970) -> begin
FStar_Util.JsonStr (fstname)
end)) st.repl_ts)
in FStar_Util.JsonList (uu____1952))
in (("loaded-dependencies"), (uu____1951)))
in (

let uu____1975 = (

let uu____1979 = (

let uu____1982 = (

let uu____1983 = (FStar_List.map (fun uu____1990 -> (match (uu____1990) with
| (name, value, doc1, dflt1) -> begin
(

let uu____2002 = (

let uu____2006 = (

let uu____2010 = (

let uu____2013 = (json_of_fstar_option value)
in (("value"), (uu____2013)))
in (

let uu____2014 = (

let uu____2018 = (

let uu____2021 = (json_of_fstar_option dflt1)
in (("default"), (uu____2021)))
in (

let uu____2022 = (

let uu____2026 = (

let uu____2029 = (json_of_opt (fun _0_38 -> FStar_Util.JsonStr (_0_38)) doc1)
in (("documentation"), (uu____2029)))
in (uu____2026)::[])
in (uu____2018)::uu____2022))
in (uu____2010)::uu____2014))
in ((("name"), (FStar_Util.JsonStr (name))))::uu____2006)
in FStar_Util.JsonAssoc (uu____2002))
end)) opts_and_defaults)
in FStar_Util.JsonList (uu____1983))
in (("options"), (uu____1982)))
in (uu____1979)::[])
in (uu____1948)::uu____1975))))


let run_exit = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (json_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl = (fun st -> (

let uu____2097 = (

let uu____2100 = (

let uu____2101 = (json_of_repl_state st)
in FStar_Util.JsonAssoc (uu____2101))
in ((QueryOK), (uu____2100)))
in ((uu____2097), (FStar_Util.Inl (st)))))


let run_protocol_violation = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_pop = (fun st -> (match (st.repl_stack) with
| [] -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| ((env, curmod))::stack -> begin
((pop st.repl_env "#pop");
(match (((FStar_List.length stack) = (FStar_List.length st.repl_ts))) with
| true -> begin
(cleanup env)
end
| uu____2174 -> begin
()
end);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl ((

let uu___254_2179 = st
in {repl_line = uu___254_2179.repl_line; repl_column = uu___254_2179.repl_column; repl_fname = uu___254_2179.repl_fname; repl_stack = stack; repl_curmod = curmod; repl_env = env; repl_ts = uu___254_2179.repl_ts; repl_stdin = uu___254_2179.repl_stdin}))));
)
end))


let run_push = (fun st kind text1 line column1 peek_only -> (

let uu____2218 = ((st.repl_stack), (st.repl_env), (st.repl_ts))
in (match (uu____2218) with
| (stack, env, ts) -> begin
(

let uu____2231 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(

let uu____2254 = (update_deps st.repl_fname st.repl_curmod stack env ts)
in ((true), (uu____2254)))
end
| uu____2261 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____2231) with
| (restore_cmd_line_options1, (stack1, env1, ts1)) -> begin
(

let stack2 = (((env1), (st.repl_curmod)))::stack1
in (

let env2 = (push env1 kind restore_cmd_line_options1 "#push")
in (

let env_mark = (mark env2)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column1}
in (

let res = (check_frag env_mark st.repl_curmod ((frag), (false)))
in (

let errors = (

let uu____2301 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____2301 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___255_2307 = st
in {repl_line = line; repl_column = column1; repl_fname = uu___255_2307.repl_fname; repl_stack = stack2; repl_curmod = uu___255_2307.repl_curmod; repl_env = uu___255_2307.repl_env; repl_ts = ts1; repl_stdin = uu___255_2307.repl_stdin})
in (match (res) with
| Some (curmod, env3, nerrs) when ((nerrs = (Prims.parse_int "0")) && (peek_only = false)) -> begin
(

let env4 = (commit_mark env3)
in ((((QueryOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl ((

let uu___256_2336 = st'
in {repl_line = uu___256_2336.repl_line; repl_column = uu___256_2336.repl_column; repl_fname = uu___256_2336.repl_fname; repl_stack = uu___256_2336.repl_stack; repl_curmod = curmod; repl_env = env4; repl_ts = uu___256_2336.repl_ts; repl_stdin = uu___256_2336.repl_stdin})))))
end
| uu____2337 -> begin
(

let env3 = (reset_mark env_mark)
in (

let uu____2348 = (run_pop (

let uu___257_2355 = st'
in {repl_line = uu___257_2355.repl_line; repl_column = uu___257_2355.repl_column; repl_fname = uu___257_2355.repl_fname; repl_stack = uu___257_2355.repl_stack; repl_curmod = uu___257_2355.repl_curmod; repl_env = env3; repl_ts = uu___257_2355.repl_ts; repl_stdin = uu___257_2355.repl_stdin}))
in (match (uu____2348) with
| (uu____2362, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____2373 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end)))
end));
)))))))
end))
end)))


let run_lookup = (fun st symbol pos_opt requested_info -> (

let uu____2416 = st.repl_env
in (match (uu____2416) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____2436 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____2436))
in (

let lid1 = (

let uu____2439 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____2439))
in (

let uu____2442 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____2442 (FStar_Util.map_option (fun uu____2468 -> (match (uu____2468) with
| ((uu____2478, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____2490 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____2490 (FStar_Util.map_option Prims.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____2507 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____2507 (fun uu___244_2527 -> (match (uu___244_2527) with
| (FStar_Util.Inr (se, uu____2539), uu____2540) -> begin
(

let uu____2555 = (FStar_Syntax_Print.sigelt_to_string se)
in Some (uu____2555))
end
| uu____2556 -> begin
None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____2581 -> (match (uu____2581) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| Some (uu____2607) -> begin
info_at_pos_opt
end
| None -> begin
(match ((symbol = "")) with
| true -> begin
None
end
| uu____2634 -> begin
(info_of_lid_str symbol)
end)
end)
in (

let response = (match (info_opt) with
| None -> begin
((QueryNOK), (FStar_Util.JsonNull))
end
| Some (name_or_lid, typ, rng) -> begin
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

let uu____2663 = (FStar_TypeChecker_Normalize.term_to_string tcenv typ)
in Some (uu____2663))
end
| uu____2664 -> begin
None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____2669 -> begin
None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____2676 -> begin
None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
Some (rng)
end
| uu____2682 -> begin
None
end)
in (

let result = {lr_name = name; lr_def_range = def_range; lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str}
in (

let uu____2684 = (json_of_lookup_result result)
in ((QueryOK), (uu____2684)))))))))
end)
in ((response), (FStar_Util.Inl (st)))))))))
end)))


let run_completions = (fun st search_term -> (

let uu____2707 = st.repl_env
in (match (uu____2707) with
| (dsenv, tcenv) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____2737) -> begin
Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____2745, []) -> begin
None
end
| ((hs)::ts, (hc)::tc) -> begin
(

let hc_text = (FStar_Ident.text_of_id hc)
in (match ((FStar_Util.starts_with hc_text hs)) with
| true -> begin
(match (ts) with
| [] -> begin
Some (((candidate), ((FStar_String.length hs))))
end
| uu____2775 -> begin
(

let uu____2777 = (measure_anchored_match ts tc)
in (FStar_All.pipe_right uu____2777 (FStar_Util.map_option (fun uu____2796 -> (match (uu____2796) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____2811 -> begin
None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____2832 = (measure_anchored_match needle candidate)
in (match (uu____2832) with
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

let uu____2874 = (locate_match needle tc)
in (FStar_All.pipe_right uu____2874 (FStar_Util.map_option (fun uu____2903 -> (match (uu____2903) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____2929 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____2929)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____2958 -> (match (uu____2958) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____2976)::[] -> begin
true
end
| uu____2977 -> begin
false
end)
in (

let uu____2979 = (FStar_ToSyntax_Env.shorten_module_path dsenv prefix1 naked_match)
in (match (uu____2979) with
| (stripped_ns, shortened) -> begin
(

let uu____2994 = (str_of_ids shortened)
in (

let uu____2995 = (str_of_ids matched)
in (

let uu____2996 = (str_of_ids stripped_ns)
in ((uu____2994), (uu____2995), (uu____2996), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____3007 -> (match (uu____3007) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((prefix1 = "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____3022 -> begin
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

let uu____3089 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____3097 = (

let uu____3099 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____3099 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____3097), (matched_length)))) uu____3089)))
end
| uu____3103 -> begin
None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____3118 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____3154 -> (match (uu____3154) with
| (ns, id, uu____3162) -> begin
(

let uu____3167 = (

let uu____3169 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____3169))
in (match (uu____3167) with
| None -> begin
false
end
| Some (l) -> begin
(

let uu____3171 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____3171))
end))
end))))))
in (

let uu____3172 = (FStar_Util.prefix needle)
in (match (uu____3172) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____3197 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____3200 = (FStar_ToSyntax_Env.resolve_module_name dsenv l true)
in (match (uu____3200) with
| None -> begin
(case_b_find_matches_in_env ())
end
| Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____3233 = (shorten_namespace x)
in (prepare_candidate uu____3233))))))
end))))
in (

let json_candidates = (

let uu____3240 = (FStar_Util.sort_with (fun uu____3248 uu____3249 -> (match (((uu____3248), (uu____3249))) with
| ((cd1, ns1, uu____3264), (cd2, ns2, uu____3267)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_39 when (_0_39 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.map (fun uu____3278 -> (match (uu____3278) with
| (candidate, ns, match_len) -> begin
FStar_Util.JsonList ((FStar_Util.JsonInt (match_len))::(FStar_Util.JsonStr (ns))::(FStar_Util.JsonStr (candidate))::[])
end)) uu____3240))
in ((((QueryOK), (FStar_Util.JsonList (json_candidates)))), (FStar_Util.Inl (st)))))))))))))
end)))


let run_compute = (fun st term rules -> (

let run_and_rewind = (fun st1 task -> (

let env_mark = (mark st1.repl_env)
in (

let results = (task st1)
in (

let env = (reset_mark env_mark)
in (

let st' = (

let uu___258_3348 = st1
in {repl_line = uu___258_3348.repl_line; repl_column = uu___258_3348.repl_column; repl_fname = uu___258_3348.repl_fname; repl_stack = uu___258_3348.repl_stack; repl_curmod = uu___258_3348.repl_curmod; repl_env = env; repl_ts = uu___258_3348.repl_ts; repl_stdin = uu___258_3348.repl_stdin})
in ((results), (FStar_Util.Inl (st'))))))))
in (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let normalize_term1 = (fun tcenv rules1 t -> (FStar_TypeChecker_Normalize.normalize rules1 tcenv t))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____3380, ({FStar_Syntax_Syntax.lbname = uu____3381; FStar_Syntax_Syntax.lbunivs = uu____3382; FStar_Syntax_Syntax.lbtyp = uu____3383; FStar_Syntax_Syntax.lbeff = uu____3384; FStar_Syntax_Syntax.lbdef = def})::[]), uu____3386, uu____3387, uu____3388); FStar_Syntax_Syntax.sigrng = uu____3389})::[] -> begin
Some (def)
end
| uu____3409 -> begin
None
end))
in (

let parse1 = (fun frag -> (

let uu____3419 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____3419) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____3432) -> begin
Some (decls)
end
| uu____3455 -> begin
None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____3475 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (Prims.snd uu____3475)))
in (

let typecheck = (fun tcenv decls -> (

let uu____3488 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____3488) with
| (ses, uu____3496, uu____3497) -> begin
ses
end)))
in (

let rules1 = (FStar_List.append (match (rules) with
| Some (rules1) -> begin
rules1
end
| None -> begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end) ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Primops)::[]))
in (run_and_rewind st (fun st1 -> (

let uu____3510 = st1.repl_env
in (match (uu____3510) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____3518 -> begin
(

let uu____3519 = (parse1 frag)
in (match (uu____3519) with
| None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Count not parse this term")))
end
| Some (decls) -> begin
try
(match (()) with
| () -> begin
(

let decls1 = (desugar dsenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| Some (def) -> begin
(

let normalized = (normalize_term1 tcenv rules1 def)
in (

let uu____3546 = (

let uu____3547 = (FStar_Syntax_Print.term_to_string normalized)
in FStar_Util.JsonStr (uu____3547))
in ((QueryOK), (uu____3546))))
end)))
end)
with
| e -> begin
(

let uu____3552 = (

let uu____3553 = (FStar_Errors.issue_of_exn e)
in (match (uu____3553) with
| Some (issue) -> begin
(

let uu____3556 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____3556))
end
| None -> begin
(Prims.raise e)
end))
in ((QueryNOK), (uu____3552)))
end
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
| uu____3573 -> begin
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
| uu____3585 -> begin
false
end))


let __proj__TypeContainsLid__item___0 : search_term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| TypeContainsLid (_0) -> begin
_0
end))


let st_cost : search_term'  ->  Prims.int = (fun uu___245_3603 -> (match (uu___245_3603) with
| NameContainsStr (str) -> begin
(~- ((FStar_String.length str)))
end
| TypeContainsLid (lid) -> begin
(Prims.parse_int "1")
end))

type search_candidate =
{sc_lid : FStar_Ident.lid; sc_typ : FStar_Syntax_Syntax.typ Prims.option FStar_ST.ref; sc_fvars : FStar_Ident.lid FStar_Util.set Prims.option FStar_ST.ref}


let sc_of_lid : FStar_Ident.lid  ->  search_candidate = (fun lid -> (

let uu____3654 = (FStar_Util.mk_ref None)
in (

let uu____3659 = (FStar_Util.mk_ref None)
in {sc_lid = lid; sc_typ = uu____3654; sc_fvars = uu____3659})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____3677 = (FStar_ST.read sc.sc_typ)
in (match (uu____3677) with
| Some (t) -> begin
t
end
| None -> begin
(

let typ = (

let uu____3686 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____3686) with
| None -> begin
((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown) None FStar_Range.dummyRange)
end
| Some ((uu____3706, typ), uu____3708) -> begin
typ
end))
in ((FStar_ST.write sc.sc_typ (Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____3728 = (FStar_ST.read sc.sc_fvars)
in (match (uu____3728) with
| Some (fv) -> begin
fv
end
| None -> begin
(

let fv = (

let uu____3742 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____3742))
in ((FStar_ST.write sc.sc_fvars (Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____3759 = (sc_typ tcenv sc)
in (FStar_Syntax_Print.term_to_string uu____3759))
in (

let uu____3760 = (

let uu____3764 = (

let uu____3767 = (

let uu____3768 = (

let uu____3769 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____3769.FStar_Ident.str)
in FStar_Util.JsonStr (uu____3768))
in (("lid"), (uu____3767)))
in (uu____3764)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____3760))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____3781) -> begin
true
end
| uu____3782 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____3789) -> begin
uu____3789
end))


let run_search = (fun st search_str -> (

let uu____3808 = st.repl_env
in (match (uu____3808) with
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

let uu____3829 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____3829))
end)
in (found <> term.st_negate)))
in (

let parse1 = (fun search_str1 -> (

let parse_one = (fun term -> (

let negate = (FStar_Util.starts_with term "-")
in (

let term1 = (match (negate) with
| true -> begin
(FStar_Util.substring_from term (Prims.parse_int "1"))
end
| uu____3842 -> begin
term
end)
in (

let beg_quote = (FStar_Util.starts_with term1 "\"")
in (

let end_quote = (FStar_Util.ends_with term1 "\"")
in (

let strip_quotes = (fun str -> (match (((FStar_String.length str) < (Prims.parse_int "2"))) with
| true -> begin
(Prims.raise (InvalidSearch ("Empty search term")))
end
| uu____3852 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((beg_quote <> end_quote)) with
| true -> begin
(

let uu____3857 = (

let uu____3858 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____3858))
in (Prims.raise uu____3857))
end
| uu____3859 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____3860 = (strip_quotes term1)
in NameContainsStr (uu____3860))
end
| uu____3861 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____3863 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____3863) with
| None -> begin
(

let uu____3865 = (

let uu____3866 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____3866))
in (Prims.raise uu____3865))
end
| Some (lid1) -> begin
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

let uu____3881 = (match (term.st_term) with
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
| uu____3884 -> begin
""
end) uu____3881)))
in (

let results = try
(match (()) with
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

let js = (FStar_Options.with_saved_options (fun uu____3917 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_List.map (json_of_search_result dsenv tcenv) sorted1);
)))
in (match (results) with
| [] -> begin
(

let kwds = (

let uu____3922 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____3922))
in (

let uu____3924 = (

let uu____3925 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____3925))
in (Prims.raise uu____3924)))
end
| uu____3928 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)
with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___246_3957 -> (match (uu___246_3957) with
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
| Push (kind, text1, l, c, peek) -> begin
(run_push st kind text1 l c peek)
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
| ProtocolViolation (query) -> begin
(run_protocol_violation st query)
end))


let rec go : repl_state  ->  Prims.unit = (fun st -> (

let query = (read_interactive_query st.repl_stdin)
in (

let uu____3995 = (

let uu____4002 = (run_query st)
in (uu____4002 query.qq))
in (match (uu____3995) with
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

let uu____4032 = (

let uu____4034 = (FStar_ST.read issues)
in (e)::uu____4034)
in (FStar_ST.write issues uu____4032)))
in (

let count_errors = (fun uu____4045 -> (

let uu____4046 = (

let uu____4048 = (FStar_ST.read issues)
in (FStar_List.filter (fun e -> (e.FStar_Errors.issue_level = FStar_Errors.EError)) uu____4048))
in (FStar_List.length uu____4046)))
in (

let report1 = (fun uu____4059 -> (

let uu____4060 = (FStar_ST.read issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____4060)))
in (

let clear1 = (fun uu____4068 -> (FStar_ST.write issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (write_message "info"); FStar_Util.printer_prwarning = (write_message "warning"); FStar_Util.printer_prerror = (write_message "error")}


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let uu____4078 = (deps_of_our_file filename)
in (match (uu____4078) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____4092 = (tc_deps None [] env filenames [])
in (match (uu____4092) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____4108 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____4109 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____4108 uu____4109)))
in (

let env2 = (

let uu____4113 = (FStar_TypeChecker_Env.set_range (Prims.snd env1) initial_range)
in (((Prims.fst env1)), (uu____4113)))
in (

let env3 = (match (maybe_intf) with
| Some (intf) -> begin
(FStar_Universal.load_interface_decls env2 intf)
end
| None -> begin
env2
end)
in (

let init_st = (

let uu____4121 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_stack = stack; repl_curmod = None; repl_env = env3; repl_ts = ts; repl_stdin = uu____4121})
in (

let uu____4122 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____4122) with
| true -> begin
(

let uu____4123 = (

let uu____4124 = (FStar_Options.file_list ())
in (FStar_List.hd uu____4124))
in (FStar_SMTEncoding_Solver.with_hints_db uu____4123 (fun uu____4126 -> (go init_st))))
end
| uu____4127 -> begin
(go init_st)
end))))))
end)))
end));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(FStar_Errors.set_handler interactive_error_handler);
(

let uu____4134 = (

let uu____4135 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____4135))
in (match (uu____4134) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____4137 -> begin
()
end));
try
(match (()) with
| () -> begin
(interactive_mode' filename)
end)
with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(Prims.raise e);
)
end;
))




