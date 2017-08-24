
open Prims
open FStar_Pervasives

let tc_one_file : Prims.string Prims.list  ->  FStar_Universal.uenv  ->  ((Prims.string FStar_Pervasives_Native.option * Prims.string) * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.string Prims.list) = (fun remaining uenv -> (

let uu____18 = uenv
in (match (uu____18) with
| (dsenv, env) -> begin
(

let uu____30 = (match (remaining) with
| (intf)::(impl)::remaining1 when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____51 = (FStar_Universal.tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____51) with
| (uu____66, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.Some (intf)), (impl))), (dsenv1), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____83 = (FStar_Universal.tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____83) with
| (uu____98, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.None), (intf_or_impl))), (dsenv1), (env1), (remaining1))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____30) with
| ((intf, impl), dsenv1, env1, remaining1) -> begin
((((intf), (impl))), (((dsenv1), (env1))), (remaining1))
end))
end)))


let tc_prims : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____152 -> (

let uu____153 = (FStar_Universal.tc_prims ())
in (match (uu____153) with
| (uu____161, dsenv, env) -> begin
((dsenv), (env))
end)))


type env_t =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let pop = (fun uu____186 msg -> (match (uu____186) with
| (uu____190, env) -> begin
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
| uu____196 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____200 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____204 -> begin
false
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____217 kind restore_cmd_line_options1 msg -> (match (uu____217) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___207_228 = tcenv
in {FStar_TypeChecker_Env.solver = uu___207_228.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___207_228.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___207_228.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___207_228.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___207_228.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___207_228.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___207_228.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___207_228.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___207_228.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___207_228.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___207_228.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___207_228.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___207_228.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___207_228.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___207_228.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___207_228.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___207_228.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___207_228.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (kind = LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___207_228.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___207_228.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___207_228.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___207_228.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___207_228.FStar_TypeChecker_Env.qname_and_index})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck))
in (

let res = (FStar_Universal.push_context ((dsenv1), (tcenv1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____235 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____235 FStar_Pervasives.ignore))
end
| uu____236 -> begin
()
end);
res;
))))
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


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____317 curmod frag -> (match (uu____317) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____349 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____349) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____371 = (

let uu____378 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____378)))
in FStar_Pervasives_Native.Some (uu____371))
end
| uu____388 -> begin
FStar_Pervasives_Native.None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____410 = (FStar_Options.trace_error ())
in (not (uu____410))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____423 = (FStar_Options.trace_error ())
in (not (uu____423))) -> begin
((

let uu____425 = (

let uu____429 = (

let uu____432 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____432)))
in (uu____429)::[])
in (FStar_TypeChecker_Err.add_errors env uu____425));
FStar_Pervasives_Native.None;
)
end
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____452 = (FStar_List.partition (fun x -> (

let uu____458 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____459 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____458 <> uu____459)))) deps)
in (match (uu____452) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____476 = ((

let uu____477 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____477))) || (

let uu____478 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____478))))
in (match (uu____476) with
| true -> begin
(

let uu____479 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____479))
end
| uu____480 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____482 -> begin
((

let uu____485 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____485));
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
| uu____518 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____529 = (

let uu____530 = (FStar_Options.lax ())
in (match (uu____530) with
| true -> begin
LaxCheck
end
| uu____531 -> begin
FullCheck
end))
in (push env uu____529 true "typecheck_modul"))
in (

let uu____532 = (tc_one_file remaining env1)
in (match (uu____532) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____560 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____568 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____568))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____560) with
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
| (uu____634, uu____635) -> begin
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
| uu____697 -> begin
((false), (depnames1))
end)
end
| uu____699 -> begin
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
| uu____714 -> begin
((false), (depnames1))
end)
end
| uu____716 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____763)::ts3 -> begin
((pop env1 "");
(

let uu____785 = (

let uu____793 = (FStar_List.hd stack)
in (

let uu____798 = (FStar_List.tl stack)
in ((uu____793), (uu____798))))
in (match (uu____785) with
| ((env2, uu____812), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____846 = ts_elt
in (match (uu____846) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____864 = (match_dep depnames intf impl)
in (match (uu____864) with
| (b, depnames') -> begin
(

let uu____875 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____875) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____886 -> begin
(

let uu____887 = (

let uu____895 = (FStar_List.hd st)
in (

let uu____900 = (FStar_List.tl st)
in ((uu____895), (uu____900))))
in (match (uu____887) with
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

let uu____940 = (deps_of_our_file filename)
in (match (uu____940) with
| (filenames, uu____949) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___197_980 -> (match (uu___197_980) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____982 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____984 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____984))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____986) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____988) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1000) -> begin
true
end
| uu____1003 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1014) -> begin
uu____1014
end))


let js_fail = (fun expected got -> (FStar_Pervasives.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___198_1031 -> (match (uu___198_1031) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___199_1036 -> (match (uu___199_1036) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list = (fun k uu___200_1054 -> (match (uu___200_1054) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___201_1066 -> (match (uu___201_1066) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1081 = (js_str s)
in (match (uu____1081) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1082 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1086 = (js_str s)
in (match (uu____1086) with
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
| uu____1087 -> begin
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
| ProtocolViolation of Prims.string 
 and query =
{qq : query'; qid : Prims.string}


let uu___is_Exit : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1140 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1144 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1148 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1152 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1162 -> begin
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
| uu____1189 -> begin
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
| uu____1209 -> begin
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
| uu____1249 -> begin
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
| uu____1273 -> begin
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
| uu____1285 -> begin
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
| InvalidQuery (uu____1308) -> begin
true
end
| uu____1309 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____1316) -> begin
uu____1316
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____1320 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____1324 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____1328 -> begin
false
end))


let try_assoc = (fun key a -> (

let uu____1350 = (FStar_Util.try_find (fun uu____1356 -> (match (uu____1356) with
| (k, uu____1360) -> begin
(k = key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____1350)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____1372 = (

let uu____1373 = (

let uu____1374 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____1374))
in ProtocolViolation (uu____1373))
in {qq = uu____1372; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____1394 = (try_assoc key a)
in (match (uu____1394) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1397 = (

let uu____1398 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____1398))
in (FStar_Pervasives.raise uu____1397))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____1407 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____1407 js_str))
in try
(match (()) with
| () -> begin
(

let query = (

let uu____1410 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____1410 js_str))
in (

let args = (

let uu____1415 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____1415 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____1428 = (try_assoc k args)
in (match (uu____1428) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____1433 = (match (query) with
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

let uu____1434 = (

let uu____1440 = (

let uu____1441 = (arg "kind")
in (FStar_All.pipe_right uu____1441 js_pushkind))
in (

let uu____1442 = (

let uu____1443 = (arg "code")
in (FStar_All.pipe_right uu____1443 js_str))
in (

let uu____1444 = (

let uu____1445 = (arg "line")
in (FStar_All.pipe_right uu____1445 js_int))
in (

let uu____1446 = (

let uu____1447 = (arg "column")
in (FStar_All.pipe_right uu____1447 js_int))
in ((uu____1440), (uu____1442), (uu____1444), (uu____1446), ((query = "peek")))))))
in Push (uu____1434))
end
| "push" -> begin
(

let uu____1448 = (

let uu____1454 = (

let uu____1455 = (arg "kind")
in (FStar_All.pipe_right uu____1455 js_pushkind))
in (

let uu____1456 = (

let uu____1457 = (arg "code")
in (FStar_All.pipe_right uu____1457 js_str))
in (

let uu____1458 = (

let uu____1459 = (arg "line")
in (FStar_All.pipe_right uu____1459 js_int))
in (

let uu____1460 = (

let uu____1461 = (arg "column")
in (FStar_All.pipe_right uu____1461 js_int))
in ((uu____1454), (uu____1456), (uu____1458), (uu____1460), ((query = "peek")))))))
in Push (uu____1448))
end
| "autocomplete" -> begin
(

let uu____1462 = (

let uu____1463 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____1463 js_str))
in AutoComplete (uu____1462))
end
| "lookup" -> begin
(

let uu____1464 = (

let uu____1473 = (

let uu____1474 = (arg "symbol")
in (FStar_All.pipe_right uu____1474 js_str))
in (

let uu____1475 = (

let uu____1480 = (

let uu____1485 = (try_arg "location")
in (FStar_All.pipe_right uu____1485 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____1480 (FStar_Util.map_option (fun loc -> (

let uu____1513 = (

let uu____1514 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____1514 js_str))
in (

let uu____1515 = (

let uu____1516 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____1516 js_int))
in (

let uu____1517 = (

let uu____1518 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____1518 js_int))
in ((uu____1513), (uu____1515), (uu____1517)))))))))
in (

let uu____1519 = (

let uu____1521 = (arg "requested-info")
in (FStar_All.pipe_right uu____1521 (js_list js_str)))
in ((uu____1473), (uu____1475), (uu____1519)))))
in Lookup (uu____1464))
end
| "compute" -> begin
(

let uu____1528 = (

let uu____1533 = (

let uu____1534 = (arg "term")
in (FStar_All.pipe_right uu____1534 js_str))
in (

let uu____1535 = (

let uu____1538 = (try_arg "rules")
in (FStar_All.pipe_right uu____1538 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____1533), (uu____1535))))
in Compute (uu____1528))
end
| "search" -> begin
(

let uu____1546 = (

let uu____1547 = (arg "terms")
in (FStar_All.pipe_right uu____1547 js_str))
in Search (uu____1546))
end
| uu____1548 -> begin
(

let uu____1549 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____1549))
end)
in {qq = uu____1433; qid = qid})))))
end)
with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end))))


let validate_interactive_query : query  ->  query = (fun uu___202_1556 -> (match (uu___202_1556) with
| {qq = Push (SyntaxCheck, uu____1557, uu____1558, uu____1559, false); qid = qid} -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = qid}
end
| other -> begin
other
end))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> try
(match (()) with
| () -> begin
(

let uu____1566 = (FStar_Util.read_line stream)
in (match (uu____1566) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____1569 = (FStar_Util.json_of_string line)
in (match (uu____1569) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(

let uu____1572 = (unpack_interactive_query request)
in (validate_interactive_query uu____1572))
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


let rec json_of_fstar_option : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___203_1579 -> (match (uu___203_1579) with
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

let uu____1586 = (FStar_List.map json_of_fstar_option vs)
in FStar_Util.JsonList (uu____1586))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let json_of_opt = (fun json_of_a opt_a -> (

let uu____1607 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____1607)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____1612 = (

let uu____1614 = (

let uu____1615 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____1615))
in (

let uu____1616 = (

let uu____1618 = (

let uu____1619 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____1619))
in (uu____1618)::[])
in (uu____1614)::uu____1616))
in FStar_Util.JsonList (uu____1612)))


let json_of_range_fields : Prims.string  ->  FStar_Range.pos  ->  FStar_Range.pos  ->  FStar_Util.json = (fun file b e -> (

let uu____1629 = (

let uu____1633 = (

let uu____1637 = (

let uu____1640 = (json_of_pos b)
in (("beg"), (uu____1640)))
in (

let uu____1641 = (

let uu____1645 = (

let uu____1648 = (json_of_pos e)
in (("end"), (uu____1648)))
in (uu____1645)::[])
in (uu____1637)::uu____1641))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____1633)
in FStar_Util.JsonAssoc (uu____1629)))


let json_of_use_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____1660 = (FStar_Range.file_of_use_range r)
in (

let uu____1661 = (FStar_Range.start_of_use_range r)
in (

let uu____1662 = (FStar_Range.end_of_use_range r)
in (json_of_range_fields uu____1660 uu____1661 uu____1662)))))


let json_of_def_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____1666 = (FStar_Range.file_of_range r)
in (

let uu____1667 = (FStar_Range.start_of_range r)
in (

let uu____1668 = (FStar_Range.end_of_range r)
in (json_of_range_fields uu____1666 uu____1667 uu____1668)))))


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

let uu____1675 = (

let uu____1679 = (

let uu____1683 = (

let uu____1687 = (

let uu____1690 = (

let uu____1691 = (

let uu____1693 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1697 = (json_of_use_range r)
in (uu____1697)::[])
end)
in (

let uu____1698 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (r.FStar_Range.def_range <> r.FStar_Range.use_range) -> begin
(

let uu____1702 = (json_of_def_range r)
in (uu____1702)::[])
end
| uu____1703 -> begin
[]
end)
in (FStar_List.append uu____1693 uu____1698)))
in FStar_Util.JsonList (uu____1691))
in (("ranges"), (uu____1690)))
in (uu____1687)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____1683)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____1679)
in FStar_Util.JsonAssoc (uu____1675)))

type lookup_result =
{lr_name : Prims.string; lr_def_range : FStar_Range.range FStar_Pervasives_Native.option; lr_typ : Prims.string FStar_Pervasives_Native.option; lr_doc : Prims.string FStar_Pervasives_Native.option; lr_def : Prims.string FStar_Pervasives_Native.option}


let json_of_lookup_result : lookup_result  ->  FStar_Util.json = (fun lr -> (

let uu____1768 = (

let uu____1772 = (

let uu____1776 = (

let uu____1779 = (json_of_opt json_of_def_range lr.lr_def_range)
in (("defined-at"), (uu____1779)))
in (

let uu____1780 = (

let uu____1784 = (

let uu____1787 = (json_of_opt (fun _0_33 -> FStar_Util.JsonStr (_0_33)) lr.lr_typ)
in (("type"), (uu____1787)))
in (

let uu____1788 = (

let uu____1792 = (

let uu____1795 = (json_of_opt (fun _0_34 -> FStar_Util.JsonStr (_0_34)) lr.lr_doc)
in (("documentation"), (uu____1795)))
in (

let uu____1796 = (

let uu____1800 = (

let uu____1803 = (json_of_opt (fun _0_35 -> FStar_Util.JsonStr (_0_35)) lr.lr_def)
in (("definition"), (uu____1803)))
in (uu____1800)::[])
in (uu____1792)::uu____1796))
in (uu____1784)::uu____1788))
in (uu____1776)::uu____1780))
in ((("name"), (FStar_Util.JsonStr (lr.lr_name))))::uu____1772)
in FStar_Util.JsonAssoc (uu____1768)))


let json_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____1821 = (FStar_List.map (fun _0_36 -> FStar_Util.JsonStr (_0_36)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_37 -> FStar_Util.JsonList (_0_37)) uu____1821))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____1834 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____1834));
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


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____1872 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____1875 = (FStar_List.map (fun _0_38 -> FStar_Util.JsonStr (_0_38)) interactive_protocol_features)
in FStar_Util.JsonList (uu____1875))
in (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::json_of_protocol_info))))))

type repl_state =
{repl_line : Prims.int; repl_column : Prims.int; repl_fname : Prims.string; repl_stack : stack_t; repl_curmod : modul_t; repl_env : env_t; repl_ts : m_timestamps; repl_stdin : FStar_Util.stream_reader}


let json_of_repl_state : repl_state  ->  (Prims.string * FStar_Util.json) Prims.list = (fun st -> (

let opts_and_defaults = (

let opt_docs = (

let uu____1958 = (FStar_Options.docs ())
in (FStar_Util.smap_of_list uu____1958))
in (

let get_doc = (fun k -> (FStar_Util.smap_try_find opt_docs k))
in (FStar_List.map (fun uu____1974 -> (match (uu____1974) with
| (k, v1) -> begin
(

let uu____1984 = (FStar_Options.get_option k)
in (

let uu____1985 = (get_doc k)
in ((k), (uu____1984), (uu____1985), (v1))))
end)) FStar_Options.defaults)))
in (

let uu____1988 = (

let uu____1991 = (

let uu____1992 = (FStar_List.map (fun uu____2000 -> (match (uu____2000) with
| (uu____2007, fstname, uu____2009, uu____2010) -> begin
FStar_Util.JsonStr (fstname)
end)) st.repl_ts)
in FStar_Util.JsonList (uu____1992))
in (("loaded-dependencies"), (uu____1991)))
in (

let uu____2015 = (

let uu____2019 = (

let uu____2022 = (

let uu____2023 = (FStar_List.map (fun uu____2030 -> (match (uu____2030) with
| (name, value, doc1, dflt1) -> begin
(

let uu____2042 = (

let uu____2046 = (

let uu____2050 = (

let uu____2053 = (json_of_fstar_option value)
in (("value"), (uu____2053)))
in (

let uu____2054 = (

let uu____2058 = (

let uu____2061 = (json_of_fstar_option dflt1)
in (("default"), (uu____2061)))
in (

let uu____2062 = (

let uu____2066 = (

let uu____2069 = (json_of_opt (fun _0_39 -> FStar_Util.JsonStr (_0_39)) doc1)
in (("documentation"), (uu____2069)))
in (uu____2066)::[])
in (uu____2058)::uu____2062))
in (uu____2050)::uu____2054))
in ((("name"), (FStar_Util.JsonStr (name))))::uu____2046)
in FStar_Util.JsonAssoc (uu____2042))
end)) opts_and_defaults)
in FStar_Util.JsonList (uu____2023))
in (("options"), (uu____2022)))
in (uu____2019)::[])
in (uu____1988)::uu____2015))))


let run_exit = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (json_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl = (fun st -> (

let uu____2137 = (

let uu____2140 = (

let uu____2141 = (json_of_repl_state st)
in FStar_Util.JsonAssoc (uu____2141))
in ((QueryOK), (uu____2140)))
in ((uu____2137), (FStar_Util.Inl (st)))))


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
| uu____2214 -> begin
()
end);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl ((

let uu___214_2219 = st
in {repl_line = uu___214_2219.repl_line; repl_column = uu___214_2219.repl_column; repl_fname = uu___214_2219.repl_fname; repl_stack = stack; repl_curmod = curmod; repl_env = env; repl_ts = uu___214_2219.repl_ts; repl_stdin = uu___214_2219.repl_stdin}))));
)
end))


let run_push = (fun st kind text1 line column1 peek_only -> (

let uu____2258 = ((st.repl_stack), (st.repl_env), (st.repl_ts))
in (match (uu____2258) with
| (stack, env, ts) -> begin
(

let uu____2271 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(

let uu____2294 = (update_deps st.repl_fname st.repl_curmod stack env ts)
in ((true), (uu____2294)))
end
| uu____2301 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____2271) with
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

let uu____2341 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____2341 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___215_2347 = st
in {repl_line = line; repl_column = column1; repl_fname = uu___215_2347.repl_fname; repl_stack = stack2; repl_curmod = uu___215_2347.repl_curmod; repl_env = uu___215_2347.repl_env; repl_ts = ts1; repl_stdin = uu___215_2347.repl_stdin})
in (match (res) with
| FStar_Pervasives_Native.Some (curmod, env3, nerrs) when ((nerrs = (Prims.parse_int "0")) && (peek_only = false)) -> begin
(

let env4 = (commit_mark env3)
in ((((QueryOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl ((

let uu___216_2376 = st'
in {repl_line = uu___216_2376.repl_line; repl_column = uu___216_2376.repl_column; repl_fname = uu___216_2376.repl_fname; repl_stack = uu___216_2376.repl_stack; repl_curmod = curmod; repl_env = env4; repl_ts = uu___216_2376.repl_ts; repl_stdin = uu___216_2376.repl_stdin})))))
end
| uu____2377 -> begin
(

let env3 = (reset_mark env_mark)
in (

let uu____2388 = (run_pop (

let uu___217_2395 = st'
in {repl_line = uu___217_2395.repl_line; repl_column = uu___217_2395.repl_column; repl_fname = uu___217_2395.repl_fname; repl_stack = uu___217_2395.repl_stack; repl_curmod = uu___217_2395.repl_curmod; repl_env = env3; repl_ts = uu___217_2395.repl_ts; repl_stdin = uu___217_2395.repl_stdin}))
in (match (uu____2388) with
| (uu____2402, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____2413 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end)))
end));
)))))))
end))
end)))


let run_lookup = (fun st symbol pos_opt requested_info -> (

let uu____2456 = st.repl_env
in (match (uu____2456) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____2476 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____2476))
in (

let lid1 = (

let uu____2479 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____2479))
in (

let uu____2482 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____2482 (FStar_Util.map_option (fun uu____2508 -> (match (uu____2508) with
| ((uu____2518, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____2530 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____2530 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____2547 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____2547 (fun uu___204_2567 -> (match (uu___204_2567) with
| (FStar_Util.Inr (se, uu____2579), uu____2580) -> begin
(

let uu____2595 = (FStar_Syntax_Print.sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____2595))
end
| uu____2596 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____2621 -> (match (uu____2621) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____2647) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((symbol = "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2674 -> begin
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

let uu____2703 = (FStar_TypeChecker_Normalize.term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____2703))
end
| uu____2704 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____2709 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____2716 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____2722 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {lr_name = name; lr_def_range = def_range; lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str}
in (

let uu____2724 = (json_of_lookup_result result)
in ((QueryOK), (uu____2724)))))))))
end)
in ((response), (FStar_Util.Inl (st)))))))))
end)))


let run_completions = (fun st search_term -> (

let uu____2747 = st.repl_env
in (match (uu____2747) with
| (dsenv, tcenv) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____2777) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____2785, []) -> begin
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
| uu____2815 -> begin
(

let uu____2817 = (measure_anchored_match ts tc)
in (FStar_All.pipe_right uu____2817 (FStar_Util.map_option (fun uu____2836 -> (match (uu____2836) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____2851 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____2872 = (measure_anchored_match needle candidate)
in (match (uu____2872) with
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

let uu____2914 = (locate_match needle tc)
in (FStar_All.pipe_right uu____2914 (FStar_Util.map_option (fun uu____2943 -> (match (uu____2943) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____2969 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____2969)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____2998 -> (match (uu____2998) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____3016)::[] -> begin
true
end
| uu____3017 -> begin
false
end)
in (

let uu____3019 = (FStar_ToSyntax_Env.shorten_module_path dsenv prefix1 naked_match)
in (match (uu____3019) with
| (stripped_ns, shortened) -> begin
(

let uu____3034 = (str_of_ids shortened)
in (

let uu____3035 = (str_of_ids matched)
in (

let uu____3036 = (str_of_ids stripped_ns)
in ((uu____3034), (uu____3035), (uu____3036), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____3047 -> (match (uu____3047) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((prefix1 = "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____3062 -> begin
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

let uu____3129 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____3137 = (

let uu____3139 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____3139 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____3137), (matched_length)))) uu____3129)))
end
| uu____3143 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____3158 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____3194 -> (match (uu____3194) with
| (ns, id, uu____3202) -> begin
(

let uu____3207 = (

let uu____3209 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____3209))
in (match (uu____3207) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3211 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____3211))
end))
end))))))
in (

let uu____3212 = (FStar_Util.prefix needle)
in (match (uu____3212) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____3237 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____3240 = (FStar_ToSyntax_Env.resolve_module_name dsenv l true)
in (match (uu____3240) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____3273 = (shorten_namespace x)
in (prepare_candidate uu____3273))))))
end))))
in (

let json_candidates = (

let uu____3280 = (FStar_Util.sort_with (fun uu____3288 uu____3289 -> (match (((uu____3288), (uu____3289))) with
| ((cd1, ns1, uu____3304), (cd2, ns2, uu____3307)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_40 when (_0_40 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.map (fun uu____3318 -> (match (uu____3318) with
| (candidate, ns, match_len) -> begin
FStar_Util.JsonList ((FStar_Util.JsonInt (match_len))::(FStar_Util.JsonStr (ns))::(FStar_Util.JsonStr (candidate))::[])
end)) uu____3280))
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

let uu___218_3388 = st1
in {repl_line = uu___218_3388.repl_line; repl_column = uu___218_3388.repl_column; repl_fname = uu___218_3388.repl_fname; repl_stack = uu___218_3388.repl_stack; repl_curmod = uu___218_3388.repl_curmod; repl_env = env; repl_ts = uu___218_3388.repl_ts; repl_stdin = uu___218_3388.repl_stdin})
in ((results), (FStar_Util.Inl (st'))))))))
in (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let normalize_term1 = (fun tcenv rules1 t -> (FStar_TypeChecker_Normalize.normalize rules1 tcenv t))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____3420, ({FStar_Syntax_Syntax.lbname = uu____3421; FStar_Syntax_Syntax.lbunivs = uu____3422; FStar_Syntax_Syntax.lbtyp = uu____3423; FStar_Syntax_Syntax.lbeff = uu____3424; FStar_Syntax_Syntax.lbdef = def})::[]), uu____3426, uu____3427); FStar_Syntax_Syntax.sigrng = uu____3428; FStar_Syntax_Syntax.sigquals = uu____3429; FStar_Syntax_Syntax.sigmeta = uu____3430})::[] -> begin
FStar_Pervasives_Native.Some (def)
end
| uu____3449 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____3459 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____3459) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____3472) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____3495 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____3515 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (FStar_Pervasives_Native.snd uu____3515)))
in (

let typecheck = (fun tcenv decls -> (

let uu____3528 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____3528) with
| (ses, uu____3536, uu____3537) -> begin
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

let uu____3550 = st1.repl_env
in (match (uu____3550) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____3558 -> begin
(

let uu____3559 = (parse1 frag)
in (match (uu____3559) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Count not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
try
(match (()) with
| () -> begin
(

let decls1 = (desugar dsenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (def) -> begin
(

let normalized = (normalize_term1 tcenv rules1 def)
in (

let uu____3586 = (

let uu____3587 = (FStar_Syntax_Print.term_to_string normalized)
in FStar_Util.JsonStr (uu____3587))
in ((QueryOK), (uu____3586))))
end)))
end)
with
| e -> begin
(

let uu____3592 = (

let uu____3593 = (FStar_Errors.issue_of_exn e)
in (match (uu____3593) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____3596 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____3596))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise e)
end))
in ((QueryNOK), (uu____3592)))
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
| uu____3617 -> begin
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
| uu____3629 -> begin
false
end))


let __proj__TypeContainsLid__item___0 : search_term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| TypeContainsLid (_0) -> begin
_0
end))


let st_cost : search_term'  ->  Prims.int = (fun uu___205_3647 -> (match (uu___205_3647) with
| NameContainsStr (str) -> begin
(~- ((FStar_String.length str)))
end
| TypeContainsLid (lid) -> begin
(Prims.parse_int "1")
end))

type search_candidate =
{sc_lid : FStar_Ident.lid; sc_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref; sc_fvars : FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option FStar_ST.ref}


let sc_of_lid : FStar_Ident.lid  ->  search_candidate = (fun lid -> (

let uu____3701 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____3706 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____3701; sc_fvars = uu____3706})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____3724 = (FStar_ST.read sc.sc_typ)
in (match (uu____3724) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____3733 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____3733) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____3749, typ), uu____3751) -> begin
typ
end))
in ((FStar_ST.write sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____3771 = (FStar_ST.read sc.sc_fvars)
in (match (uu____3771) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____3785 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____3785))
in ((FStar_ST.write sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____3802 = (sc_typ tcenv sc)
in (FStar_Syntax_Print.term_to_string uu____3802))
in (

let uu____3803 = (

let uu____3807 = (

let uu____3810 = (

let uu____3811 = (

let uu____3812 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____3812.FStar_Ident.str)
in FStar_Util.JsonStr (uu____3811))
in (("lid"), (uu____3810)))
in (uu____3807)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____3803))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____3825) -> begin
true
end
| uu____3826 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____3833) -> begin
uu____3833
end))


let run_search = (fun st search_str -> (

let uu____3852 = st.repl_env
in (match (uu____3852) with
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

let uu____3873 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____3873))
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
| uu____3886 -> begin
term
end)
in (

let beg_quote = (FStar_Util.starts_with term1 "\"")
in (

let end_quote = (FStar_Util.ends_with term1 "\"")
in (

let strip_quotes = (fun str -> (match (((FStar_String.length str) < (Prims.parse_int "2"))) with
| true -> begin
(FStar_Pervasives.raise (InvalidSearch ("Empty search term")))
end
| uu____3896 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((beg_quote <> end_quote)) with
| true -> begin
(

let uu____3901 = (

let uu____3902 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____3902))
in (FStar_Pervasives.raise uu____3901))
end
| uu____3903 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____3904 = (strip_quotes term1)
in NameContainsStr (uu____3904))
end
| uu____3905 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____3907 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____3907) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3909 = (

let uu____3910 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____3910))
in (FStar_Pervasives.raise uu____3909))
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

let uu____3925 = (match (term.st_term) with
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
| uu____3928 -> begin
""
end) uu____3925)))
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

let js = (FStar_Options.with_saved_options (fun uu____3961 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_List.map (json_of_search_result dsenv tcenv) sorted1);
)))
in (match (results) with
| [] -> begin
(

let kwds = (

let uu____3966 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____3966))
in (

let uu____3968 = (

let uu____3969 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____3969))
in (FStar_Pervasives.raise uu____3968)))
end
| uu____3972 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)
with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___206_4001 -> (match (uu___206_4001) with
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

let uu____4039 = (

let uu____4046 = (run_query st)
in (uu____4046 query.qq))
in (match (uu____4039) with
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

let uu____4076 = (

let uu____4078 = (FStar_ST.read issues)
in (e)::uu____4078)
in (FStar_ST.write issues uu____4076)))
in (

let count_errors = (fun uu____4089 -> (

let uu____4090 = (

let uu____4092 = (FStar_ST.read issues)
in (FStar_List.filter (fun e -> (e.FStar_Errors.issue_level = FStar_Errors.EError)) uu____4092))
in (FStar_List.length uu____4090)))
in (

let report1 = (fun uu____4103 -> (

let uu____4104 = (FStar_ST.read issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____4104)))
in (

let clear1 = (fun uu____4112 -> (FStar_ST.write issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (write_message "info"); FStar_Util.printer_prwarning = (write_message "warning"); FStar_Util.printer_prerror = (write_message "error")}


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let uu____4122 = (deps_of_our_file filename)
in (match (uu____4122) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____4136 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____4136) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____4152 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____4153 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____4152 uu____4153)))
in (

let env2 = (

let uu____4157 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env1) initial_range)
in (((FStar_Pervasives_Native.fst env1)), (uu____4157)))
in (

let env3 = (match (maybe_intf) with
| FStar_Pervasives_Native.Some (intf) -> begin
(FStar_Universal.load_interface_decls env2 intf)
end
| FStar_Pervasives_Native.None -> begin
env2
end)
in (

let init_st = (

let uu____4165 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_stack = stack; repl_curmod = FStar_Pervasives_Native.None; repl_env = env3; repl_ts = ts; repl_stdin = uu____4165})
in (

let uu____4166 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____4166) with
| true -> begin
(

let uu____4167 = (

let uu____4168 = (FStar_Options.file_list ())
in (FStar_List.hd uu____4168))
in (FStar_SMTEncoding_Solver.with_hints_db uu____4167 (fun uu____4170 -> (go init_st))))
end
| uu____4171 -> begin
(go init_st)
end))))))
end)))
end));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(FStar_Errors.set_handler interactive_error_handler);
(

let uu____4178 = (

let uu____4179 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____4179))
in (match (uu____4178) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____4181 -> begin
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
(FStar_Pervasives.raise e);
)
end;
))




