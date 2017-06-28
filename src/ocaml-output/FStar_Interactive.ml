
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

type push_kind =
| SyntaxCheck
| LaxCheck
| FullCheck


let uu___is_SyntaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SyntaxCheck -> begin
true
end
| uu____203 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____208 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____213 -> begin
false
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____230 kind restore_cmd_line_options1 msg -> (match (uu____230) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___192_241 = tcenv
in {FStar_TypeChecker_Env.solver = uu___192_241.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___192_241.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___192_241.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___192_241.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___192_241.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___192_241.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___192_241.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___192_241.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___192_241.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___192_241.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___192_241.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___192_241.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___192_241.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___192_241.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___192_241.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___192_241.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___192_241.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___192_241.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (kind = LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___192_241.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___192_241.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___192_241.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___192_241.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___192_241.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___192_241.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___192_241.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___192_241.FStar_TypeChecker_Env.is_native_tactic})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck))
in (

let res = (FStar_Universal.push_context ((dsenv1), (tcenv1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____248 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____248 FStar_Pervasives.ignore))
end
| uu____249 -> begin
()
end);
res;
))))
end))


let mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____257 -> (match (uu____257) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv1), (env1));
)))
end))


let reset_mark = (fun uu____279 -> (match (uu____279) with
| (uu____282, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark ())
in (

let env1 = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env1));
)))
end))


let cleanup = (fun uu____297 -> (match (uu____297) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____309 -> (match (uu____309) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv1), (env1))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____339 curmod frag -> (match (uu____339) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____377 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____377) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____399 = (

let uu____406 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____406)))
in FStar_Pervasives_Native.Some (uu____399))
end
| uu____416 -> begin
FStar_Pervasives_Native.None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____442 = (FStar_Options.trace_error ())
in (not (uu____442))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____455 = (FStar_Options.trace_error ())
in (not (uu____455))) -> begin
((

let uu____457 = (

let uu____461 = (

let uu____464 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____464)))
in (uu____461)::[])
in (FStar_TypeChecker_Err.add_errors env uu____457));
FStar_Pervasives_Native.None;
)
end
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____485 = (FStar_List.partition (fun x -> (

let uu____494 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____495 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____494 <> uu____495)))) deps)
in (match (uu____485) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____512 = ((

let uu____515 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____515))) || (

let uu____517 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____517))))
in (match (uu____512) with
| true -> begin
(

let uu____518 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____518))
end
| uu____519 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____521 -> begin
((

let uu____524 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____524));
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
| uu____562 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____573 = (

let uu____574 = (FStar_Options.lax ())
in (match (uu____574) with
| true -> begin
LaxCheck
end
| uu____575 -> begin
FullCheck
end))
in (push env uu____573 true "typecheck_modul"))
in (

let uu____576 = (tc_one_file remaining env1)
in (match (uu____576) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____604 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____612 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____612))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____604) with
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
| (uu____686, uu____687) -> begin
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
| uu____749 -> begin
((false), (depnames1))
end)
end
| uu____751 -> begin
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
| uu____766 -> begin
((false), (depnames1))
end)
end
| uu____768 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____815)::ts3 -> begin
((pop env1 "");
(

let uu____837 = (

let uu____845 = (FStar_List.hd stack)
in (

let uu____850 = (FStar_List.tl stack)
in ((uu____845), (uu____850))))
in (match (uu____837) with
| ((env2, uu____864), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____898 = ts_elt
in (match (uu____898) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____916 = (match_dep depnames intf impl)
in (match (uu____916) with
| (b, depnames') -> begin
(

let uu____927 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____927) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____938 -> begin
(

let uu____939 = (

let uu____947 = (FStar_List.hd st)
in (

let uu____952 = (FStar_List.tl st)
in ((uu____947), (uu____952))))
in (match (uu____939) with
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

let uu____992 = (deps_of_our_file filename)
in (match (uu____992) with
| (filenames, uu____1001) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___182_1033 -> (match (uu___182_1033) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____1035 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____1037 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____1037))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____1039) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____1041) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1054) -> begin
true
end
| uu____1057 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1069) -> begin
uu____1069
end))


let js_fail = (fun expected got -> (FStar_Pervasives.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___183_1090 -> (match (uu___183_1090) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___184_1096 -> (match (uu___184_1096) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list = (fun k uu___185_1117 -> (match (uu___185_1117) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___186_1130 -> (match (uu___186_1130) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1146 = (js_str s)
in (match (uu____1146) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1147 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1152 = (js_str s)
in (match (uu____1152) with
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
| uu____1153 -> begin
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
| uu____1207 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1212 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1217 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1222 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1233 -> begin
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
| uu____1262 -> begin
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
| uu____1284 -> begin
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
| uu____1326 -> begin
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
| uu____1352 -> begin
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
| uu____1366 -> begin
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


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "1")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("compute")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/documentation")::("lookup/definition")::("pop")::("peek")::("push")::("search")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____1395) -> begin
true
end
| uu____1396 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____1404) -> begin
uu____1404
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____1409 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____1414 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____1419 -> begin
false
end))


let try_assoc = (fun key a -> (

let uu____1445 = (FStar_Util.try_find (fun uu____1454 -> (match (uu____1454) with
| (k, uu____1458) -> begin
(k = key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____1445)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____1473 = (

let uu____1474 = (

let uu____1475 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____1475))
in ProtocolViolation (uu____1474))
in {qq = uu____1473; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____1496 = (try_assoc key a)
in (match (uu____1496) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1499 = (

let uu____1500 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____1500))
in (FStar_Pervasives.raise uu____1499))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____1509 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____1509 js_str))
in try
(match (()) with
| () -> begin
(

let query = (

let uu____1518 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____1518 js_str))
in (

let args = (

let uu____1523 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____1523 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____1536 = (try_assoc k args)
in (match (uu____1536) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____1541 = (match (query) with
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

let uu____1542 = (

let uu____1548 = (

let uu____1549 = (arg "kind")
in (FStar_All.pipe_right uu____1549 js_pushkind))
in (

let uu____1550 = (

let uu____1551 = (arg "code")
in (FStar_All.pipe_right uu____1551 js_str))
in (

let uu____1552 = (

let uu____1553 = (arg "line")
in (FStar_All.pipe_right uu____1553 js_int))
in (

let uu____1554 = (

let uu____1555 = (arg "column")
in (FStar_All.pipe_right uu____1555 js_int))
in ((uu____1548), (uu____1550), (uu____1552), (uu____1554), ((query = "peek")))))))
in Push (uu____1542))
end
| "push" -> begin
(

let uu____1556 = (

let uu____1562 = (

let uu____1563 = (arg "kind")
in (FStar_All.pipe_right uu____1563 js_pushkind))
in (

let uu____1564 = (

let uu____1565 = (arg "code")
in (FStar_All.pipe_right uu____1565 js_str))
in (

let uu____1566 = (

let uu____1567 = (arg "line")
in (FStar_All.pipe_right uu____1567 js_int))
in (

let uu____1568 = (

let uu____1569 = (arg "column")
in (FStar_All.pipe_right uu____1569 js_int))
in ((uu____1562), (uu____1564), (uu____1566), (uu____1568), ((query = "peek")))))))
in Push (uu____1556))
end
| "autocomplete" -> begin
(

let uu____1570 = (

let uu____1571 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____1571 js_str))
in AutoComplete (uu____1570))
end
| "lookup" -> begin
(

let uu____1572 = (

let uu____1581 = (

let uu____1582 = (arg "symbol")
in (FStar_All.pipe_right uu____1582 js_str))
in (

let uu____1583 = (

let uu____1588 = (

let uu____1593 = (try_arg "location")
in (FStar_All.pipe_right uu____1593 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____1588 (FStar_Util.map_option (fun loc -> (

let uu____1625 = (

let uu____1626 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____1626 js_str))
in (

let uu____1627 = (

let uu____1628 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____1628 js_int))
in (

let uu____1629 = (

let uu____1630 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____1630 js_int))
in ((uu____1625), (uu____1627), (uu____1629)))))))))
in (

let uu____1631 = (

let uu____1633 = (arg "requested-info")
in (FStar_All.pipe_right uu____1633 (js_list js_str)))
in ((uu____1581), (uu____1583), (uu____1631)))))
in Lookup (uu____1572))
end
| "compute" -> begin
(

let uu____1640 = (

let uu____1645 = (

let uu____1646 = (arg "term")
in (FStar_All.pipe_right uu____1646 js_str))
in (

let uu____1647 = (

let uu____1650 = (try_arg "rules")
in (FStar_All.pipe_right uu____1650 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____1645), (uu____1647))))
in Compute (uu____1640))
end
| "search" -> begin
(

let uu____1658 = (

let uu____1659 = (arg "terms")
in (FStar_All.pipe_right uu____1659 js_str))
in Search (uu____1658))
end
| uu____1660 -> begin
(

let uu____1661 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____1661))
end)
in {qq = uu____1541; qid = qid})))))
end)
with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end))))


let validate_interactive_query : query  ->  query = (fun uu___187_1671 -> (match (uu___187_1671) with
| {qq = Push (SyntaxCheck, uu____1672, uu____1673, uu____1674, false); qid = qid} -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = qid}
end
| other -> begin
other
end))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> try
(match (()) with
| () -> begin
(

let uu____1684 = (FStar_Util.read_line stream)
in (match (uu____1684) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____1687 = (FStar_Util.json_of_string line)
in (match (uu____1687) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(

let uu____1690 = (unpack_interactive_query request)
in (validate_interactive_query uu____1690))
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


let rec json_of_fstar_option : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___188_1700 -> (match (uu___188_1700) with
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

let uu____1707 = (FStar_List.map json_of_fstar_option vs)
in FStar_Util.JsonList (uu____1707))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let json_of_opt = (fun json_of_a opt_a -> (

let uu____1731 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____1731)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____1737 = (

let uu____1739 = (

let uu____1740 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____1740))
in (

let uu____1741 = (

let uu____1743 = (

let uu____1744 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____1744))
in (uu____1743)::[])
in (uu____1739)::uu____1741))
in FStar_Util.JsonList (uu____1737)))


let json_of_range_fields : Prims.string  ->  FStar_Range.pos  ->  FStar_Range.pos  ->  FStar_Util.json = (fun file b e -> (

let uu____1757 = (

let uu____1761 = (

let uu____1765 = (

let uu____1768 = (json_of_pos b)
in (("beg"), (uu____1768)))
in (

let uu____1769 = (

let uu____1773 = (

let uu____1776 = (json_of_pos e)
in (("end"), (uu____1776)))
in (uu____1773)::[])
in (uu____1765)::uu____1769))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____1761)
in FStar_Util.JsonAssoc (uu____1757)))


let json_of_use_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____1789 = (FStar_Range.file_of_use_range r)
in (

let uu____1790 = (FStar_Range.start_of_use_range r)
in (

let uu____1791 = (FStar_Range.end_of_use_range r)
in (json_of_range_fields uu____1789 uu____1790 uu____1791)))))


let json_of_def_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____1796 = (FStar_Range.file_of_range r)
in (

let uu____1797 = (FStar_Range.start_of_range r)
in (

let uu____1798 = (FStar_Range.end_of_range r)
in (json_of_range_fields uu____1796 uu____1797 uu____1798)))))


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

let uu____1807 = (

let uu____1811 = (

let uu____1815 = (

let uu____1819 = (

let uu____1822 = (

let uu____1823 = (

let uu____1825 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____1829 = (json_of_use_range r)
in (uu____1829)::[])
end)
in (

let uu____1830 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (r.FStar_Range.def_range <> r.FStar_Range.use_range) -> begin
(

let uu____1834 = (json_of_def_range r)
in (uu____1834)::[])
end
| uu____1835 -> begin
[]
end)
in (FStar_List.append uu____1825 uu____1830)))
in FStar_Util.JsonList (uu____1823))
in (("ranges"), (uu____1822)))
in (uu____1819)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____1815)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____1811)
in FStar_Util.JsonAssoc (uu____1807)))

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

let uu____1946 = (

let uu____1950 = (

let uu____1954 = (

let uu____1957 = (json_of_opt json_of_def_range lr.lr_def_range)
in (("defined-at"), (uu____1957)))
in (

let uu____1958 = (

let uu____1962 = (

let uu____1965 = (json_of_opt (fun _0_40 -> FStar_Util.JsonStr (_0_40)) lr.lr_typ)
in (("type"), (uu____1965)))
in (

let uu____1966 = (

let uu____1970 = (

let uu____1973 = (json_of_opt (fun _0_41 -> FStar_Util.JsonStr (_0_41)) lr.lr_doc)
in (("documentation"), (uu____1973)))
in (

let uu____1974 = (

let uu____1978 = (

let uu____1981 = (json_of_opt (fun _0_42 -> FStar_Util.JsonStr (_0_42)) lr.lr_def)
in (("definition"), (uu____1981)))
in (uu____1978)::[])
in (uu____1970)::uu____1974))
in (uu____1962)::uu____1966))
in (uu____1954)::uu____1958))
in ((("name"), (FStar_Util.JsonStr (lr.lr_name))))::uu____1950)
in FStar_Util.JsonAssoc (uu____1946)))


let json_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____1999 = (FStar_List.map (fun _0_43 -> FStar_Util.JsonStr (_0_43)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_44 -> FStar_Util.JsonList (_0_44)) uu____1999))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____2013 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____2013));
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


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____2057 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____2060 = (FStar_List.map (fun _0_45 -> FStar_Util.JsonStr (_0_45)) interactive_protocol_features)
in FStar_Util.JsonList (uu____2060))
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

let uu____2208 = (FStar_Options.docs ())
in (FStar_Util.smap_of_list uu____2208))
in (

let get_doc = (fun k -> (FStar_Util.smap_try_find opt_docs k))
in (FStar_List.map (fun uu____2229 -> (match (uu____2229) with
| (k, v1) -> begin
(

let uu____2239 = (FStar_Options.get_option k)
in (

let uu____2240 = (get_doc k)
in ((k), (uu____2239), (uu____2240), (v1))))
end)) FStar_Options.defaults)))
in (

let uu____2243 = (

let uu____2246 = (

let uu____2247 = (FStar_List.map (fun uu____2260 -> (match (uu____2260) with
| (uu____2267, fstname, uu____2269, uu____2270) -> begin
FStar_Util.JsonStr (fstname)
end)) st.repl_ts)
in FStar_Util.JsonList (uu____2247))
in (("loaded-dependencies"), (uu____2246)))
in (

let uu____2275 = (

let uu____2279 = (

let uu____2282 = (

let uu____2283 = (FStar_List.map (fun uu____2296 -> (match (uu____2296) with
| (name, value, doc1, dflt1) -> begin
(

let uu____2308 = (

let uu____2312 = (

let uu____2316 = (

let uu____2319 = (json_of_fstar_option value)
in (("value"), (uu____2319)))
in (

let uu____2320 = (

let uu____2324 = (

let uu____2327 = (json_of_fstar_option dflt1)
in (("default"), (uu____2327)))
in (

let uu____2328 = (

let uu____2332 = (

let uu____2335 = (json_of_opt (fun _0_46 -> FStar_Util.JsonStr (_0_46)) doc1)
in (("documentation"), (uu____2335)))
in (uu____2332)::[])
in (uu____2324)::uu____2328))
in (uu____2316)::uu____2320))
in ((("name"), (FStar_Util.JsonStr (name))))::uu____2312)
in FStar_Util.JsonAssoc (uu____2308))
end)) opts_and_defaults)
in FStar_Util.JsonList (uu____2283))
in (("options"), (uu____2282)))
in (uu____2279)::[])
in (uu____2243)::uu____2275))))


let run_exit = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (json_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl = (fun st -> (

let uu____2411 = (

let uu____2414 = (

let uu____2415 = (json_of_repl_state st)
in FStar_Util.JsonAssoc (uu____2415))
in ((QueryOK), (uu____2414)))
in ((uu____2411), (FStar_Util.Inl (st)))))


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
| uu____2498 -> begin
()
end);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl ((

let uu___199_2504 = st
in {repl_line = uu___199_2504.repl_line; repl_column = uu___199_2504.repl_column; repl_fname = uu___199_2504.repl_fname; repl_stack = stack; repl_curmod = curmod; repl_env = env; repl_ts = uu___199_2504.repl_ts; repl_stdin = uu___199_2504.repl_stdin}))));
)
end))


let run_push = (fun st kind text1 line column1 peek_only -> (

let uu____2550 = ((st.repl_stack), (st.repl_env), (st.repl_ts))
in (match (uu____2550) with
| (stack, env, ts) -> begin
(

let uu____2563 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(

let uu____2590 = (update_deps st.repl_fname st.repl_curmod stack env ts)
in ((true), (uu____2590)))
end
| uu____2597 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____2563) with
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

let uu____2637 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____2637 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___200_2643 = st
in {repl_line = line; repl_column = column1; repl_fname = uu___200_2643.repl_fname; repl_stack = stack2; repl_curmod = uu___200_2643.repl_curmod; repl_env = uu___200_2643.repl_env; repl_ts = ts1; repl_stdin = uu___200_2643.repl_stdin})
in (match (res) with
| FStar_Pervasives_Native.Some (curmod, env3, nerrs) when ((nerrs = (Prims.parse_int "0")) && (peek_only = false)) -> begin
(

let env4 = (commit_mark env3)
in ((((QueryOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl ((

let uu___201_2673 = st'
in {repl_line = uu___201_2673.repl_line; repl_column = uu___201_2673.repl_column; repl_fname = uu___201_2673.repl_fname; repl_stack = uu___201_2673.repl_stack; repl_curmod = curmod; repl_env = env4; repl_ts = uu___201_2673.repl_ts; repl_stdin = uu___201_2673.repl_stdin})))))
end
| uu____2674 -> begin
(

let env3 = (reset_mark env_mark)
in (

let uu____2685 = (run_pop (

let uu___202_2693 = st'
in {repl_line = uu___202_2693.repl_line; repl_column = uu___202_2693.repl_column; repl_fname = uu___202_2693.repl_fname; repl_stack = uu___202_2693.repl_stack; repl_curmod = uu___202_2693.repl_curmod; repl_env = env3; repl_ts = uu___202_2693.repl_ts; repl_stdin = uu___202_2693.repl_stdin}))
in (match (uu____2685) with
| (uu____2700, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____2711 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end)))
end));
)))))))
end))
end)))


let run_lookup = (fun st symbol pos_opt requested_info -> (

let uu____2759 = st.repl_env
in (match (uu____2759) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____2779 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____2779))
in (

let lid1 = (

let uu____2782 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____2782))
in (

let uu____2785 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____2785 (FStar_Util.map_option (fun uu____2815 -> (match (uu____2815) with
| ((uu____2825, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____2837 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____2837 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____2854 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____2854 (fun uu___189_2879 -> (match (uu___189_2879) with
| (FStar_Util.Inr (se, uu____2891), uu____2892) -> begin
(

let uu____2907 = (FStar_Syntax_Print.sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____2907))
end
| uu____2908 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____2937 -> (match (uu____2937) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____2963) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((symbol = "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____2990 -> begin
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

let uu____3019 = (FStar_TypeChecker_Normalize.term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____3019))
end
| uu____3020 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____3025 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____3032 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____3038 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {lr_name = name; lr_def_range = def_range; lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str}
in (

let uu____3040 = (json_of_lookup_result result)
in ((QueryOK), (uu____3040)))))))))
end)
in ((response), (FStar_Util.Inl (st)))))))))
end)))


let run_completions = (fun st search_term -> (

let uu____3066 = st.repl_env
in (match (uu____3066) with
| (dsenv, tcenv) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____3096) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____3104, []) -> begin
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
| uu____3136 -> begin
(

let uu____3138 = (measure_anchored_match ts tc)
in (FStar_All.pipe_right uu____3138 (FStar_Util.map_option (fun uu____3160 -> (match (uu____3160) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____3178 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____3199 = (measure_anchored_match needle candidate)
in (match (uu____3199) with
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

let uu____3241 = (locate_match needle tc)
in (FStar_All.pipe_right uu____3241 (FStar_Util.map_option (fun uu____3274 -> (match (uu____3274) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____3300 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____3300)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____3329 -> (match (uu____3329) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____3347)::[] -> begin
true
end
| uu____3348 -> begin
false
end)
in (

let uu____3350 = (FStar_ToSyntax_Env.shorten_module_path dsenv prefix1 naked_match)
in (match (uu____3350) with
| (stripped_ns, shortened) -> begin
(

let uu____3365 = (str_of_ids shortened)
in (

let uu____3366 = (str_of_ids matched)
in (

let uu____3367 = (str_of_ids stripped_ns)
in ((uu____3365), (uu____3366), (uu____3367), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____3378 -> (match (uu____3378) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((prefix1 = "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____3393 -> begin
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

let uu____3473 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____3483 = (

let uu____3485 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____3485 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____3483), (matched_length)))) uu____3473)))
end
| uu____3489 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____3504 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____3545 -> (match (uu____3545) with
| (ns, id, uu____3553) -> begin
(

let uu____3558 = (

let uu____3560 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____3560))
in (match (uu____3558) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____3562 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____3562))
end))
end))))))
in (

let uu____3563 = (FStar_Util.prefix needle)
in (match (uu____3563) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____3588 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____3591 = (FStar_ToSyntax_Env.resolve_module_name dsenv l true)
in (match (uu____3591) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____3626 = (shorten_namespace x)
in (prepare_candidate uu____3626))))))
end))))
in (

let json_candidates = (

let uu____3633 = (FStar_Util.sort_with (fun uu____3649 uu____3650 -> (match (((uu____3649), (uu____3650))) with
| ((cd1, ns1, uu____3665), (cd2, ns2, uu____3668)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_47 when (_0_47 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.map (fun uu____3683 -> (match (uu____3683) with
| (candidate, ns, match_len) -> begin
FStar_Util.JsonList ((FStar_Util.JsonInt (match_len))::(FStar_Util.JsonStr (ns))::(FStar_Util.JsonStr (candidate))::[])
end)) uu____3633))
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

let uu___203_3757 = st1
in {repl_line = uu___203_3757.repl_line; repl_column = uu___203_3757.repl_column; repl_fname = uu___203_3757.repl_fname; repl_stack = uu___203_3757.repl_stack; repl_curmod = uu___203_3757.repl_curmod; repl_env = env; repl_ts = uu___203_3757.repl_ts; repl_stdin = uu___203_3757.repl_stdin})
in ((results), (FStar_Util.Inl (st'))))))))
in (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let normalize_term1 = (fun tcenv rules1 t -> (FStar_TypeChecker_Normalize.normalize rules1 tcenv t))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____3789, ({FStar_Syntax_Syntax.lbname = uu____3790; FStar_Syntax_Syntax.lbunivs = uu____3791; FStar_Syntax_Syntax.lbtyp = uu____3792; FStar_Syntax_Syntax.lbeff = uu____3793; FStar_Syntax_Syntax.lbdef = def})::[]), uu____3795, uu____3796); FStar_Syntax_Syntax.sigrng = uu____3797; FStar_Syntax_Syntax.sigquals = uu____3798; FStar_Syntax_Syntax.sigmeta = uu____3799})::[] -> begin
FStar_Pervasives_Native.Some (def)
end
| uu____3818 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____3828 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____3828) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____3841) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____3864 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____3884 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (FStar_Pervasives_Native.snd uu____3884)))
in (

let typecheck = (fun tcenv decls -> (

let uu____3897 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____3897) with
| (ses, uu____3905, uu____3906) -> begin
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

let uu____3925 = st1.repl_env
in (match (uu____3925) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____3933 -> begin
(

let uu____3934 = (parse1 frag)
in (match (uu____3934) with
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

let uu____3964 = (

let uu____3965 = (FStar_Syntax_Print.term_to_string normalized)
in FStar_Util.JsonStr (uu____3965))
in ((QueryOK), (uu____3964))))
end)))
end)
with
| e -> begin
(

let uu____3973 = (

let uu____3974 = (FStar_Errors.issue_of_exn e)
in (match (uu____3974) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____3977 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____3977))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise e)
end))
in ((QueryNOK), (uu____3973)))
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
| uu____3999 -> begin
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
| uu____4013 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___190_4037 -> (match (uu___190_4037) with
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

let uu____4121 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____4126 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____4121; sc_fvars = uu____4126})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____4146 = (FStar_ST.read sc.sc_typ)
in (match (uu____4146) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____4155 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____4155) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____4171, typ), uu____4173) -> begin
typ
end))
in ((FStar_ST.write sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____4195 = (FStar_ST.read sc.sc_fvars)
in (match (uu____4195) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____4209 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____4209))
in ((FStar_ST.write sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____4229 = (sc_typ tcenv sc)
in (FStar_Syntax_Print.term_to_string uu____4229))
in (

let uu____4230 = (

let uu____4234 = (

let uu____4237 = (

let uu____4238 = (

let uu____4239 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____4239.FStar_Ident.str)
in FStar_Util.JsonStr (uu____4238))
in (("lid"), (uu____4237)))
in (uu____4234)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____4230))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____4253) -> begin
true
end
| uu____4254 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____4262) -> begin
uu____4262
end))


let run_search = (fun st search_str -> (

let uu____4284 = st.repl_env
in (match (uu____4284) with
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

let uu____4305 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____4305))
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
| uu____4318 -> begin
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
| uu____4331 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((beg_quote <> end_quote)) with
| true -> begin
(

let uu____4339 = (

let uu____4340 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____4340))
in (FStar_Pervasives.raise uu____4339))
end
| uu____4341 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____4342 = (strip_quotes term1)
in NameContainsStr (uu____4342))
end
| uu____4343 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____4345 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____4345) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4347 = (

let uu____4348 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____4348))
in (FStar_Pervasives.raise uu____4347))
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

let uu____4363 = (match (term.st_term) with
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
| uu____4366 -> begin
""
end) uu____4363)))
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

let js = (FStar_Options.with_saved_options (fun uu____4412 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_List.map (json_of_search_result dsenv tcenv) sorted1);
)))
in (match (results) with
| [] -> begin
(

let kwds = (

let uu____4417 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____4417))
in (

let uu____4419 = (

let uu____4420 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____4420))
in (FStar_Pervasives.raise uu____4419)))
end
| uu____4423 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)
with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___191_4455 -> (match (uu___191_4455) with
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
| ProtocolViolation (query) -> begin
(run_protocol_violation st query)
end))


let rec go : repl_state  ->  Prims.unit = (fun st -> (

let query = (read_interactive_query st.repl_stdin)
in (

let uu____4494 = (

let uu____4501 = (run_query st)
in (uu____4501 query.qq))
in (match (uu____4494) with
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

let uu____4531 = (

let uu____4533 = (FStar_ST.read issues)
in (e)::uu____4533)
in (FStar_ST.write issues uu____4531)))
in (

let count_errors = (fun uu____4544 -> (

let uu____4545 = (

let uu____4547 = (FStar_ST.read issues)
in (FStar_List.filter (fun e -> (e.FStar_Errors.issue_level = FStar_Errors.EError)) uu____4547))
in (FStar_List.length uu____4545)))
in (

let report1 = (fun uu____4560 -> (

let uu____4561 = (FStar_ST.read issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____4561)))
in (

let clear1 = (fun uu____4569 -> (FStar_ST.write issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (write_message "info"); FStar_Util.printer_prwarning = (write_message "warning"); FStar_Util.printer_prerror = (write_message "error")}


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let uu____4582 = (deps_of_our_file filename)
in (match (uu____4582) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____4596 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____4596) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____4612 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____4613 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____4612 uu____4613)))
in (

let env2 = (

let uu____4617 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env1) initial_range)
in (((FStar_Pervasives_Native.fst env1)), (uu____4617)))
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

let uu____4625 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_stack = stack; repl_curmod = FStar_Pervasives_Native.None; repl_env = env3; repl_ts = ts; repl_stdin = uu____4625})
in (

let uu____4626 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____4626) with
| true -> begin
(

let uu____4627 = (

let uu____4628 = (FStar_Options.file_list ())
in (FStar_List.hd uu____4628))
in (FStar_SMTEncoding_Solver.with_hints_db uu____4627 (fun uu____4631 -> (go init_st))))
end
| uu____4632 -> begin
(go init_st)
end))))))
end)))
end));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(FStar_Errors.set_handler interactive_error_handler);
(

let uu____4640 = (

let uu____4641 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____4641))
in (match (uu____4640) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____4643 -> begin
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




