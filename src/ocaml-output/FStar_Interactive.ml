
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
| (uu____119, dsenv1, env1) -> begin
((((FStar_Pervasives_Native.Some (intf)), (impl))), (dsenv1), (env1), (remaining1))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____148 = (FStar_Universal.tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____148) with
| (uu____177, dsenv1, env1) -> begin
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


let tc_prims : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____276 -> (

let uu____277 = (FStar_Universal.tc_prims ())
in (match (uu____277) with
| (uu____292, dsenv, env) -> begin
((dsenv), (env))
end)))


type env_t =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


type stack_t =
(env_t * modul_t) Prims.list


let pop : 'Auu____321 . ('Auu____321 * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____332 msg -> (match (uu____332) with
| (uu____338, env) -> begin
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
| uu____345 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____350 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____355 -> begin
false
end))


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  Prims.bool  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____376 kind restore_cmd_line_options1 msg -> (match (uu____376) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___195_391 = tcenv
in {FStar_TypeChecker_Env.solver = uu___195_391.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___195_391.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___195_391.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___195_391.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___195_391.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___195_391.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___195_391.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___195_391.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___195_391.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___195_391.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___195_391.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___195_391.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___195_391.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___195_391.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___195_391.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___195_391.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___195_391.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___195_391.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (kind = LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___195_391.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___195_391.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___195_391.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___195_391.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___195_391.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___195_391.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___195_391.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___195_391.FStar_TypeChecker_Env.is_native_tactic})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (kind = SyntaxCheck))
in (

let res = (FStar_Universal.push_context ((dsenv1), (tcenv1)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options1) with
| true -> begin
(

let uu____400 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____400 FStar_Pervasives.ignore))
end
| uu____401 -> begin
()
end);
res;
))))
end))


let mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____413 -> (match (uu____413) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv1), (env1));
)))
end))


let reset_mark : 'Auu____431 . ('Auu____431 * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____443 -> (match (uu____443) with
| (uu____448, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark ())
in (

let env1 = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env1));
)))
end))


let cleanup : 'Auu____457 . ('Auu____457 * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____465 -> (match (uu____465) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let commit_mark : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____483 -> (match (uu____483) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env1 = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv1), (env1))))
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____529 curmod frag -> (match (uu____529) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____593 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____593) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____633 = (

let uu____646 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____646)))
in FStar_Pervasives_Native.Some (uu____633))
end
| uu____665 -> begin
FStar_Pervasives_Native.None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____709 = (FStar_Options.trace_error ())
in (not (uu____709))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____732 = (FStar_Options.trace_error ())
in (not (uu____732))) -> begin
((

let uu____734 = (

let uu____741 = (

let uu____746 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____746)))
in (uu____741)::[])
in (FStar_TypeChecker_Err.add_errors env uu____734));
FStar_Pervasives_Native.None;
)
end
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____782 = (FStar_List.partition (fun x -> (

let uu____795 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____796 = (FStar_Parser_Dep.lowercase_module_name filename)
in (uu____795 <> uu____796)))) deps)
in (match (uu____782) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____823 = ((

let uu____826 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____826))) || (

let uu____828 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____828))))
in (match (uu____823) with
| true -> begin
(

let uu____829 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____829))
end
| uu____830 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____832 -> begin
((

let uu____836 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____836));
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
| uu____891 -> begin
(

let stack1 = (((env), (m)))::stack
in (

let env1 = (

let uu____910 = (

let uu____911 = (FStar_Options.lax ())
in (match (uu____911) with
| true -> begin
LaxCheck
end
| uu____912 -> begin
FullCheck
end))
in (push env uu____910 true "typecheck_modul"))
in (

let uu____913 = (tc_one_file remaining env1)
in (match (uu____913) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____964 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____977 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____977))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____964) with
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
| (uu____1081, uu____1082) -> begin
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
| uu____1174 -> begin
((false), (depnames1))
end)
end
| uu____1177 -> begin
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
| uu____1202 -> begin
((false), (depnames1))
end)
end
| uu____1205 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____1288)::ts3 -> begin
((pop env1 "");
(

let uu____1329 = (

let uu____1344 = (FStar_List.hd stack)
in (

let uu____1353 = (FStar_List.tl stack)
in ((uu____1344), (uu____1353))))
in (match (uu____1329) with
| ((env2, uu____1379), stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____1443 = ts_elt
in (match (uu____1443) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1474 = (match_dep depnames intf impl)
in (match (uu____1474) with
| (b, depnames') -> begin
(

let uu____1493 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1493) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps m good_stack env1 depnames good_ts))
end
| uu____1513 -> begin
(

let uu____1514 = (

let uu____1529 = (FStar_List.hd st)
in (

let uu____1538 = (FStar_List.tl st)
in ((uu____1529), (uu____1538))))
in (match (uu____1514) with
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

let uu____1615 = (deps_of_our_file filename)
in (match (uu____1615) with
| (filenames, uu____1631) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___185_1691 -> (match (uu___185_1691) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____1693 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____1695 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____1695))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____1697) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____1700) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1718) -> begin
true
end
| uu____1723 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1739) -> begin
uu____1739
end))


let js_fail : 'Auu____1750 . Prims.string  ->  FStar_Util.json  ->  'Auu____1750 = (fun expected got -> (FStar_Pervasives.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___186_1762 -> (match (uu___186_1762) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___187_1768 -> (match (uu___187_1768) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____1777 . (FStar_Util.json  ->  'Auu____1777)  ->  FStar_Util.json  ->  'Auu____1777 Prims.list = (fun k uu___188_1790 -> (match (uu___188_1790) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___189_1808 -> (match (uu___189_1808) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1833 = (js_str s)
in (match (uu____1833) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1834 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1839 = (js_str s)
in (match (uu____1839) with
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
| uu____1840 -> begin
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
| uu____1911 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1916 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1921 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1926 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1942 -> begin
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
| uu____1986 -> begin
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
| uu____2016 -> begin
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
| uu____2086 -> begin
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
| uu____2124 -> begin
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
| uu____2138 -> begin
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
| InvalidQuery (uu____2168) -> begin
true
end
| uu____2169 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2177) -> begin
uu____2177
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____2182 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____2187 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____2192 -> begin
false
end))


let try_assoc : 'Auu____2201 'Auu____2202 . 'Auu____2202  ->  ('Auu____2202 * 'Auu____2201) Prims.list  ->  'Auu____2201 FStar_Pervasives_Native.option = (fun key a -> (

let uu____2225 = (FStar_Util.try_find (fun uu____2239 -> (match (uu____2239) with
| (k, uu____2245) -> begin
(k = key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____2225)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____2262 = (

let uu____2263 = (

let uu____2264 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____2264))
in ProtocolViolation (uu____2263))
in {qq = uu____2262; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____2291 = (try_assoc key a)
in (match (uu____2291) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2295 = (

let uu____2296 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____2296))
in (FStar_Pervasives.raise uu____2295))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____2311 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____2311 js_str))
in try
(match (()) with
| () -> begin
(

let query = (

let uu____2320 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____2320 js_str))
in (

let args = (

let uu____2328 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____2328 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____2345 = (try_assoc k args)
in (match (uu____2345) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____2353 = (match (query) with
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

let uu____2354 = (

let uu____2365 = (

let uu____2366 = (arg "kind")
in (FStar_All.pipe_right uu____2366 js_pushkind))
in (

let uu____2367 = (

let uu____2368 = (arg "code")
in (FStar_All.pipe_right uu____2368 js_str))
in (

let uu____2369 = (

let uu____2370 = (arg "line")
in (FStar_All.pipe_right uu____2370 js_int))
in (

let uu____2371 = (

let uu____2372 = (arg "column")
in (FStar_All.pipe_right uu____2372 js_int))
in ((uu____2365), (uu____2367), (uu____2369), (uu____2371), ((query = "peek")))))))
in Push (uu____2354))
end
| "push" -> begin
(

let uu____2373 = (

let uu____2384 = (

let uu____2385 = (arg "kind")
in (FStar_All.pipe_right uu____2385 js_pushkind))
in (

let uu____2386 = (

let uu____2387 = (arg "code")
in (FStar_All.pipe_right uu____2387 js_str))
in (

let uu____2388 = (

let uu____2389 = (arg "line")
in (FStar_All.pipe_right uu____2389 js_int))
in (

let uu____2390 = (

let uu____2391 = (arg "column")
in (FStar_All.pipe_right uu____2391 js_int))
in ((uu____2384), (uu____2386), (uu____2388), (uu____2390), ((query = "peek")))))))
in Push (uu____2373))
end
| "autocomplete" -> begin
(

let uu____2392 = (

let uu____2393 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____2393 js_str))
in AutoComplete (uu____2392))
end
| "lookup" -> begin
(

let uu____2394 = (

let uu____2411 = (

let uu____2412 = (arg "symbol")
in (FStar_All.pipe_right uu____2412 js_str))
in (

let uu____2413 = (

let uu____2422 = (

let uu____2431 = (try_arg "location")
in (FStar_All.pipe_right uu____2431 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____2422 (FStar_Util.map_option (fun loc -> (

let uu____2489 = (

let uu____2490 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____2490 js_str))
in (

let uu____2491 = (

let uu____2492 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____2492 js_int))
in (

let uu____2493 = (

let uu____2494 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____2494 js_int))
in ((uu____2489), (uu____2491), (uu____2493)))))))))
in (

let uu____2495 = (

let uu____2498 = (arg "requested-info")
in (FStar_All.pipe_right uu____2498 (js_list js_str)))
in ((uu____2411), (uu____2413), (uu____2495)))))
in Lookup (uu____2394))
end
| "compute" -> begin
(

let uu____2511 = (

let uu____2520 = (

let uu____2521 = (arg "term")
in (FStar_All.pipe_right uu____2521 js_str))
in (

let uu____2522 = (

let uu____2527 = (try_arg "rules")
in (FStar_All.pipe_right uu____2527 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____2520), (uu____2522))))
in Compute (uu____2511))
end
| "search" -> begin
(

let uu____2542 = (

let uu____2543 = (arg "terms")
in (FStar_All.pipe_right uu____2543 js_str))
in Search (uu____2542))
end
| uu____2544 -> begin
(

let uu____2545 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____2545))
end)
in {qq = uu____2353; qid = qid})))))
end)
with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end))))


let validate_interactive_query : query  ->  query = (fun uu___190_2555 -> (match (uu___190_2555) with
| {qq = Push (SyntaxCheck, uu____2556, uu____2557, uu____2558, false); qid = qid} -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = qid}
end
| other -> begin
other
end))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> try
(match (()) with
| () -> begin
(

let uu____2568 = (FStar_Util.read_line stream)
in (match (uu____2568) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____2572 = (FStar_Util.json_of_string line)
in (match (uu____2572) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(

let uu____2576 = (unpack_interactive_query request)
in (validate_interactive_query uu____2576))
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


let rec json_of_fstar_option : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___191_2586 -> (match (uu___191_2586) with
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

let uu____2594 = (FStar_List.map json_of_fstar_option vs)
in FStar_Util.JsonList (uu____2594))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let json_of_opt : 'Auu____2603 . ('Auu____2603  ->  FStar_Util.json)  ->  'Auu____2603 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____2621 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____2621)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____2628 = (

let uu____2631 = (

let uu____2632 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____2632))
in (

let uu____2633 = (

let uu____2636 = (

let uu____2637 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____2637))
in (uu____2636)::[])
in (uu____2631)::uu____2633))
in FStar_Util.JsonList (uu____2628)))


let json_of_range_fields : Prims.string  ->  FStar_Range.pos  ->  FStar_Range.pos  ->  FStar_Util.json = (fun file b e -> (

let uu____2650 = (

let uu____2657 = (

let uu____2664 = (

let uu____2669 = (json_of_pos b)
in (("beg"), (uu____2669)))
in (

let uu____2670 = (

let uu____2677 = (

let uu____2682 = (json_of_pos e)
in (("end"), (uu____2682)))
in (uu____2677)::[])
in (uu____2664)::uu____2670))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____2657)
in FStar_Util.JsonAssoc (uu____2650)))


let json_of_use_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2703 = (FStar_Range.file_of_use_range r)
in (

let uu____2704 = (FStar_Range.start_of_use_range r)
in (

let uu____2705 = (FStar_Range.end_of_use_range r)
in (json_of_range_fields uu____2703 uu____2704 uu____2705)))))


let json_of_def_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2710 = (FStar_Range.file_of_range r)
in (

let uu____2711 = (FStar_Range.start_of_range r)
in (

let uu____2712 = (FStar_Range.end_of_range r)
in (json_of_range_fields uu____2710 uu____2711 uu____2712)))))


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

let uu____2721 = (

let uu____2728 = (

let uu____2735 = (

let uu____2742 = (

let uu____2747 = (

let uu____2748 = (

let uu____2751 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____2757 = (json_of_use_range r)
in (uu____2757)::[])
end)
in (

let uu____2758 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (r.FStar_Range.def_range <> r.FStar_Range.use_range) -> begin
(

let uu____2764 = (json_of_def_range r)
in (uu____2764)::[])
end
| uu____2765 -> begin
[]
end)
in (FStar_List.append uu____2751 uu____2758)))
in FStar_Util.JsonList (uu____2748))
in (("ranges"), (uu____2747)))
in (uu____2742)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____2735)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____2728)
in FStar_Util.JsonAssoc (uu____2721)))

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

let uu____2917 = (

let uu____2924 = (

let uu____2931 = (

let uu____2936 = (json_of_opt json_of_def_range lr.lr_def_range)
in (("defined-at"), (uu____2936)))
in (

let uu____2937 = (

let uu____2944 = (

let uu____2949 = (json_of_opt (fun _0_40 -> FStar_Util.JsonStr (_0_40)) lr.lr_typ)
in (("type"), (uu____2949)))
in (

let uu____2950 = (

let uu____2957 = (

let uu____2962 = (json_of_opt (fun _0_41 -> FStar_Util.JsonStr (_0_41)) lr.lr_doc)
in (("documentation"), (uu____2962)))
in (

let uu____2963 = (

let uu____2970 = (

let uu____2975 = (json_of_opt (fun _0_42 -> FStar_Util.JsonStr (_0_42)) lr.lr_def)
in (("definition"), (uu____2975)))
in (uu____2970)::[])
in (uu____2957)::uu____2963))
in (uu____2944)::uu____2950))
in (uu____2931)::uu____2937))
in ((("name"), (FStar_Util.JsonStr (lr.lr_name))))::uu____2924)
in FStar_Util.JsonAssoc (uu____2917)))


let json_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3008 = (FStar_List.map (fun _0_43 -> FStar_Util.JsonStr (_0_43)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_44 -> FStar_Util.JsonList (_0_44)) uu____3008))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____3030 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____3030));
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


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____3092 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3095 = (FStar_List.map (fun _0_45 -> FStar_Util.JsonStr (_0_45)) interactive_protocol_features)
in FStar_Util.JsonList (uu____3095))
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

let uu____3256 = (FStar_Options.docs ())
in (FStar_Util.smap_of_list uu____3256))
in (

let get_doc = (fun k -> (FStar_Util.smap_try_find opt_docs k))
in (FStar_List.map (fun uu____3288 -> (match (uu____3288) with
| (k, v1) -> begin
(

let uu____3305 = (FStar_Options.get_option k)
in (

let uu____3306 = (get_doc k)
in ((k), (uu____3305), (uu____3306), (v1))))
end)) FStar_Options.defaults)))
in (

let uu____3311 = (

let uu____3316 = (

let uu____3317 = (FStar_List.map (fun uu____3337 -> (match (uu____3337) with
| (uu____3350, fstname, uu____3352, uu____3353) -> begin
FStar_Util.JsonStr (fstname)
end)) st.repl_ts)
in FStar_Util.JsonList (uu____3317))
in (("loaded-dependencies"), (uu____3316)))
in (

let uu____3362 = (

let uu____3369 = (

let uu____3374 = (

let uu____3375 = (FStar_List.map (fun uu____3394 -> (match (uu____3394) with
| (name, value, doc1, dflt1) -> begin
(

let uu____3413 = (

let uu____3420 = (

let uu____3427 = (

let uu____3432 = (json_of_fstar_option value)
in (("value"), (uu____3432)))
in (

let uu____3433 = (

let uu____3440 = (

let uu____3445 = (json_of_fstar_option dflt1)
in (("default"), (uu____3445)))
in (

let uu____3446 = (

let uu____3453 = (

let uu____3458 = (json_of_opt (fun _0_46 -> FStar_Util.JsonStr (_0_46)) doc1)
in (("documentation"), (uu____3458)))
in (uu____3453)::[])
in (uu____3440)::uu____3446))
in (uu____3427)::uu____3433))
in ((("name"), (FStar_Util.JsonStr (name))))::uu____3420)
in FStar_Util.JsonAssoc (uu____3413))
end)) opts_and_defaults)
in FStar_Util.JsonList (uu____3375))
in (("options"), (uu____3374)))
in (uu____3369)::[])
in (uu____3311)::uu____3362))))


let run_exit : 'Auu____3497 'Auu____3498 . 'Auu____3498  ->  ((query_status * FStar_Util.json) * ('Auu____3497, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____3529 'Auu____3530 . 'Auu____3530  ->  ((query_status * FStar_Util.json) * ('Auu____3530, 'Auu____3529) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (json_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____3559 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3559) FStar_Util.either) = (fun st -> (

let uu____3576 = (

let uu____3581 = (

let uu____3582 = (json_of_repl_state st)
in FStar_Util.JsonAssoc (uu____3582))
in ((QueryOK), (uu____3581)))
in ((uu____3576), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____3605 'Auu____3606 . 'Auu____3606  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____3606, 'Auu____3605) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> ((FStar_List.length st.repl_stack) <= (FStar_List.length st.repl_ts)))


let run_pop : 'Auu____3659 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3659) FStar_Util.either) = (fun st -> (match ((nothing_left_to_pop st)) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____3684 -> begin
(match (st.repl_stack) with
| [] -> begin
(failwith "impossible")
end
| ((env, curmod))::stack -> begin
((pop st.repl_env "#pop");
(

let st' = (

let uu___202_3728 = st
in {repl_line = uu___202_3728.repl_line; repl_column = uu___202_3728.repl_column; repl_fname = uu___202_3728.repl_fname; repl_stack = stack; repl_curmod = curmod; repl_env = env; repl_ts = uu___202_3728.repl_ts; repl_stdin = uu___202_3728.repl_stdin})
in ((match ((nothing_left_to_pop st')) with
| true -> begin
(cleanup env)
end
| uu____3730 -> begin
()
end);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st')));
));
)
end)
end))


let run_push : 'Auu____3753 . repl_state  ->  push_kind  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____3753) FStar_Util.either) = (fun st kind text1 line column1 peek_only -> (

let uu____3790 = ((st.repl_stack), (st.repl_env), (st.repl_ts))
in (match (uu____3790) with
| (stack, env, ts) -> begin
(

let uu____3812 = (match ((nothing_left_to_pop st)) with
| true -> begin
(

let uu____3833 = (update_deps st.repl_fname st.repl_curmod stack env ts)
in ((true), (uu____3833)))
end
| uu____3846 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____3812) with
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

let uu____3915 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____3915 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___203_3924 = st
in {repl_line = line; repl_column = column1; repl_fname = uu___203_3924.repl_fname; repl_stack = stack2; repl_curmod = uu___203_3924.repl_curmod; repl_env = uu___203_3924.repl_env; repl_ts = ts1; repl_stdin = uu___203_3924.repl_stdin})
in (match (res) with
| FStar_Pervasives_Native.Some (curmod, env3, nerrs) when ((nerrs = (Prims.parse_int "0")) && (peek_only = false)) -> begin
(

let env4 = (commit_mark env3)
in ((((QueryOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl ((

let uu___204_3978 = st'
in {repl_line = uu___204_3978.repl_line; repl_column = uu___204_3978.repl_column; repl_fname = uu___204_3978.repl_fname; repl_stack = uu___204_3978.repl_stack; repl_curmod = curmod; repl_env = env4; repl_ts = uu___204_3978.repl_ts; repl_stdin = uu___204_3978.repl_stdin})))))
end
| uu____3979 -> begin
(

let env3 = (reset_mark env_mark)
in (

let uu____3999 = (run_pop (

let uu___205_4013 = st'
in {repl_line = uu___205_4013.repl_line; repl_column = uu___205_4013.repl_column; repl_fname = uu___205_4013.repl_fname; repl_stack = uu___205_4013.repl_stack; repl_curmod = uu___205_4013.repl_curmod; repl_env = env3; repl_ts = uu___205_4013.repl_ts; repl_stdin = uu___205_4013.repl_stdin}))
in (match (uu____3999) with
| (uu____4026, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____4045 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end)))
end));
)))))))
end))
end)))


let run_lookup : 'Auu____4064 . repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4064) FStar_Util.either) = (fun st symbol pos_opt requested_info -> (

let uu____4113 = st.repl_env
in (match (uu____4113) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____4145 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____4145))
in (

let lid1 = (

let uu____4149 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____4149))
in (

let uu____4154 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____4154 (FStar_Util.map_option (fun uu____4209 -> (match (uu____4209) with
| ((uu____4228, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____4245 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____4245 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____4274 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____4274 (fun uu___192_4318 -> (match (uu___192_4318) with
| (FStar_Util.Inr (se, uu____4340), uu____4341) -> begin
(

let uu____4370 = (FStar_Syntax_Print.sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____4370))
end
| uu____4371 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____4423 -> (match (uu____4423) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____4470) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((symbol = "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4523 -> begin
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

let uu____4572 = (FStar_Syntax_Print.term_to_string typ)
in FStar_Pervasives_Native.Some (uu____4572))
end
| uu____4573 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____4580 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____4591 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____4601 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {lr_name = name; lr_def_range = def_range; lr_typ = typ_str; lr_doc = doc_str; lr_def = def_str}
in (

let uu____4603 = (json_of_lookup_result result)
in ((QueryOK), (uu____4603)))))))))
end)
in ((response), (FStar_Util.Inl (st)))))))))
end)))


let run_completions : 'Auu____4618 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4618) FStar_Util.either) = (fun st search_term -> (

let uu____4639 = st.repl_env
in (match (uu____4639) with
| (dsenv, tcenv) -> begin
(

let rec measure_anchored_match = (fun search_term1 candidate -> (match (((search_term1), (candidate))) with
| ([], uu____4689) -> begin
FStar_Pervasives_Native.Some ((([]), ((Prims.parse_int "0"))))
end
| (uu____4704, []) -> begin
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
| uu____4754 -> begin
(

let uu____4757 = (measure_anchored_match ts tc)
in (FStar_All.pipe_right uu____4757 (FStar_Util.map_option (fun uu____4797 -> (match (uu____4797) with
| (matched, len) -> begin
(((hc)::matched), ((((FStar_String.length hc_text) + (Prims.parse_int "1")) + len)))
end)))))
end)
end
| uu____4818 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let rec locate_match = (fun needle candidate -> (

let uu____4852 = (measure_anchored_match needle candidate)
in (match (uu____4852) with
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

let uu____4931 = (locate_match needle tc)
in (FStar_All.pipe_right uu____4931 (FStar_Util.map_option (fun uu____4992 -> (match (uu____4992) with
| (prefix1, matched, len) -> begin
(((hc)::prefix1), (matched), (len))
end)))))
end)
end)))
in (

let str_of_ids = (fun ids -> (

let uu____5036 = (FStar_List.map FStar_Ident.text_of_id ids)
in (FStar_Util.concat_l "." uu____5036)))
in (

let match_lident_against = (fun needle lident -> (locate_match needle (FStar_List.append lident.FStar_Ident.ns ((lident.FStar_Ident.ident)::[]))))
in (

let shorten_namespace = (fun uu____5083 -> (match (uu____5083) with
| (prefix1, matched, match_len) -> begin
(

let naked_match = (match (matched) with
| (uu____5114)::[] -> begin
true
end
| uu____5115 -> begin
false
end)
in (

let uu____5118 = (FStar_ToSyntax_Env.shorten_module_path dsenv prefix1 naked_match)
in (match (uu____5118) with
| (stripped_ns, shortened) -> begin
(

let uu____5145 = (str_of_ids shortened)
in (

let uu____5146 = (str_of_ids matched)
in (

let uu____5147 = (str_of_ids stripped_ns)
in ((uu____5145), (uu____5146), (uu____5147), (match_len)))))
end)))
end))
in (

let prepare_candidate = (fun uu____5165 -> (match (uu____5165) with
| (prefix1, matched, stripped_ns, match_len) -> begin
(match ((prefix1 = "")) with
| true -> begin
((matched), (stripped_ns), (match_len))
end
| uu____5190 -> begin
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

let uu____5293 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_Option.map (fun fqn -> (

let uu____5309 = (

let uu____5312 = (FStar_List.map FStar_Ident.id_of_text orig_ns)
in (FStar_List.append uu____5312 ((fqn.FStar_Ident.ident)::[])))
in (([]), (uu____5309), (matched_length)))) uu____5293)))
end
| uu____5319 -> begin
FStar_Pervasives_Native.None
end)))))))
in (

let case_b_find_matches_in_env = (fun uu____5345 -> (

let matches = (FStar_List.filter_map (match_lident_against needle) all_lidents_in_env)
in (FStar_All.pipe_right matches (FStar_List.filter (fun uu____5420 -> (match (uu____5420) with
| (ns, id, uu____5433) -> begin
(

let uu____5442 = (

let uu____5445 = (FStar_Ident.lid_of_ids id)
in (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv uu____5445))
in (match (uu____5442) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____5447 = (FStar_Ident.lid_of_ids (FStar_List.append ns id))
in (FStar_Ident.lid_equals l uu____5447))
end))
end))))))
in (

let uu____5448 = (FStar_Util.prefix needle)
in (match (uu____5448) with
| (ns, id) -> begin
(

let matched_ids = (match (ns) with
| [] -> begin
(case_b_find_matches_in_env ())
end
| uu____5494 -> begin
(

let l = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in (

let uu____5498 = (FStar_ToSyntax_Env.resolve_module_name dsenv l true)
in (match (uu____5498) with
| FStar_Pervasives_Native.None -> begin
(case_b_find_matches_in_env ())
end
| FStar_Pervasives_Native.Some (m) -> begin
(case_a_find_transitive_includes ns m id)
end)))
end)
in (FStar_All.pipe_right matched_ids (FStar_List.map (fun x -> (

let uu____5563 = (shorten_namespace x)
in (prepare_candidate uu____5563))))))
end))))
in (

let json_candidates = (

let uu____5575 = (FStar_Util.sort_with (fun uu____5598 uu____5599 -> (match (((uu____5598), (uu____5599))) with
| ((cd1, ns1, uu____5626), (cd2, ns2, uu____5629)) -> begin
(match ((FStar_String.compare cd1 cd2)) with
| _0_47 when (_0_47 = (Prims.parse_int "0")) -> begin
(FStar_String.compare ns1 ns2)
end
| n1 -> begin
n1
end)
end)) matches)
in (FStar_List.map (fun uu____5653 -> (match (uu____5653) with
| (candidate, ns, match_len) -> begin
FStar_Util.JsonList ((FStar_Util.JsonInt (match_len))::(FStar_Util.JsonStr (ns))::(FStar_Util.JsonStr (candidate))::[])
end)) uu____5575))
in ((((QueryOK), (FStar_Util.JsonList (json_candidates)))), (FStar_Util.Inl (st)))))))))))))
end)))


let run_compute : 'Auu____5679 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5679) FStar_Util.either) = (fun st term rules -> (

let run_and_rewind = (fun st1 task -> (

let env_mark = (mark st1.repl_env)
in (

let results = (task st1)
in (

let env = (reset_mark env_mark)
in (

let st' = (

let uu___206_5760 = st1
in {repl_line = uu___206_5760.repl_line; repl_column = uu___206_5760.repl_column; repl_fname = uu___206_5760.repl_fname; repl_stack = uu___206_5760.repl_stack; repl_curmod = uu___206_5760.repl_curmod; repl_env = env; repl_ts = uu___206_5760.repl_ts; repl_stdin = uu___206_5760.repl_stdin})
in ((results), (FStar_Util.Inl (st'))))))))
in (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let normalize_term1 = (fun tcenv rules1 t -> (FStar_TypeChecker_Normalize.normalize rules1 tcenv t))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____5800, ({FStar_Syntax_Syntax.lbname = uu____5801; FStar_Syntax_Syntax.lbunivs = uu____5802; FStar_Syntax_Syntax.lbtyp = uu____5803; FStar_Syntax_Syntax.lbeff = uu____5804; FStar_Syntax_Syntax.lbdef = def})::[]), uu____5806); FStar_Syntax_Syntax.sigrng = uu____5807; FStar_Syntax_Syntax.sigquals = uu____5808; FStar_Syntax_Syntax.sigmeta = uu____5809; FStar_Syntax_Syntax.sigattrs = uu____5810})::[] -> begin
FStar_Pervasives_Native.Some (def)
end
| uu____5839 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____5852 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____5852) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____5876) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____5921 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____5953 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (FStar_Pervasives_Native.snd uu____5953)))
in (

let typecheck = (fun tcenv decls -> (

let uu____5971 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____5971) with
| (ses, uu____5985, uu____5986) -> begin
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

let uu____6014 = st1.repl_env
in (match (uu____6014) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____6026 -> begin
(

let uu____6027 = (parse1 frag)
in (match (uu____6027) with
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

let uu____6071 = (

let uu____6072 = (FStar_Syntax_Print.term_to_string normalized)
in FStar_Util.JsonStr (uu____6072))
in ((QueryOK), (uu____6071))))
end)))
end)
with
| e -> begin
(

let uu____6082 = (

let uu____6083 = (FStar_Errors.issue_of_exn e)
in (match (uu____6083) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____6087 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____6087))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise e)
end))
in ((QueryNOK), (uu____6082)))
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
| uu____6109 -> begin
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
| uu____6123 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___193_6147 -> (match (uu___193_6147) with
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

let uu____6255 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____6262 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____6255; sc_fvars = uu____6262})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____6287 = (FStar_ST.read sc.sc_typ)
in (match (uu____6287) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____6296 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____6296) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____6317, typ), uu____6319) -> begin
typ
end))
in ((FStar_ST.write sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____6347 = (FStar_ST.read sc.sc_fvars)
in (match (uu____6347) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____6368 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____6368))
in ((FStar_ST.write sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____6389 = (sc_typ tcenv sc)
in (FStar_Syntax_Print.term_to_string uu____6389))
in (

let uu____6390 = (

let uu____6397 = (

let uu____6402 = (

let uu____6403 = (

let uu____6404 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____6404.FStar_Ident.str)
in FStar_Util.JsonStr (uu____6403))
in (("lid"), (uu____6402)))
in (uu____6397)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____6390))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____6424) -> begin
true
end
| uu____6425 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____6433) -> begin
uu____6433
end))


let run_search : 'Auu____6440 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6440) FStar_Util.either) = (fun st search_str -> (

let uu____6461 = st.repl_env
in (match (uu____6461) with
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

let uu____6489 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____6489))
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
| uu____6504 -> begin
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
| uu____6511 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((beg_quote <> end_quote)) with
| true -> begin
(

let uu____6513 = (

let uu____6514 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____6514))
in (FStar_Pervasives.raise uu____6513))
end
| uu____6515 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____6516 = (strip_quotes term1)
in NameContainsStr (uu____6516))
end
| uu____6517 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____6519 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____6519) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6522 = (

let uu____6523 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____6523))
in (FStar_Pervasives.raise uu____6522))
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

let uu____6539 = (match (term.st_term) with
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
| uu____6542 -> begin
""
end) uu____6539)))
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

let js = (FStar_Options.with_saved_options (fun uu____6601 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(FStar_List.map (json_of_search_result dsenv tcenv) sorted1);
)))
in (match (results) with
| [] -> begin
(

let kwds = (

let uu____6608 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____6608))
in (

let uu____6611 = (

let uu____6612 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____6612))
in (FStar_Pervasives.raise uu____6611)))
end
| uu____6617 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)
with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___194_6668 -> (match (uu___194_6668) with
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

let uu____6727 = (

let uu____6740 = (run_query st)
in (uu____6740 query.qq))
in (match (uu____6727) with
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

let uu____6784 = (

let uu____6787 = (FStar_ST.read issues)
in (e)::uu____6787)
in (FStar_ST.write issues uu____6784)))
in (

let count_errors = (fun uu____6801 -> (

let uu____6802 = (

let uu____6805 = (FStar_ST.read issues)
in (FStar_List.filter (fun e -> (e.FStar_Errors.issue_level = FStar_Errors.EError)) uu____6805))
in (FStar_List.length uu____6802)))
in (

let report1 = (fun uu____6819 -> (

let uu____6820 = (FStar_ST.read issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____6820)))
in (

let clear1 = (fun uu____6830 -> (FStar_ST.write issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (write_message "info"); FStar_Util.printer_prwarning = (write_message "warning"); FStar_Util.printer_prerror = (write_message "error")}


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let uu____6844 = (deps_of_our_file filename)
in (match (uu____6844) with
| (filenames, maybe_intf) -> begin
(

let env = (tc_prims ())
in (

let uu____6868 = (tc_deps FStar_Pervasives_Native.None [] env filenames [])
in (match (uu____6868) with
| (stack, env1, ts) -> begin
(

let initial_range = (

let uu____6895 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____6896 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____6895 uu____6896)))
in (

let env2 = (

let uu____6902 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env1) initial_range)
in (((FStar_Pervasives_Native.fst env1)), (uu____6902)))
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

let uu____6914 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_stack = stack; repl_curmod = FStar_Pervasives_Native.None; repl_env = env3; repl_ts = ts; repl_stdin = uu____6914})
in ((FStar_TypeChecker_Common.insert_id_info.FStar_TypeChecker_Common.enable true);
(

let uu____6916 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____6916) with
| true -> begin
(

let uu____6917 = (

let uu____6918 = (FStar_Options.file_list ())
in (FStar_List.hd uu____6918))
in (FStar_SMTEncoding_Solver.with_hints_db uu____6917 (fun uu____6922 -> (go init_st))))
end
| uu____6923 -> begin
(go init_st)
end));
)))))
end)))
end));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(FStar_Errors.set_handler interactive_error_handler);
(

let uu____6931 = (

let uu____6932 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____6932))
in (match (uu____6931) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____6935 -> begin
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




