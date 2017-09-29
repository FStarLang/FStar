
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


let tc_prims : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun env -> (

let uu____273 = (FStar_Universal.tc_prims env)
in (match (uu____273) with
| (uu____288, dsenv, env1) -> begin
((dsenv), (env1))
end)))


type env_t =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


type modul_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option


let push : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun env msg -> (

let res = (FStar_Universal.push_context env msg)
in ((FStar_Options.push ());
res;
)))


let pop : 'Auu____337 . ('Auu____337 * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((FStar_Universal.pop_context (FStar_Pervasives_Native.snd env) msg);
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
| uu____359 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____364 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____369 -> begin
false
end))


let set_check_kind : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  push_kind  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____384 check_kind -> (match (uu____384) with
| (dsenv, tcenv) -> begin
(

let tcenv1 = (

let uu___249_397 = tcenv
in {FStar_TypeChecker_Env.solver = uu___249_397.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___249_397.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___249_397.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___249_397.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___249_397.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___249_397.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___249_397.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___249_397.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___249_397.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___249_397.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___249_397.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___249_397.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___249_397.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___249_397.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___249_397.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___249_397.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___249_397.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___249_397.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality check_kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___249_397.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___249_397.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___249_397.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___249_397.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___249_397.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___249_397.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___249_397.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___249_397.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___249_397.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___249_397.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___249_397.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___249_397.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___249_397.FStar_TypeChecker_Env.tc_hooks})
in (

let dsenv1 = (FStar_ToSyntax_Env.set_syntax_only dsenv (Prims.op_Equality check_kind SyntaxCheck))
in ((dsenv1), (tcenv1))))
end))


let cleanup : 'Auu____403 . ('Auu____403 * FStar_TypeChecker_Env.env)  ->  Prims.unit = (fun uu____411 -> (match (uu____411) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))


let check_frag : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) * Prims.int) FStar_Pervasives_Native.option = (fun uu____451 curmod frag -> (match (uu____451) with
| (dsenv, env) -> begin
(FStar_All.try_with (fun uu___251_500 -> (match (()) with
| () -> begin
(

let uu____515 = (FStar_Universal.tc_one_fragment curmod dsenv env frag)
in (match (uu____515) with
| FStar_Pervasives_Native.Some (m, dsenv1, env1) -> begin
(

let uu____555 = (

let uu____568 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv1), (env1))), (uu____568)))
in FStar_Pervasives_Native.Some (uu____555))
end
| uu____587 -> begin
FStar_Pervasives_Native.None
end))
end)) (fun uu___250_615 -> (match (uu___250_615) with
| FStar_All.Failure (msg) when (

let uu____631 = (FStar_Options.trace_error ())
in (not (uu____631))) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____634 = (

let uu____641 = (

let uu____646 = (FStar_TypeChecker_Env.get_range env)
in ((msg1), (uu____646)))
in (uu____641)::[])
in (FStar_TypeChecker_Err.add_errors env uu____634));
(FStar_Util.print_error msg1);
FStar_Pervasives_Native.None;
))
end
| FStar_Errors.Error (msg, r) when (

let uu____670 = (FStar_Options.trace_error ())
in (not (uu____670))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____693 = (FStar_Options.trace_error ())
in (not (uu____693))) -> begin
((

let uu____695 = (

let uu____702 = (

let uu____707 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____707)))
in (uu____702)::[])
in (FStar_TypeChecker_Err.add_errors env uu____695));
FStar_Pervasives_Native.None;
)
end)))
end))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string FStar_Pervasives_Native.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____743 = (FStar_List.partition (fun x -> (

let uu____756 = (FStar_Parser_Dep.lowercase_module_name x)
in (

let uu____757 = (FStar_Parser_Dep.lowercase_module_name filename)
in (Prims.op_disEquality uu____756 uu____757)))) deps)
in (match (uu____743) with
| (deps1, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____784 = ((

let uu____787 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____787))) || (

let uu____789 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____789))))
in (match (uu____784) with
| true -> begin
(

let uu____790 = (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl)
in (FStar_Util.print_warning uu____790))
end
| uu____791 -> begin
()
end));
FStar_Pervasives_Native.Some (intf);
)
end
| (impl)::[] -> begin
FStar_Pervasives_Native.None
end
| uu____793 -> begin
((

let uu____797 = (FStar_Util.format1 "Unsupported: ended up with %s" (FStar_String.concat " " same_name))
in (FStar_Util.print_warning uu____797));
FStar_Pervasives_Native.None;
)
end)
in ((deps1), (maybe_intf)))
end))))


type m_timestamps =
(Prims.string FStar_Pervasives_Native.option * Prims.string * FStar_Util.time FStar_Pervasives_Native.option * FStar_Util.time) Prims.list


type deps_stack_t =
env_t Prims.list


let rec tc_deps : deps_stack_t  ->  env_t  ->  Prims.string Prims.list  ->  m_timestamps  ->  (env_t * (deps_stack_t * m_timestamps)) = (fun deps_stack env remaining ts -> (match (remaining) with
| [] -> begin
((env), (((deps_stack), (ts))))
end
| uu____858 -> begin
(

let deps_stack1 = (env)::deps_stack
in (

let push_kind = (

let uu____865 = (FStar_Options.lax ())
in (match (uu____865) with
| true -> begin
LaxCheck
end
| uu____866 -> begin
FullCheck
end))
in (

let env1 = (

let uu____872 = (set_check_kind env push_kind)
in (push uu____872 "typecheck_modul"))
in ((

let uu____878 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____878 FStar_Pervasives.ignore));
(

let uu____879 = (tc_one_file remaining env1)
in (match (uu____879) with
| ((intf, impl), env2, remaining1) -> begin
(

let uu____932 = (

let intf_t = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(

let uu____945 = (FStar_Util.get_file_last_modification_time intf1)
in FStar_Pervasives_Native.Some (uu____945))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____932) with
| (intf_t, impl_t) -> begin
(tc_deps deps_stack1 env2 remaining1 ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end));
))))
end))


let update_deps : Prims.string  ->  env_t  ->  (deps_stack_t * m_timestamps)  ->  (env_t * (deps_stack_t * m_timestamps)) = (fun filename env uu____1002 -> (match (uu____1002) with
| (stk, ts) -> begin
(

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
| (uu____1065, uu____1066) -> begin
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
| uu____1172 -> begin
((false), (depnames1))
end)
end
| uu____1175 -> begin
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
| uu____1200 -> begin
((false), (depnames1))
end)
end
| uu____1203 -> begin
((false), (depnames1))
end)
end))
in (

let rec pop_tc_and_stack = (fun env1 stack ts2 -> (match (ts2) with
| [] -> begin
env1
end
| (uu____1278)::ts3 -> begin
((pop env1 "");
(

let uu____1319 = (

let uu____1326 = (FStar_List.hd stack)
in (

let uu____1327 = (FStar_List.tl stack)
in ((uu____1326), (uu____1327))))
in (match (uu____1319) with
| (env2, stack1) -> begin
(pop_tc_and_stack env2 stack1 ts3)
end));
)
end))
in (match (ts1) with
| (ts_elt)::ts' -> begin
(

let uu____1392 = ts_elt
in (match (uu____1392) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1427 = (match_dep depnames intf impl)
in (match (uu____1427) with
| (b, depnames') -> begin
(

let uu____1450 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1450) with
| true -> begin
(

let env1 = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts1)
in (tc_deps good_stack env1 depnames good_ts))
end
| uu____1466 -> begin
(

let uu____1467 = (

let uu____1474 = (FStar_List.hd st)
in (

let uu____1475 = (FStar_List.tl st)
in ((uu____1474), (uu____1475))))
in (match (uu____1467) with
| (stack_elt, st') -> begin
(iterate depnames' st' env' ts' ((stack_elt)::good_stack) ((ts_elt)::good_ts))
end))
end))
end))
end))
end
| [] -> begin
(tc_deps good_stack env' depnames good_ts)
end))))
in (

let uu____1520 = (deps_of_our_file filename)
in (match (uu____1520) with
| (filenames, uu____1538) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end))))
end))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___236_1586 -> (match (uu___236_1586) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____1588 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____1590 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____1590))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____1592) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____1595) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1613) -> begin
true
end
| uu____1618 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____1634) -> begin
uu____1634
end))


let js_fail : 'Auu____1645 . Prims.string  ->  FStar_Util.json  ->  'Auu____1645 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___237_1657 -> (match (uu___237_1657) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___238_1663 -> (match (uu___238_1663) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____1672 . (FStar_Util.json  ->  'Auu____1672)  ->  FStar_Util.json  ->  'Auu____1672 Prims.list = (fun k uu___239_1685 -> (match (uu___239_1685) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___240_1703 -> (match (uu___240_1703) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____1728 = (js_str s)
in (match (uu____1728) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____1729 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____1734 = (js_str s)
in (match (uu____1734) with
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
| uu____1735 -> begin
(js_fail "reduction rule" s)
end)))

type completion_context =
| CKCode
| CKOption of Prims.bool
| CKModuleOrNamespace of (Prims.bool * Prims.bool)


let uu___is_CKCode : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKCode -> begin
true
end
| uu____1752 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____1758 -> begin
false
end))


let __proj__CKOption__item___0 : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
_0
end))


let uu___is_CKModuleOrNamespace : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKModuleOrNamespace (_0) -> begin
true
end
| uu____1776 -> begin
false
end))


let __proj__CKModuleOrNamespace__item___0 : completion_context  ->  (Prims.bool * Prims.bool) = (fun projectee -> (match (projectee) with
| CKModuleOrNamespace (_0) -> begin
_0
end))


let js_optional_completion_context : FStar_Util.json FStar_Pervasives_Native.option  ->  completion_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
CKCode
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____1806 = (js_str k1)
in (match (uu____1806) with
| "symbol" -> begin
CKCode
end
| "code" -> begin
CKCode
end
| "set-options" -> begin
CKOption (false)
end
| "reset-options" -> begin
CKOption (true)
end
| "open" -> begin
CKModuleOrNamespace (((true), (true)))
end
| "let-open" -> begin
CKModuleOrNamespace (((true), (true)))
end
| "include" -> begin
CKModuleOrNamespace (((true), (false)))
end
| "module-alias" -> begin
CKModuleOrNamespace (((true), (false)))
end
| uu____1807 -> begin
(js_fail "completion context (code, set-options, reset-options, open, let-open, include, module-alias)" k1)
end))
end))

type lookup_context =
| LKSymbolOnly
| LKModule
| LKOption
| LKCode


let uu___is_LKSymbolOnly : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKSymbolOnly -> begin
true
end
| uu____1812 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____1817 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____1822 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____1827 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____1837 = (js_str k1)
in (match (uu____1837) with
| "symbol-only" -> begin
LKSymbolOnly
end
| "code" -> begin
LKCode
end
| "set-options" -> begin
LKOption
end
| "reset-options" -> begin
LKOption
end
| "open" -> begin
LKModule
end
| "let-open" -> begin
LKModule
end
| "include" -> begin
LKModule
end
| "module-alias" -> begin
LKModule
end
| uu____1838 -> begin
(js_fail "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)" k1)
end))
end))


type position =
(Prims.string * Prims.int * Prims.int)

type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Pop
| Push of (push_kind * Prims.string * Prims.int * Prims.int * Prims.bool)
| AutoComplete of (Prims.string * completion_context)
| Lookup of (Prims.string * lookup_context * position FStar_Pervasives_Native.option * Prims.string Prims.list)
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
| uu____1915 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1920 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1925 -> begin
false
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1930 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1946 -> begin
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
| uu____1994 -> begin
false
end))


let __proj__AutoComplete__item___0 : query'  ->  (Prims.string * completion_context) = (fun projectee -> (match (projectee) with
| AutoComplete (_0) -> begin
_0
end))


let uu___is_Lookup : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lookup (_0) -> begin
true
end
| uu____2032 -> begin
false
end))


let __proj__Lookup__item___0 : query'  ->  (Prims.string * lookup_context * position FStar_Pervasives_Native.option * Prims.string Prims.list) = (fun projectee -> (match (projectee) with
| Lookup (_0) -> begin
_0
end))


let uu___is_Compute : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Compute (_0) -> begin
true
end
| uu____2090 -> begin
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
| uu____2128 -> begin
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
| uu____2141 -> begin
false
end))


let uu___is_ProtocolViolation : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
true
end
| uu____2147 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___241_2171 -> (match (uu___241_2171) with
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
| Push (uu____2172, uu____2173, uu____2174, uu____2175, false) -> begin
false
end
| MissingCurrentModule -> begin
false
end
| ProtocolViolation (uu____2176) -> begin
false
end
| Push (uu____2177) -> begin
true
end
| AutoComplete (uu____2188) -> begin
true
end
| Lookup (uu____2193) -> begin
true
end
| Compute (uu____2206) -> begin
true
end
| Search (uu____2215) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2225) -> begin
true
end
| uu____2226 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2234) -> begin
uu____2234
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____2239 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____2244 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____2249 -> begin
false
end))


let try_assoc : 'Auu____2258 'Auu____2259 . 'Auu____2259  ->  ('Auu____2259 * 'Auu____2258) Prims.list  ->  'Auu____2258 FStar_Pervasives_Native.option = (fun key a -> (

let uu____2282 = (FStar_Util.try_find (fun uu____2296 -> (match (uu____2296) with
| (k, uu____2302) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____2282)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____2319 = (

let uu____2320 = (

let uu____2321 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____2321))
in ProtocolViolation (uu____2320))
in {qq = uu____2319; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____2348 = (try_assoc key a)
in (match (uu____2348) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2352 = (

let uu____2353 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____2353))
in (FStar_Exn.raise uu____2352))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____2368 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____2368 js_str))
in (FStar_All.try_with (fun uu___253_2375 -> (match (()) with
| () -> begin
(

let query = (

let uu____2377 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____2377 js_str))
in (

let args = (

let uu____2385 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____2385 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____2402 = (try_assoc k args)
in (match (uu____2402) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____2410 = (match (query) with
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

let uu____2411 = (

let uu____2422 = (

let uu____2423 = (arg "kind")
in (FStar_All.pipe_right uu____2423 js_pushkind))
in (

let uu____2424 = (

let uu____2425 = (arg "code")
in (FStar_All.pipe_right uu____2425 js_str))
in (

let uu____2426 = (

let uu____2427 = (arg "line")
in (FStar_All.pipe_right uu____2427 js_int))
in (

let uu____2428 = (

let uu____2429 = (arg "column")
in (FStar_All.pipe_right uu____2429 js_int))
in ((uu____2422), (uu____2424), (uu____2426), (uu____2428), ((Prims.op_Equality query "peek")))))))
in Push (uu____2411))
end
| "push" -> begin
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
| "autocomplete" -> begin
(

let uu____2449 = (

let uu____2454 = (

let uu____2455 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____2455 js_str))
in (

let uu____2456 = (

let uu____2457 = (try_arg "context")
in (FStar_All.pipe_right uu____2457 js_optional_completion_context))
in ((uu____2454), (uu____2456))))
in AutoComplete (uu____2449))
end
| "lookup" -> begin
(

let uu____2462 = (

let uu____2475 = (

let uu____2476 = (arg "symbol")
in (FStar_All.pipe_right uu____2476 js_str))
in (

let uu____2477 = (

let uu____2478 = (try_arg "context")
in (FStar_All.pipe_right uu____2478 js_optional_lookup_context))
in (

let uu____2483 = (

let uu____2492 = (

let uu____2501 = (try_arg "location")
in (FStar_All.pipe_right uu____2501 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____2492 (FStar_Util.map_option (fun loc -> (

let uu____2559 = (

let uu____2560 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____2560 js_str))
in (

let uu____2561 = (

let uu____2562 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____2562 js_int))
in (

let uu____2563 = (

let uu____2564 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____2564 js_int))
in ((uu____2559), (uu____2561), (uu____2563)))))))))
in (

let uu____2565 = (

let uu____2568 = (arg "requested-info")
in (FStar_All.pipe_right uu____2568 (js_list js_str)))
in ((uu____2475), (uu____2477), (uu____2483), (uu____2565))))))
in Lookup (uu____2462))
end
| "compute" -> begin
(

let uu____2581 = (

let uu____2590 = (

let uu____2591 = (arg "term")
in (FStar_All.pipe_right uu____2591 js_str))
in (

let uu____2592 = (

let uu____2597 = (try_arg "rules")
in (FStar_All.pipe_right uu____2597 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____2590), (uu____2592))))
in Compute (uu____2581))
end
| "search" -> begin
(

let uu____2612 = (

let uu____2613 = (arg "terms")
in (FStar_All.pipe_right uu____2613 js_str))
in Search (uu____2612))
end
| uu____2614 -> begin
(

let uu____2615 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____2615))
end)
in {qq = uu____2410; qid = qid})))))
end)) (fun uu___252_2618 -> (match (uu___252_2618) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (FStar_All.try_with (fun uu___255_2628 -> (match (()) with
| () -> begin
(

let uu____2629 = (FStar_Util.read_line stream)
in (match (uu____2629) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____2633 = (FStar_Util.json_of_string line)
in (match (uu____2633) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(unpack_interactive_query request)
end))
end))
end)) (fun uu___254_2639 -> (match (uu___254_2639) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let json_of_opt : 'Auu____2649 . ('Auu____2649  ->  FStar_Util.json)  ->  'Auu____2649 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____2667 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____2667)))


let json_of_pos : FStar_Range.pos  ->  FStar_Util.json = (fun pos -> (

let uu____2674 = (

let uu____2677 = (

let uu____2678 = (FStar_Range.line_of_pos pos)
in FStar_Util.JsonInt (uu____2678))
in (

let uu____2679 = (

let uu____2682 = (

let uu____2683 = (FStar_Range.col_of_pos pos)
in FStar_Util.JsonInt (uu____2683))
in (uu____2682)::[])
in (uu____2677)::uu____2679))
in FStar_Util.JsonList (uu____2674)))


let json_of_range_fields : Prims.string  ->  FStar_Range.pos  ->  FStar_Range.pos  ->  FStar_Util.json = (fun file b e -> (

let uu____2696 = (

let uu____2703 = (

let uu____2710 = (

let uu____2715 = (json_of_pos b)
in (("beg"), (uu____2715)))
in (

let uu____2716 = (

let uu____2723 = (

let uu____2728 = (json_of_pos e)
in (("end"), (uu____2728)))
in (uu____2723)::[])
in (uu____2710)::uu____2716))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____2703)
in FStar_Util.JsonAssoc (uu____2696)))


let json_of_use_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2749 = (FStar_Range.file_of_use_range r)
in (

let uu____2750 = (FStar_Range.start_of_use_range r)
in (

let uu____2751 = (FStar_Range.end_of_use_range r)
in (json_of_range_fields uu____2749 uu____2750 uu____2751)))))


let json_of_def_range : FStar_Range.range  ->  FStar_Util.json = (fun r -> (

let uu____2756 = (FStar_Range.file_of_range r)
in (

let uu____2757 = (FStar_Range.start_of_range r)
in (

let uu____2758 = (FStar_Range.end_of_range r)
in (json_of_range_fields uu____2756 uu____2757 uu____2758)))))


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

let uu____2767 = (

let uu____2774 = (

let uu____2781 = (

let uu____2788 = (

let uu____2793 = (

let uu____2794 = (

let uu____2797 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____2803 = (json_of_use_range r)
in (uu____2803)::[])
end)
in (

let uu____2804 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (Prims.op_disEquality r.FStar_Range.def_range r.FStar_Range.use_range) -> begin
(

let uu____2810 = (json_of_def_range r)
in (uu____2810)::[])
end
| uu____2811 -> begin
[]
end)
in (FStar_List.append uu____2797 uu____2804)))
in FStar_Util.JsonList (uu____2794))
in (("ranges"), (uu____2793)))
in (uu____2788)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____2781)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____2774)
in FStar_Util.JsonAssoc (uu____2767)))

type symbol_lookup_result =
{slr_name : Prims.string; slr_def_range : FStar_Range.range FStar_Pervasives_Native.option; slr_typ : Prims.string FStar_Pervasives_Native.option; slr_doc : Prims.string FStar_Pervasives_Native.option; slr_def : Prims.string FStar_Pervasives_Native.option}


let __proj__Mksymbol_lookup_result__item__slr_name : symbol_lookup_result  ->  Prims.string = (fun projectee -> (match (projectee) with
| {slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range; slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc; slr_def = __fname__slr_def} -> begin
__fname__slr_name
end))


let __proj__Mksymbol_lookup_result__item__slr_def_range : symbol_lookup_result  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range; slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc; slr_def = __fname__slr_def} -> begin
__fname__slr_def_range
end))


let __proj__Mksymbol_lookup_result__item__slr_typ : symbol_lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range; slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc; slr_def = __fname__slr_def} -> begin
__fname__slr_typ
end))


let __proj__Mksymbol_lookup_result__item__slr_doc : symbol_lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range; slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc; slr_def = __fname__slr_def} -> begin
__fname__slr_doc
end))


let __proj__Mksymbol_lookup_result__item__slr_def : symbol_lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range; slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc; slr_def = __fname__slr_def} -> begin
__fname__slr_def
end))


let alist_of_symbol_lookup_result : symbol_lookup_result  ->  (Prims.string * FStar_Util.json) Prims.list = (fun lr -> (

let uu____2969 = (

let uu____2976 = (

let uu____2981 = (json_of_opt json_of_def_range lr.slr_def_range)
in (("defined-at"), (uu____2981)))
in (

let uu____2982 = (

let uu____2989 = (

let uu____2994 = (json_of_opt (fun _0_42 -> FStar_Util.JsonStr (_0_42)) lr.slr_typ)
in (("type"), (uu____2994)))
in (

let uu____2995 = (

let uu____3002 = (

let uu____3007 = (json_of_opt (fun _0_43 -> FStar_Util.JsonStr (_0_43)) lr.slr_doc)
in (("documentation"), (uu____3007)))
in (

let uu____3008 = (

let uu____3015 = (

let uu____3020 = (json_of_opt (fun _0_44 -> FStar_Util.JsonStr (_0_44)) lr.slr_def)
in (("definition"), (uu____3020)))
in (uu____3015)::[])
in (uu____3002)::uu____3008))
in (uu____2989)::uu____2995))
in (uu____2976)::uu____2982))
in ((("name"), (FStar_Util.JsonStr (lr.slr_name))))::uu____2969))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3053 = (FStar_List.map (fun _0_45 -> FStar_Util.JsonStr (_0_45)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_46 -> FStar_Util.JsonList (_0_46)) uu____3053))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____3074 -> begin
false
end))


let uu___is_OptReset : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReset -> begin
true
end
| uu____3079 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____3084 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___242_3088 -> (match (uu___242_3088) with
| OptSet -> begin
""
end
| OptReset -> begin
"requires #reset-options"
end
| OptReadOnly -> begin
"read-only"
end))

type fstar_option =
{opt_name : Prims.string; opt_sig : Prims.string; opt_value : FStar_Options.option_val; opt_default : FStar_Options.option_val; opt_type : FStar_Options.opt_type; opt_snippets : Prims.string Prims.list; opt_documentation : Prims.string FStar_Pervasives_Native.option; opt_permission_level : fstar_option_permission_level}


let __proj__Mkfstar_option__item__opt_name : fstar_option  ->  Prims.string = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_name
end))


let __proj__Mkfstar_option__item__opt_sig : fstar_option  ->  Prims.string = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_sig
end))


let __proj__Mkfstar_option__item__opt_value : fstar_option  ->  FStar_Options.option_val = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_value
end))


let __proj__Mkfstar_option__item__opt_default : fstar_option  ->  FStar_Options.option_val = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_default
end))


let __proj__Mkfstar_option__item__opt_type : fstar_option  ->  FStar_Options.opt_type = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_type
end))


let __proj__Mkfstar_option__item__opt_snippets : fstar_option  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_snippets
end))


let __proj__Mkfstar_option__item__opt_documentation : fstar_option  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_documentation
end))


let __proj__Mkfstar_option__item__opt_permission_level : fstar_option  ->  fstar_option_permission_level = (fun projectee -> (match (projectee) with
| {opt_name = __fname__opt_name; opt_sig = __fname__opt_sig; opt_value = __fname__opt_value; opt_default = __fname__opt_default; opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets; opt_documentation = __fname__opt_documentation; opt_permission_level = __fname__opt_permission_level} -> begin
__fname__opt_permission_level
end))


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___243_3264 -> (match (uu___243_3264) with
| FStar_Options.Const (uu____3265) -> begin
"flag"
end
| FStar_Options.IntStr (uu____3266) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____3267) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____3268) -> begin
"string"
end
| FStar_Options.EnumStr (uu____3269) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____3272) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____3279, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____3287, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let rec snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.strcat "${" (Prims.strcat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.strcat "--" (Prims.strcat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.strcat " " argstring)
end
| uu____3314 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____3323) -> begin
("")::[]
end
| FStar_Options.BoolStr -> begin
("true")::("false")::[]
end
| FStar_Options.IntStr (desc) -> begin
((mk_field desc))::[]
end
| FStar_Options.PathStr (desc) -> begin
((mk_field desc))::[]
end
| FStar_Options.SimpleStr (desc) -> begin
((mk_field desc))::[]
end
| FStar_Options.EnumStr (strs) -> begin
strs
end
| FStar_Options.OpenEnumStr (strs, desc) -> begin
(FStar_List.append strs (((mk_field desc))::[]))
end
| FStar_Options.PostProcessed (uu____3336, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____3344, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____3350 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____3350))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___244_3356 -> (match (uu___244_3356) with
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

let uu____3364 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____3364))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____3377 = (

let uu____3384 = (

let uu____3391 = (

let uu____3396 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____3396)))
in (

let uu____3397 = (

let uu____3404 = (

let uu____3409 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____3409)))
in (

let uu____3410 = (

let uu____3417 = (

let uu____3422 = (json_of_opt (fun _0_47 -> FStar_Util.JsonStr (_0_47)) opt.opt_documentation)
in (("documentation"), (uu____3422)))
in (

let uu____3423 = (

let uu____3430 = (

let uu____3435 = (

let uu____3436 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____3436))
in (("type"), (uu____3435)))
in (uu____3430)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____3417)::uu____3423))
in (uu____3404)::uu____3410))
in (uu____3391)::uu____3397))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____3384)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____3377))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____3473 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____3473)))


let write_json : FStar_Util.json  ->  Prims.unit = (fun json -> ((

let uu____3485 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____3485));
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


let write_hello : Prims.unit  ->  Prims.unit = (fun uu____3547 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3550 = (FStar_List.map (fun _0_48 -> FStar_Util.JsonStr (_0_48)) interactive_protocol_features)
in FStar_Util.JsonList (uu____3550))
in (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info))))))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.strcat "--" name)
in (

let uu____3566 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____3566) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.strcat flag (Prims.strcat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____3575 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____3604 -> (match (uu____3604) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____3619 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____3619 (FStar_Util.map_option (fun default_value -> (

let uu____3631 = (sig_of_fstar_option name typ)
in (

let uu____3632 = (snippets_of_fstar_option name typ)
in (

let uu____3635 = (

let uu____3636 = (FStar_Options.settable name)
in (match (uu____3636) with
| true -> begin
OptSet
end
| uu____3637 -> begin
(

let uu____3638 = (FStar_Options.resettable name)
in (match (uu____3638) with
| true -> begin
OptReset
end
| uu____3639 -> begin
OptReadOnly
end))
end))
in {opt_name = name; opt_sig = uu____3631; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____3632; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3642 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____3635})))))))
end))))
in (FStar_All.pipe_right uu____3575 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___256_3663 = opt
in (

let uu____3664 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___256_3663.opt_name; opt_sig = uu___256_3663.opt_sig; opt_value = uu____3664; opt_default = uu___256_3663.opt_default; opt_type = uu___256_3663.opt_type; opt_snippets = uu___256_3663.opt_snippets; opt_documentation = uu___256_3663.opt_documentation; opt_permission_level = uu___256_3663.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____3676 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____3676)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____3692 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____3692)))
end
| uu____3693 -> begin
((""), (opt_name))
end)))

type repl_state =
{repl_line : Prims.int; repl_column : Prims.int; repl_fname : Prims.string; repl_deps : (deps_stack_t * m_timestamps); repl_curmod : modul_t; repl_env : env_t; repl_stdin : FStar_Util.stream_reader; repl_names : FStar_Interactive_CompletionTable.table}


let __proj__Mkrepl_state__item__repl_line : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_line
end))


let __proj__Mkrepl_state__item__repl_column : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_column
end))


let __proj__Mkrepl_state__item__repl_fname : repl_state  ->  Prims.string = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_fname
end))


let __proj__Mkrepl_state__item__repl_deps : repl_state  ->  (deps_stack_t * m_timestamps) = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_deps
end))


let __proj__Mkrepl_state__item__repl_curmod : repl_state  ->  modul_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_curmod
end))


let __proj__Mkrepl_state__item__repl_env : repl_state  ->  env_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_env
end))


let __proj__Mkrepl_state__item__repl_stdin : repl_state  ->  FStar_Util.stream_reader = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_stdin
end))


let __proj__Mkrepl_state__item__repl_names : repl_state  ->  FStar_Interactive_CompletionTable.table = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps = __fname__repl_deps; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_names
end))


let repl_stack : repl_state Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let repl_stack_empty : Prims.unit  ->  Prims.bool = (fun uu____3882 -> (

let uu____3883 = (FStar_ST.op_Bang repl_stack)
in (match (uu____3883) with
| [] -> begin
true
end
| uu____3936 -> begin
false
end)))


let pop_repl : 'Auu____3943 . ('Auu____3943 * FStar_TypeChecker_Env.env)  ->  repl_state = (fun env -> (

let uu____3956 = (FStar_ST.op_Bang repl_stack)
in (match (uu____3956) with
| [] -> begin
(failwith "Too many pops")
end
| (st')::stack -> begin
((pop env "#pop");
(FStar_ST.op_Colon_Equals repl_stack stack);
(

let uu____4066 = (repl_stack_empty ())
in (match (uu____4066) with
| true -> begin
(cleanup st'.repl_env)
end
| uu____4067 -> begin
()
end));
st';
)
end)))


let push_repl : push_kind  ->  repl_state  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun push_kind st -> ((

let uu____4081 = (

let uu____4084 = (FStar_ST.op_Bang repl_stack)
in (st)::uu____4084)
in (FStar_ST.op_Colon_Equals repl_stack uu____4081));
(

let uu____4187 = (set_check_kind st.repl_env push_kind)
in (push uu____4187 ""));
))


let json_of_repl_state : repl_state  ->  FStar_Util.json = (fun st -> (

let uu____4196 = (

let uu____4203 = (

let uu____4208 = (

let uu____4209 = (FStar_List.map (fun uu____4229 -> (match (uu____4229) with
| (uu____4242, fstname, uu____4244, uu____4245) -> begin
FStar_Util.JsonStr (fstname)
end)) (FStar_Pervasives_Native.snd st.repl_deps))
in FStar_Util.JsonList (uu____4209))
in (("loaded-dependencies"), (uu____4208)))
in (

let uu____4254 = (

let uu____4261 = (

let uu____4266 = (

let uu____4267 = (

let uu____4270 = (current_fstar_options (fun uu____4275 -> true))
in (FStar_List.map json_of_fstar_option uu____4270))
in FStar_Util.JsonList (uu____4267))
in (("options"), (uu____4266)))
in (uu____4261)::[])
in (uu____4203)::uu____4254))
in FStar_Util.JsonAssoc (uu____4196)))


let with_printed_effect_args : 'Auu____4292 . (Prims.unit  ->  'Auu____4292)  ->  'Auu____4292 = (fun k -> (FStar_Options.with_saved_options (fun uu____4304 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____4315 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____4321 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____4328 'Auu____4329 . 'Auu____4329  ->  ((query_status * FStar_Util.json) * ('Auu____4328, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____4360 'Auu____4361 . 'Auu____4361  ->  ((query_status * FStar_Util.json) * ('Auu____4361, 'Auu____4360) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____4390 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4390) FStar_Util.either) = (fun st -> (

let uu____4407 = (

let uu____4412 = (json_of_repl_state st)
in ((QueryOK), (uu____4412)))
in ((uu____4407), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____4429 'Auu____4430 . 'Auu____4430  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____4430, 'Auu____4429) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_missing_current_module : 'Auu____4469 'Auu____4470 'Auu____4471 . 'Auu____4471  ->  'Auu____4470  ->  ((query_status * FStar_Util.json) * ('Auu____4471, 'Auu____4469) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))), (FStar_Util.Inl (st))))


let run_pop : 'Auu____4504 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4504) FStar_Util.either) = (fun st -> (

let uu____4521 = (repl_stack_empty ())
in (match (uu____4521) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____4542 -> begin
(

let uu____4543 = (

let uu____4548 = (pop_repl st.repl_env)
in FStar_Util.Inl (uu____4548))
in ((((QueryOK), (FStar_Util.JsonNull))), (uu____4543)))
end)))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_ToSyntax_Env.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of FStar_TypeChecker_Env.binding


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____4598 -> begin
false
end))


let __proj__NTAlias__item___0 : name_tracking_event  ->  (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
_0
end))


let uu___is_NTOpen : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTOpen (_0) -> begin
true
end
| uu____4634 -> begin
false
end))


let __proj__NTOpen__item___0 : name_tracking_event  ->  (FStar_Ident.lid * FStar_ToSyntax_Env.open_module_or_namespace) = (fun projectee -> (match (projectee) with
| NTOpen (_0) -> begin
_0
end))


let uu___is_NTInclude : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTInclude (_0) -> begin
true
end
| uu____4664 -> begin
false
end))


let __proj__NTInclude__item___0 : name_tracking_event  ->  (FStar_Ident.lid * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| NTInclude (_0) -> begin
_0
end))


let uu___is_NTBinding : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTBinding (_0) -> begin
true
end
| uu____4690 -> begin
false
end))


let __proj__NTBinding__item___0 : name_tracking_event  ->  FStar_TypeChecker_Env.binding = (fun projectee -> (match (projectee) with
| NTBinding (_0) -> begin
_0
end))


let query_of_ids : FStar_Ident.ident Prims.list  ->  FStar_Interactive_CompletionTable.query = (fun ids -> (FStar_List.map FStar_Ident.text_of_id ids))


let query_of_lid : FStar_Ident.lident  ->  FStar_Interactive_CompletionTable.query = (fun lid -> (query_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))


let update_names_from_event : Prims.string  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod_str table evt -> (

let is_cur_mod = (fun lid -> (Prims.op_Equality lid.FStar_Ident.str cur_mod_str))
in (match (evt) with
| NTAlias (host, id, included) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____4730 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table (FStar_Ident.text_of_id id) [] uu____4730))
end
| uu____4731 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____4739 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_ToSyntax_Env.Open_module) [] uu____4739))
end
| uu____4740 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____4743 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____4744 -> begin
(query_of_lid host)
end)
in (

let uu____4745 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____4743 uu____4745)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_TypeChecker_Env.Binding_lid (lid, uu____4753) -> begin
(lid)::[]
end
| FStar_TypeChecker_Env.Binding_sig (lids, uu____4755) -> begin
lids
end
| FStar_TypeChecker_Env.Binding_sig_inst (lids, uu____4761, uu____4762) -> begin
lids
end
| uu____4767 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____4778 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (FStar_Interactive_CompletionTable.insert tbl ns_query (FStar_Ident.text_of_id lid.FStar_Ident.ident) lid))) table lids))
end)))


let commit_name_tracking : modul_t  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____4797 = (FStar_Syntax_Syntax.mod_name md)
in uu____4797.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let fresh_name_tracking_hooks : Prims.unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_ToSyntax_Env.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____4816 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____4828 = (

let uu____4831 = (FStar_ST.op_Bang events)
in (evt)::uu____4831)
in (FStar_ST.op_Colon_Equals events uu____4828)))
in ((events), ({FStar_ToSyntax_Env.ds_push_open_hook = (fun dsenv op -> (

let uu____4988 = (

let uu____4989 = (

let uu____4994 = (FStar_ToSyntax_Env.current_module dsenv)
in ((uu____4994), (op)))
in NTOpen (uu____4989))
in (push_event uu____4988))); FStar_ToSyntax_Env.ds_push_include_hook = (fun dsenv ns -> (

let uu____5000 = (

let uu____5001 = (

let uu____5006 = (FStar_ToSyntax_Env.current_module dsenv)
in ((uu____5006), (ns)))
in NTInclude (uu____5001))
in (push_event uu____5000))); FStar_ToSyntax_Env.ds_push_module_abbrev_hook = (fun dsenv x l -> (

let uu____5014 = (

let uu____5015 = (

let uu____5022 = (FStar_ToSyntax_Env.current_module dsenv)
in ((uu____5022), (x), (l)))
in NTAlias (uu____5015))
in (push_event uu____5014)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____5027 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : env_t  ->  (env_t * (env_t  ->  (env_t * name_tracking_event Prims.list))) = (fun uu____5044 -> (match (uu____5044) with
| (dsenv, tcenv) -> begin
(

let uu____5071 = (

let uu____5076 = (FStar_ToSyntax_Env.ds_hooks dsenv)
in (

let uu____5077 = (FStar_TypeChecker_Env.tc_hooks tcenv)
in ((uu____5076), (uu____5077))))
in (match (uu____5071) with
| (dsenv_old_hooks, tcenv_old_hooks) -> begin
(

let uu____5092 = (fresh_name_tracking_hooks ())
in (match (uu____5092) with
| (events, dsenv_new_hooks, tcenv_new_hooks) -> begin
(

let uu____5126 = (

let uu____5131 = (FStar_ToSyntax_Env.set_ds_hooks dsenv dsenv_new_hooks)
in (

let uu____5132 = (FStar_TypeChecker_Env.set_tc_hooks tcenv tcenv_new_hooks)
in ((uu____5131), (uu____5132))))
in ((uu____5126), ((fun uu____5158 -> (match (uu____5158) with
| (dsenv1, tcenv1) -> begin
(

let uu____5175 = (

let uu____5180 = (FStar_ToSyntax_Env.set_ds_hooks dsenv1 dsenv_old_hooks)
in (

let uu____5181 = (FStar_TypeChecker_Env.set_tc_hooks tcenv1 tcenv_old_hooks)
in ((uu____5180), (uu____5181))))
in (

let uu____5182 = (

let uu____5185 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____5185))
in ((uu____5175), (uu____5182))))
end)))))
end))
end))
end))


let run_push : 'Auu____5272 . repl_state  ->  push_kind  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5272) FStar_Util.either) = (fun st kind text1 line column peek_only -> (

let env = (push_repl kind st)
in (

let uu____5314 = (track_name_changes env)
in (match (uu____5314) with
| (env1, finish_name_tracking) -> begin
(

let uu____5357 = (

let uu____5370 = (repl_stack_empty ())
in (match (uu____5370) with
| true -> begin
(

let uu____5383 = (update_deps st.repl_fname env1 st.repl_deps)
in ((true), (uu____5383)))
end
| uu____5400 -> begin
((false), (((env1), (st.repl_deps))))
end))
in (match (uu____5357) with
| (restore_cmd_line_options1, (env2, deps)) -> begin
((match (restore_cmd_line_options1) with
| true -> begin
(

let uu____5445 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____5445 FStar_Pervasives.ignore))
end
| uu____5446 -> begin
()
end);
(

let frag = {FStar_Parser_ParseIt.frag_text = text1; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in (

let res = (check_frag env2 st.repl_curmod ((frag), (false)))
in (

let errors = (

let uu____5466 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____5466 (FStar_List.map json_of_issue)))
in ((FStar_Errors.clear ());
(

let st' = (

let uu___257_5475 = st
in {repl_line = line; repl_column = column; repl_fname = uu___257_5475.repl_fname; repl_deps = deps; repl_curmod = uu___257_5475.repl_curmod; repl_env = uu___257_5475.repl_env; repl_stdin = uu___257_5475.repl_stdin; repl_names = uu___257_5475.repl_names})
in (match (res) with
| FStar_Pervasives_Native.Some (curmod, env3, nerrs) when ((Prims.op_Equality nerrs (Prims.parse_int "0")) && (Prims.op_Equality peek_only false)) -> begin
(

let uu____5515 = (finish_name_tracking env3)
in (match (uu____5515) with
| (env4, name_events) -> begin
(

let uu____5540 = (

let uu____5545 = (

let uu___258_5546 = st'
in (

let uu____5547 = (commit_name_tracking curmod st'.repl_names name_events)
in {repl_line = uu___258_5546.repl_line; repl_column = uu___258_5546.repl_column; repl_fname = uu___258_5546.repl_fname; repl_deps = uu___258_5546.repl_deps; repl_curmod = curmod; repl_env = env4; repl_stdin = uu___258_5546.repl_stdin; repl_names = uu____5547}))
in FStar_Util.Inl (uu____5545))
in ((((QueryOK), (FStar_Util.JsonList (errors)))), (uu____5540)))
end))
end
| uu____5556 -> begin
(

let uu____5571 = (finish_name_tracking env2)
in (match (uu____5571) with
| (env3, uu____5591) -> begin
(

let uu____5596 = (run_pop (

let uu___259_5610 = st'
in {repl_line = uu___259_5610.repl_line; repl_column = uu___259_5610.repl_column; repl_fname = uu___259_5610.repl_fname; repl_deps = uu___259_5610.repl_deps; repl_curmod = uu___259_5610.repl_curmod; repl_env = env3; repl_stdin = uu___259_5610.repl_stdin; repl_names = uu___259_5610.repl_names}))
in (match (uu____5596) with
| (uu____5623, st'') -> begin
(

let status = (match (peek_only) with
| true -> begin
QueryOK
end
| uu____5642 -> begin
QueryNOK
end)
in ((((status), (FStar_Util.JsonList (errors)))), (st'')))
end))
end))
end));
))));
)
end))
end))))


let run_symbol_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____5701 = st.repl_env
in (match (uu____5701) with
| (dsenv, tcenv) -> begin
(

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____5735 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____5735))
in (

let lid1 = (

let uu____5739 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____5739))
in (

let uu____5744 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____5744 (FStar_Util.map_option (fun uu____5799 -> (match (uu____5799) with
| ((uu____5818, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____5835 = (FStar_ToSyntax_Env.try_lookup_doc dsenv lid)
in (FStar_All.pipe_right uu____5835 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____5864 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____5864 (fun uu___245_5908 -> (match (uu___245_5908) with
| (FStar_Util.Inr (se, uu____5930), uu____5931) -> begin
(

let uu____5960 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____5960))
end
| uu____5961 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____6013 -> (match (uu____6013) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____6060) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6113 -> begin
(info_of_lid_str symbol)
end)
end)
in (

let response = (match (info_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
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

let uu____6188 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____6188))
end
| uu____6189 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____6196 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____6207 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____6217 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {slr_name = name; slr_def_range = def_range; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}
in (

let uu____6219 = (

let uu____6230 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____6230)))
in FStar_Pervasives_Native.Some (uu____6219))))))))
end)
in (match (response) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (info) -> begin
FStar_Util.Inr (info)
end)))))))
end)))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____6336 = (trim_option_name opt_name)
in (match (uu____6336) with
| (uu____6355, trimmed_name) -> begin
(

let uu____6357 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____6357) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.strcat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____6385 = (

let uu____6396 = (

let uu____6403 = (update_option opt)
in (alist_of_fstar_option uu____6403))
in (("option"), (uu____6396)))
in FStar_Util.Inr (uu____6385))
end))
end)))


let run_module_lookup : repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____6445 = (FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names query)
in (match (uu____6445) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____6473 = (

let uu____6484 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____6484)))
in FStar_Util.Inr (uu____6473))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____6508 = (

let uu____6519 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____6519)))
in FStar_Util.Inr (uu____6508))
end))))


let run_code_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____6592 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____6592) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____6652) -> begin
(

let uu____6663 = (run_module_lookup st symbol)
in (match (uu____6663) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (err_msg) -> begin
FStar_Util.Inl ("No such symbol, module, or namespace.")
end))
end)))


let run_lookup' : repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol context pos_opt requested_info -> (match (context) with
| LKSymbolOnly -> begin
(run_symbol_lookup st symbol pos_opt requested_info)
end
| LKModule -> begin
(run_module_lookup st symbol)
end
| LKOption -> begin
(run_option_lookup symbol)
end
| LKCode -> begin
(run_code_lookup st symbol pos_opt requested_info)
end))


let run_lookup : 'Auu____6824 . repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6824) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____6877 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____6877) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let code_autocomplete_mod_filter : 'Auu____6963 . ('Auu____6963 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____6963 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___246_6977 -> (match (uu___246_6977) with
| (uu____6982, FStar_Interactive_CompletionTable.Namespace (uu____6983)) -> begin
FStar_Pervasives_Native.None
end
| (uu____6988, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____6989; FStar_Interactive_CompletionTable.mod_path = uu____6990; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____6997 = (

let uu____7002 = (

let uu____7003 = (

let uu___260_7004 = md
in (

let uu____7005 = (

let uu____7006 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.strcat uu____7006 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____7005; FStar_Interactive_CompletionTable.mod_path = uu___260_7004.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___260_7004.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____7003))
in ((pth), (uu____7002)))
in FStar_Pervasives_Native.Some (uu____6997))
end))


let run_code_autocomplete : 'Auu____7017 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7017) FStar_Util.either) = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names needle)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result (FStar_List.append lids mods_and_nss))
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st))))))))


let run_module_autocomplete : 'Auu____7072 'Auu____7073 'Auu____7074 . repl_state  ->  Prims.string  ->  'Auu____7074  ->  'Auu____7073  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7072) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle (fun _0_49 -> FStar_Pervasives_Native.Some (_0_49)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : Prims.int  ->  Prims.bool  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____7138 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReset -> begin
((is_reset), ("#reset-only"))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____7138) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____7153 -> begin
(Prims.strcat "(" (Prims.strcat explanation (Prims.strcat " " (Prims.strcat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____7170 'Auu____7171 . 'Auu____7171  ->  Prims.string  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * ('Auu____7171, 'Auu____7170) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____7196 = (trim_option_name search_term)
in (match (uu____7196) with
| ("--", trimmed_name) -> begin
(

let matcher = (fun opt -> (FStar_Util.starts_with opt.opt_name trimmed_name))
in (

let options = (current_fstar_options matcher)
in (

let match_len = (FStar_String.length search_term)
in (

let collect_candidates = (candidates_of_fstar_option match_len is_reset)
in (

let results = (FStar_List.concatMap collect_candidates options)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result results)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))))
end
| (uu____7247, uu____7248) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____7265 . repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7265) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_compute : 'Auu____7301 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7301) FStar_Util.either) = (fun st term rules -> (

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
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____7428, ({FStar_Syntax_Syntax.lbname = uu____7429; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____7431; FStar_Syntax_Syntax.lbeff = uu____7432; FStar_Syntax_Syntax.lbdef = def})::[]), uu____7434); FStar_Syntax_Syntax.sigrng = uu____7435; FStar_Syntax_Syntax.sigquals = uu____7436; FStar_Syntax_Syntax.sigmeta = uu____7437; FStar_Syntax_Syntax.sigattrs = uu____7438})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____7477 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____7496 = (FStar_Parser_ParseIt.parse (FStar_Util.Inr (frag)))
in (match (uu____7496) with
| FStar_Util.Inl (FStar_Util.Inr (decls), uu____7520) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____7565 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun dsenv decls -> (

let uu____7597 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv decls)
in (FStar_Pervasives_Native.snd uu____7597)))
in (

let typecheck = (fun tcenv decls -> (

let uu____7615 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____7615) with
| (ses, uu____7629, uu____7630) -> begin
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

let uu____7658 = st1.repl_env
in (match (uu____7658) with
| (dsenv, tcenv) -> begin
(

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____7670 -> begin
(

let uu____7671 = (parse1 frag)
in (match (uu____7671) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____7694 -> (

let decls1 = (desugar dsenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____7729 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____7729) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (

let normalized = (normalize_term1 tcenv1 rules1 def1)
in (

let uu____7742 = (

let uu____7743 = (term_to_string tcenv1 normalized)
in FStar_Util.JsonStr (uu____7743))
in ((QueryOK), (uu____7742)))))
end))
end))))
in (

let uu____7744 = (FStar_Options.trace_error ())
in (match (uu____7744) with
| true -> begin
(aux ())
end
| uu____7749 -> begin
(FStar_All.try_with (fun uu___262_7755 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___261_7763 -> (match (uu___261_7763) with
| e -> begin
(

let uu____7769 = (

let uu____7770 = (FStar_Errors.issue_of_exn e)
in (match (uu____7770) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____7774 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____7774))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise e)
end))
in ((QueryNOK), (uu____7769)))
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
| uu____7796 -> begin
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
| uu____7810 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___247_7834 -> (match (uu___247_7834) with
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

let uu____8002 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____8009 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____8002; sc_fvars = uu____8009})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____8058 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____8058) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____8115 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____8115) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____8136, typ), uu____8138) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____8214 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____8214) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____8285 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____8285))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun dsenv tcenv sc -> (

let typ_str = (

let uu____8356 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____8356))
in (

let uu____8357 = (

let uu____8364 = (

let uu____8369 = (

let uu____8370 = (

let uu____8371 = (FStar_ToSyntax_Env.shorten_lid dsenv sc.sc_lid)
in uu____8371.FStar_Ident.str)
in FStar_Util.JsonStr (uu____8370))
in (("lid"), (uu____8369)))
in (uu____8364)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____8357))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____8391) -> begin
true
end
| uu____8392 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____8400) -> begin
uu____8400
end))


let run_search : 'Auu____8407 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8407) FStar_Util.either) = (fun st search_str -> (

let uu____8428 = st.repl_env
in (match (uu____8428) with
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

let uu____8456 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____8456))
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
| uu____8471 -> begin
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
| uu____8478 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____8480 = (

let uu____8481 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____8481))
in (FStar_Exn.raise uu____8480))
end
| uu____8482 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____8483 = (strip_quotes term1)
in NameContainsStr (uu____8483))
end
| uu____8484 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____8486 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name dsenv lid)
in (match (uu____8486) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8489 = (

let uu____8490 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____8490))
in (FStar_Exn.raise uu____8489))
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

let uu____8506 = (match (term.st_term) with
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
| uu____8509 -> begin
""
end) uu____8506)))
in (

let results = (FStar_All.try_with (fun uu___264_8530 -> (match (()) with
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

let uu____8569 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____8569))
in (

let uu____8572 = (

let uu____8573 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____8573))
in (FStar_Exn.raise uu____8572)))
end
| uu____8578 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___263_8583 -> (match (uu___263_8583) with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end)))
in ((results), (FStar_Util.Inl (st))))))))
end)))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st uu___248_8629 -> (match (uu___248_8629) with
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
| AutoComplete (search_term, context) -> begin
(run_autocomplete st search_term context)
end
| Lookup (symbol, context, pos_opt, rq_info) -> begin
(run_lookup st symbol context pos_opt rq_info)
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
| Push (SyntaxCheck, uu____8681, uu____8682, uu____8683, false) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____8684 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = MissingCurrentModule; qid = q.qid}
end
| uu____8685 -> begin
q
end)
end))


let rec go : repl_state  ->  Prims.unit = (fun st -> (

let query = (

let uu____8691 = (read_interactive_query st.repl_stdin)
in (validate_query st uu____8691))
in (

let uu____8692 = (

let uu____8705 = (run_query st)
in (uu____8705 query.qq))
in (match (uu____8692) with
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

let uu____8749 = (

let uu____8752 = (FStar_ST.op_Bang issues)
in (e)::uu____8752)
in (FStar_ST.op_Colon_Equals issues uu____8749)))
in (

let count_errors = (fun uu____8886 -> (

let uu____8887 = (

let uu____8890 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____8890))
in (FStar_List.length uu____8887)))
in (

let report1 = (fun uu____8964 -> (

let uu____8965 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____8965)))
in (

let clear1 = (fun uu____9035 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report1; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (fun s -> (write_message "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (write_message "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (write_message "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label1 get_string get_json -> (

let uu____9122 = (get_json ())
in (write_message label1 uu____9122)))}


let capitalize : Prims.string  ->  Prims.string = (fun str -> (match ((Prims.op_Equality str "")) with
| true -> begin
str
end
| uu____9127 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____9129 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat (FStar_String.uppercase first) uu____9129)))
end))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____9156 = (FStar_Util.psmap_empty ())
in (

let uu____9159 = (

let uu____9162 = (FStar_Options.prims ())
in (uu____9162)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____9172 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____9172 true))) uu____9156 uu____9159)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____9188 -> (match (uu____9188) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____9196 -> begin
(

let ns_query = (

let uu____9200 = (capitalize modname)
in (FStar_Util.split uu____9200 "."))
in (

let uu____9201 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____9201 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods)))))))


let initial_range : FStar_Range.range = (

let uu____9206 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____9207 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____9206 uu____9207)))


let interactive_mode' : Prims.string  ->  Prims.unit = (fun filename -> ((write_hello ());
(

let env = (FStar_Universal.init_env ())
in (

let env1 = (

let uu____9223 = (FStar_TypeChecker_Env.set_range (FStar_Pervasives_Native.snd env) initial_range)
in (((FStar_Pervasives_Native.fst env)), (uu____9223)))
in (

let uu____9224 = (track_name_changes env1)
in (match (uu____9224) with
| (env2, finish_name_tracking) -> begin
(

let env3 = (tc_prims env2)
in (

let uu____9260 = (deps_of_our_file filename)
in (match (uu____9260) with
| (deps, maybe_inferface) -> begin
(

let uu____9279 = (tc_deps [] env3 deps [])
in (match (uu____9279) with
| (env4, repl_deps) -> begin
(

let env5 = (match (maybe_inferface) with
| FStar_Pervasives_Native.None -> begin
env4
end
| FStar_Pervasives_Native.Some (intf) -> begin
(FStar_Universal.load_interface_decls env4 intf)
end)
in (

let uu____9312 = (finish_name_tracking env5)
in (match (uu____9312) with
| (env6, name_events) -> begin
((FStar_TypeChecker_Env.toggle_id_info (FStar_Pervasives_Native.snd env6) true);
(

let initial_names = (add_module_completions filename deps FStar_Interactive_CompletionTable.empty)
in (

let init_st = (

let uu____9328 = (FStar_Util.open_stdin ())
in (

let uu____9329 = (commit_name_tracking FStar_Pervasives_Native.None initial_names name_events)
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_deps = repl_deps; repl_curmod = FStar_Pervasives_Native.None; repl_env = env6; repl_stdin = uu____9328; repl_names = uu____9329}))
in (

let uu____9330 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____9330) with
| true -> begin
(

let uu____9331 = (

let uu____9332 = (FStar_Options.file_list ())
in (FStar_List.hd uu____9332))
in (FStar_SMTEncoding_Solver.with_hints_db uu____9331 (fun uu____9336 -> (go init_st))))
end
| uu____9337 -> begin
(go init_st)
end))));
)
end)))
end))
end)))
end))));
))


let interactive_mode : Prims.string  ->  Prims.unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(

let uu____9344 = (

let uu____9345 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____9345))
in (match (uu____9344) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____9348 -> begin
()
end));
(

let uu____9349 = (FStar_Options.trace_error ())
in (match (uu____9349) with
| true -> begin
(interactive_mode' filename)
end
| uu____9350 -> begin
(FStar_All.try_with (fun uu___266_9353 -> (match (()) with
| () -> begin
((FStar_Errors.set_handler interactive_error_handler);
(interactive_mode' filename);
)
end)) (fun uu___265_9358 -> (match (uu___265_9358) with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise e);
)
end)))
end));
))




