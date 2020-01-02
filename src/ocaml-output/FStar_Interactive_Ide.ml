
open Prims
open FStar_Pervasives

let with_captured_errors' : 'Auu____28 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____28 FStar_Pervasives_Native.option)  ->  'Auu____28 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (FStar_All.try_with (fun uu___11_58 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler sigint_handler (fun uu____64 -> (f env)))
end)) (fun uu___10_69 -> (match (uu___10_69) with
| FStar_All.Failure (msg) -> begin
(

let msg1 = (Prims.op_Hat "ASSERTION FAILURE: " (Prims.op_Hat msg (Prims.op_Hat "\n" (Prims.op_Hat "F* may be in an inconsistent state.\n" (Prims.op_Hat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____82 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.log_issue uu____82 ((FStar_Errors.Error_IDEAssertionFailure), (msg1))));
FStar_Pervasives_Native.None;
))
end
| FStar_Util.SigInt -> begin
((FStar_Util.print_string "Interrupted");
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Error (e, msg, r) -> begin
((FStar_TypeChecker_Err.add_errors env ((((e), (msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (e, msg) -> begin
((

let uu____112 = (

let uu____122 = (

let uu____130 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____130)))
in (uu____122)::[])
in (FStar_TypeChecker_Err.add_errors env uu____112));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Stop -> begin
FStar_Pervasives_Native.None
end))))


let with_captured_errors : 'Auu____155 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____155 FStar_Pervasives_Native.option)  ->  'Auu____155 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (

let uu____182 = (FStar_Options.trace_error ())
in (match (uu____182) with
| true -> begin
(f env)
end
| uu____187 -> begin
(with_captured_errors' env sigint_handler f)
end)))


let t0 : FStar_Util.time = (FStar_Util.now ())


let dummy_tf_of_fname : Prims.string  ->  FStar_Interactive_JsonHelper.timed_fname = (fun fname -> {FStar_Interactive_JsonHelper.tf_fname = fname; FStar_Interactive_JsonHelper.tf_modtime = t0})


let string_of_timed_fname : FStar_Interactive_JsonHelper.timed_fname  ->  Prims.string = (fun uu____204 -> (match (uu____204) with
| {FStar_Interactive_JsonHelper.tf_fname = fname; FStar_Interactive_JsonHelper.tf_modtime = modtime} -> begin
(match ((Prims.op_Equality modtime t0)) with
| true -> begin
(FStar_Util.format1 "{ %s }" fname)
end
| uu____212 -> begin
(

let uu____214 = (FStar_Util.string_of_time modtime)
in (FStar_Util.format2 "{ %s; %s }" fname uu____214))
end)
end))

type push_query =
{push_kind : FStar_Interactive_PushHelper.push_kind; push_code : Prims.string; push_line : Prims.int; push_column : Prims.int; push_peek_only : Prims.bool}


let __proj__Mkpush_query__item__push_kind : push_query  ->  FStar_Interactive_PushHelper.push_kind = (fun projectee -> (match (projectee) with
| {push_kind = push_kind; push_code = push_code; push_line = push_line; push_column = push_column; push_peek_only = push_peek_only} -> begin
push_kind
end))


let __proj__Mkpush_query__item__push_code : push_query  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push_kind = push_kind; push_code = push_code; push_line = push_line; push_column = push_column; push_peek_only = push_peek_only} -> begin
push_code
end))


let __proj__Mkpush_query__item__push_line : push_query  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push_kind = push_kind; push_code = push_code; push_line = push_line; push_column = push_column; push_peek_only = push_peek_only} -> begin
push_line
end))


let __proj__Mkpush_query__item__push_column : push_query  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push_kind = push_kind; push_code = push_code; push_line = push_line; push_column = push_column; push_peek_only = push_peek_only} -> begin
push_column
end))


let __proj__Mkpush_query__item__push_peek_only : push_query  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {push_kind = push_kind; push_code = push_code; push_line = push_line; push_column = push_column; push_peek_only = push_peek_only} -> begin
push_peek_only
end))


type env_t =
FStar_TypeChecker_Env.env


let repl_current_qid : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let nothing_left_to_pop : FStar_Interactive_JsonHelper.repl_state  ->  Prims.bool = (fun st -> (

let uu____346 = (

let uu____347 = (FStar_ST.op_Bang FStar_Interactive_PushHelper.repl_stack)
in (FStar_List.length uu____347))
in (Prims.op_Equality uu____346 (FStar_List.length st.FStar_Interactive_JsonHelper.repl_deps_stack))))


let string_of_repl_task : FStar_Interactive_JsonHelper.repl_task  ->  Prims.string = (fun uu___0_399 -> (match (uu___0_399) with
| FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) -> begin
(

let uu____403 = (string_of_timed_fname intf)
in (

let uu____405 = (string_of_timed_fname impl)
in (FStar_Util.format2 "LDInterleaved (%s, %s)" uu____403 uu____405)))
end
| FStar_Interactive_JsonHelper.LDSingle (intf_or_impl) -> begin
(

let uu____409 = (string_of_timed_fname intf_or_impl)
in (FStar_Util.format1 "LDSingle %s" uu____409))
end
| FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____413 = (string_of_timed_fname intf)
in (FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____413))
end
| FStar_Interactive_JsonHelper.PushFragment (frag) -> begin
(FStar_Util.format1 "PushFragment { code = %s }" frag.FStar_Parser_ParseIt.frag_text)
end
| FStar_Interactive_JsonHelper.Noop -> begin
"Noop {}"
end))


let run_repl_transaction : FStar_Interactive_JsonHelper.repl_state  ->  FStar_Interactive_PushHelper.push_kind  ->  Prims.bool  ->  FStar_Interactive_JsonHelper.repl_task  ->  (Prims.bool * FStar_Interactive_JsonHelper.repl_state) = (fun st push_kind must_rollback task -> (

let st1 = (FStar_Interactive_PushHelper.push_repl "run_repl_transaction" push_kind task st)
in (

let uu____449 = (FStar_Interactive_PushHelper.track_name_changes st1.FStar_Interactive_JsonHelper.repl_env)
in (match (uu____449) with
| (env, finish_name_tracking) -> begin
(

let check_success = (fun uu____494 -> ((

let uu____497 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____497 (Prims.parse_int "0"))) && (not (must_rollback))))
in (

let uu____501 = (

let uu____509 = (with_captured_errors env FStar_Util.sigint_raise (fun env1 -> (

let uu____523 = (FStar_Interactive_PushHelper.run_repl_task st1.FStar_Interactive_JsonHelper.repl_curmod env1 task)
in (FStar_All.pipe_left (fun _542 -> FStar_Pervasives_Native.Some (_542)) uu____523))))
in (match (uu____509) with
| FStar_Pervasives_Native.Some (curmod, env1) when (check_success ()) -> begin
((curmod), (env1), (true))
end
| uu____558 -> begin
((st1.FStar_Interactive_JsonHelper.repl_curmod), (env), (false))
end))
in (match (uu____501) with
| (curmod, env1, success) -> begin
(

let uu____577 = (finish_name_tracking env1)
in (match (uu____577) with
| (env2, name_events) -> begin
(

let st2 = (match (success) with
| true -> begin
(

let st2 = (

let uu___95_598 = st1
in {FStar_Interactive_JsonHelper.repl_line = uu___95_598.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___95_598.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___95_598.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___95_598.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = curmod; FStar_Interactive_JsonHelper.repl_env = env2; FStar_Interactive_JsonHelper.repl_stdin = uu___95_598.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___95_598.FStar_Interactive_JsonHelper.repl_names})
in (FStar_Interactive_PushHelper.commit_name_tracking st2 name_events))
end
| uu____599 -> begin
(FStar_Interactive_PushHelper.pop_repl "run_repl_transaction" st1)
end)
in ((success), (st2)))
end))
end)))
end))))


let run_repl_ld_transactions : FStar_Interactive_JsonHelper.repl_state  ->  FStar_Interactive_JsonHelper.repl_task Prims.list  ->  (FStar_Interactive_JsonHelper.repl_task  ->  unit)  ->  (FStar_Interactive_JsonHelper.repl_state, FStar_Interactive_JsonHelper.repl_state) FStar_Util.either = (fun st tasks progress_callback -> (

let debug1 = (fun verb task -> (

let uu____645 = (FStar_Options.debug_any ())
in (match (uu____645) with
| true -> begin
(

let uu____648 = (string_of_repl_task task)
in (FStar_Util.print2 "%s %s" verb uu____648))
end
| uu____651 -> begin
()
end)))
in (

let rec revert_many = (fun st1 uu___1_673 -> (match (uu___1_673) with
| [] -> begin
st1
end
| ((_id, (task, _st')))::entries -> begin
((debug1 "Reverting" task);
(

let st' = (FStar_Interactive_PushHelper.pop_repl "run_repl_ls_transactions" st1)
in (

let dep_graph1 = (FStar_TypeChecker_Env.dep_graph st1.FStar_Interactive_JsonHelper.repl_env)
in (

let st'1 = (

let uu___121_726 = st'
in (

let uu____727 = (FStar_TypeChecker_Env.set_dep_graph st'.FStar_Interactive_JsonHelper.repl_env dep_graph1)
in {FStar_Interactive_JsonHelper.repl_line = uu___121_726.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___121_726.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___121_726.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___121_726.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___121_726.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu____727; FStar_Interactive_JsonHelper.repl_stdin = uu___121_726.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___121_726.FStar_Interactive_JsonHelper.repl_names}))
in (revert_many st'1 entries))));
)
end))
in (

let rec aux = (fun st1 tasks1 previous -> (match (((tasks1), (previous))) with
| ([], []) -> begin
FStar_Util.Inl (st1)
end
| ((task)::tasks2, []) -> begin
((debug1 "Loading" task);
(progress_callback task);
(

let uu____780 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____780 (fun a1 -> ())));
(

let timestamped_task = (FStar_Interactive_PushHelper.update_task_timestamps task)
in (

let push_kind = (

let uu____784 = (FStar_Options.lax ())
in (match (uu____784) with
| true -> begin
FStar_Interactive_PushHelper.LaxCheck
end
| uu____787 -> begin
FStar_Interactive_PushHelper.FullCheck
end))
in (

let uu____789 = (run_repl_transaction st1 push_kind false timestamped_task)
in (match (uu____789) with
| (success, st2) -> begin
(match (success) with
| true -> begin
(

let uu____809 = (

let uu___146_810 = st2
in (

let uu____811 = (FStar_ST.op_Bang FStar_Interactive_PushHelper.repl_stack)
in {FStar_Interactive_JsonHelper.repl_line = uu___146_810.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___146_810.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___146_810.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu____811; FStar_Interactive_JsonHelper.repl_curmod = uu___146_810.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu___146_810.FStar_Interactive_JsonHelper.repl_env; FStar_Interactive_JsonHelper.repl_stdin = uu___146_810.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___146_810.FStar_Interactive_JsonHelper.repl_names}))
in (aux uu____809 tasks2 []))
end
| uu____841 -> begin
FStar_Util.Inr (st2)
end)
end))));
)
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____855 = (FStar_Interactive_PushHelper.update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev)) uu____855)) -> begin
((debug1 "Skipping" task);
(aux st1 tasks2 previous1);
)
end
| (tasks2, previous1) -> begin
(

let uu____872 = (revert_many st1 previous1)
in (aux uu____872 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack))))))


let js_pushkind : FStar_Util.json  ->  FStar_Interactive_PushHelper.push_kind = (fun s -> (

let uu____887 = (FStar_Interactive_JsonHelper.js_str s)
in (match (uu____887) with
| "syntax" -> begin
FStar_Interactive_PushHelper.SyntaxCheck
end
| "lax" -> begin
FStar_Interactive_PushHelper.LaxCheck
end
| "full" -> begin
FStar_Interactive_PushHelper.FullCheck
end
| uu____892 -> begin
(FStar_Interactive_JsonHelper.js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Env.step = (fun s -> (

let uu____901 = (FStar_Interactive_JsonHelper.js_str s)
in (match (uu____901) with
| "beta" -> begin
FStar_TypeChecker_Env.Beta
end
| "delta" -> begin
FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant)
end
| "iota" -> begin
FStar_TypeChecker_Env.Iota
end
| "zeta" -> begin
FStar_TypeChecker_Env.Zeta
end
| "reify" -> begin
FStar_TypeChecker_Env.Reify
end
| "pure-subterms" -> begin
FStar_TypeChecker_Env.PureSubtermsWithinComputations
end
| uu____909 -> begin
(FStar_Interactive_JsonHelper.js_fail "reduction rule" s)
end)))

type completion_context =
| CKCode
| CKOption of Prims.bool
| CKModuleOrNamespace of (Prims.bool * Prims.bool)


let uu___is_CKCode : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKCode -> begin
true
end
| uu____938 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____951 -> begin
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
| uu____979 -> begin
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

let uu____1017 = (FStar_Interactive_JsonHelper.js_str k1)
in (match (uu____1017) with
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
| uu____1045 -> begin
(FStar_Interactive_JsonHelper.js_fail "completion context (code, set-options, reset-options, open, let-open, include, module-alias)" k1)
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
| uu____1057 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____1068 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____1079 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____1090 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____1103 = (FStar_Interactive_JsonHelper.js_str k1)
in (match (uu____1103) with
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
| uu____1113 -> begin
(FStar_Interactive_JsonHelper.js_fail "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)" k1)
end))
end))


type position =
(Prims.string * Prims.int * Prims.int)

type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Segment of Prims.string
| Pop
| Push of push_query
| VfsAdd of (Prims.string FStar_Pervasives_Native.option * Prims.string)
| AutoComplete of (Prims.string * completion_context)
| Lookup of (Prims.string * lookup_context * position FStar_Pervasives_Native.option * Prims.string Prims.list)
| Compute of (Prims.string * FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option)
| Search of Prims.string
| GenericError of Prims.string
| ProtocolViolation of Prims.string 
 and query =
{qq : query'; qid : Prims.string}


let uu___is_Exit : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1230 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____1241 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____1252 -> begin
false
end))


let uu___is_Segment : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
true
end
| uu____1265 -> begin
false
end))


let __proj__Segment__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
_0
end))


let uu___is_Pop : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop -> begin
true
end
| uu____1286 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____1298 -> begin
false
end))


let __proj__Push__item___0 : query'  ->  push_query = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
_0
end))


let uu___is_VfsAdd : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VfsAdd (_0) -> begin
true
end
| uu____1325 -> begin
false
end))


let __proj__VfsAdd__item___0 : query'  ->  (Prims.string FStar_Pervasives_Native.option * Prims.string) = (fun projectee -> (match (projectee) with
| VfsAdd (_0) -> begin
_0
end))


let uu___is_AutoComplete : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AutoComplete (_0) -> begin
true
end
| uu____1373 -> begin
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
| uu____1421 -> begin
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
| uu____1491 -> begin
false
end))


let __proj__Compute__item___0 : query'  ->  (Prims.string * FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Compute (_0) -> begin
_0
end))


let uu___is_Search : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Search (_0) -> begin
true
end
| uu____1538 -> begin
false
end))


let __proj__Search__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| Search (_0) -> begin
_0
end))


let uu___is_GenericError : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| GenericError (_0) -> begin
true
end
| uu____1561 -> begin
false
end))


let __proj__GenericError__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| GenericError (_0) -> begin
_0
end))


let uu___is_ProtocolViolation : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
true
end
| uu____1584 -> begin
false
end))


let __proj__ProtocolViolation__item___0 : query'  ->  Prims.string = (fun projectee -> (match (projectee) with
| ProtocolViolation (_0) -> begin
_0
end))


let __proj__Mkquery__item__qq : query  ->  query' = (fun projectee -> (match (projectee) with
| {qq = qq; qid = qid} -> begin
qq
end))


let __proj__Mkquery__item__qid : query  ->  Prims.string = (fun projectee -> (match (projectee) with
| {qq = qq; qid = qid} -> begin
qid
end))


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___2_1622 -> (match (uu___2_1622) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Segment (uu____1627) -> begin
false
end
| Pop -> begin
false
end
| Push ({push_kind = uu____1631; push_code = uu____1632; push_line = uu____1633; push_column = uu____1634; push_peek_only = false}) -> begin
false
end
| VfsAdd (uu____1640) -> begin
false
end
| GenericError (uu____1650) -> begin
false
end
| ProtocolViolation (uu____1653) -> begin
false
end
| Push (uu____1656) -> begin
true
end
| AutoComplete (uu____1658) -> begin
true
end
| Lookup (uu____1665) -> begin
true
end
| Compute (uu____1681) -> begin
true
end
| Search (uu____1692) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::("segment")::("vfs-add")::("tactic-ranges")::("interrupt")::("progress")::[]

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____1754 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____1765 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____1776 -> begin
false
end))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____1798 = (

let uu____1799 = (

let uu____1801 = (FStar_Interactive_JsonHelper.json_debug got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____1801))
in ProtocolViolation (uu____1799))
in {qq = uu____1798; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____1830 = (FStar_Interactive_JsonHelper.try_assoc key a)
in (match (uu____1830) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1834 = (

let uu____1835 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in FStar_Interactive_JsonHelper.InvalidQuery (uu____1835))
in (FStar_Exn.raise uu____1834))
end)))
in (

let request = (FStar_All.pipe_right json FStar_Interactive_JsonHelper.js_assoc)
in (

let qid = (

let uu____1841 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____1841 FStar_Interactive_JsonHelper.js_str))
in (FStar_All.try_with (fun uu___259_1851 -> (match (()) with
| () -> begin
(

let query = (

let uu____1854 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____1854 FStar_Interactive_JsonHelper.js_str))
in (

let args = (

let uu____1859 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____1859 FStar_Interactive_JsonHelper.js_assoc))
in (

let arg1 = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____1881 = (FStar_Interactive_JsonHelper.try_assoc k args)
in (match (uu____1881) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____1889 = (match (query) with
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
| "segment" -> begin
(

let uu____1895 = (

let uu____1897 = (arg1 "code")
in (FStar_All.pipe_right uu____1897 FStar_Interactive_JsonHelper.js_str))
in Segment (uu____1895))
end
| "peek" -> begin
(

let uu____1901 = (

let uu____1902 = (

let uu____1903 = (arg1 "kind")
in (FStar_All.pipe_right uu____1903 js_pushkind))
in (

let uu____1905 = (

let uu____1907 = (arg1 "code")
in (FStar_All.pipe_right uu____1907 FStar_Interactive_JsonHelper.js_str))
in (

let uu____1910 = (

let uu____1912 = (arg1 "line")
in (FStar_All.pipe_right uu____1912 FStar_Interactive_JsonHelper.js_int))
in (

let uu____1915 = (

let uu____1917 = (arg1 "column")
in (FStar_All.pipe_right uu____1917 FStar_Interactive_JsonHelper.js_int))
in {push_kind = uu____1902; push_code = uu____1905; push_line = uu____1910; push_column = uu____1915; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____1901))
end
| "push" -> begin
(

let uu____1923 = (

let uu____1924 = (

let uu____1925 = (arg1 "kind")
in (FStar_All.pipe_right uu____1925 js_pushkind))
in (

let uu____1927 = (

let uu____1929 = (arg1 "code")
in (FStar_All.pipe_right uu____1929 FStar_Interactive_JsonHelper.js_str))
in (

let uu____1932 = (

let uu____1934 = (arg1 "line")
in (FStar_All.pipe_right uu____1934 FStar_Interactive_JsonHelper.js_int))
in (

let uu____1937 = (

let uu____1939 = (arg1 "column")
in (FStar_All.pipe_right uu____1939 FStar_Interactive_JsonHelper.js_int))
in {push_kind = uu____1924; push_code = uu____1927; push_line = uu____1932; push_column = uu____1937; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____1923))
end
| "autocomplete" -> begin
(

let uu____1945 = (

let uu____1951 = (

let uu____1953 = (arg1 "partial-symbol")
in (FStar_All.pipe_right uu____1953 FStar_Interactive_JsonHelper.js_str))
in (

let uu____1956 = (

let uu____1957 = (try_arg "context")
in (FStar_All.pipe_right uu____1957 js_optional_completion_context))
in ((uu____1951), (uu____1956))))
in AutoComplete (uu____1945))
end
| "lookup" -> begin
(

let uu____1965 = (

let uu____1980 = (

let uu____1982 = (arg1 "symbol")
in (FStar_All.pipe_right uu____1982 FStar_Interactive_JsonHelper.js_str))
in (

let uu____1985 = (

let uu____1986 = (try_arg "context")
in (FStar_All.pipe_right uu____1986 js_optional_lookup_context))
in (

let uu____1992 = (

let uu____1995 = (

let uu____1998 = (try_arg "location")
in (FStar_All.pipe_right uu____1998 (FStar_Util.map_option FStar_Interactive_JsonHelper.js_assoc)))
in (FStar_All.pipe_right uu____1995 (FStar_Util.map_option (fun loc -> (

let uu____2024 = (

let uu____2026 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____2026 FStar_Interactive_JsonHelper.js_str))
in (

let uu____2030 = (

let uu____2032 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____2032 FStar_Interactive_JsonHelper.js_int))
in (

let uu____2036 = (

let uu____2038 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____2038 FStar_Interactive_JsonHelper.js_int))
in ((uu____2024), (uu____2030), (uu____2036)))))))))
in (

let uu____2045 = (

let uu____2049 = (arg1 "requested-info")
in (FStar_All.pipe_right uu____2049 (FStar_Interactive_JsonHelper.js_list FStar_Interactive_JsonHelper.js_str)))
in ((uu____1980), (uu____1985), (uu____1992), (uu____2045))))))
in Lookup (uu____1965))
end
| "compute" -> begin
(

let uu____2062 = (

let uu____2072 = (

let uu____2074 = (arg1 "term")
in (FStar_All.pipe_right uu____2074 FStar_Interactive_JsonHelper.js_str))
in (

let uu____2077 = (

let uu____2082 = (try_arg "rules")
in (FStar_All.pipe_right uu____2082 (FStar_Util.map_option (FStar_Interactive_JsonHelper.js_list js_reductionrule))))
in ((uu____2072), (uu____2077))))
in Compute (uu____2062))
end
| "search" -> begin
(

let uu____2100 = (

let uu____2102 = (arg1 "terms")
in (FStar_All.pipe_right uu____2102 FStar_Interactive_JsonHelper.js_str))
in Search (uu____2100))
end
| "vfs-add" -> begin
(

let uu____2106 = (

let uu____2115 = (

let uu____2119 = (try_arg "filename")
in (FStar_All.pipe_right uu____2119 (FStar_Util.map_option FStar_Interactive_JsonHelper.js_str)))
in (

let uu____2129 = (

let uu____2131 = (arg1 "contents")
in (FStar_All.pipe_right uu____2131 FStar_Interactive_JsonHelper.js_str))
in ((uu____2115), (uu____2129))))
in VfsAdd (uu____2106))
end
| uu____2138 -> begin
(

let uu____2140 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____2140))
end)
in {qq = uu____1889; qid = qid})))))
end)) (fun uu___258_2145 -> (match (uu___258_2145) with
| FStar_Interactive_JsonHelper.InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let deserialize_interactive_query : FStar_Util.json  ->  query = (fun js_query -> (FStar_All.try_with (fun uu___294_2159 -> (match (()) with
| () -> begin
(unpack_interactive_query js_query)
end)) (fun uu___293_2162 -> (match (uu___293_2162) with
| FStar_Interactive_JsonHelper.InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| FStar_Interactive_JsonHelper.UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let parse_interactive_query : Prims.string  ->  query = (fun query_str -> (

let uu____2179 = (FStar_Util.json_of_string query_str)
in (match (uu____2179) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(deserialize_interactive_query request)
end)))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (

let uu____2191 = (FStar_Util.read_line stream)
in (match (uu____2191) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(parse_interactive_query line)
end)))


let json_of_opt : 'Auu____2207 . ('Auu____2207  ->  FStar_Util.json)  ->  'Auu____2207 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____2227 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____2227)))


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

let uu____2247 = (

let uu____2255 = (

let uu____2263 = (

let uu____2271 = (

let uu____2277 = (

let uu____2278 = (

let uu____2281 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____2287 = (FStar_Range.json_of_use_range r)
in (uu____2287)::[])
end)
in (

let uu____2288 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (

let uu____2294 = (FStar_Range.def_range r)
in (

let uu____2295 = (FStar_Range.use_range r)
in (Prims.op_disEquality uu____2294 uu____2295))) -> begin
(

let uu____2296 = (FStar_Range.json_of_def_range r)
in (uu____2296)::[])
end
| uu____2297 -> begin
[]
end)
in (FStar_List.append uu____2281 uu____2288)))
in FStar_Util.JsonList (uu____2278))
in (("ranges"), (uu____2277)))
in (uu____2271)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____2263)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____2255)
in FStar_Util.JsonAssoc (uu____2247)))


let alist_of_symbol_lookup_result : FStar_Interactive_QueryHelper.sl_reponse  ->  (Prims.string * FStar_Util.json) Prims.list = (fun lr -> (

let uu____2339 = (

let uu____2347 = (

let uu____2353 = (json_of_opt FStar_Range.json_of_def_range lr.FStar_Interactive_QueryHelper.slr_def_range)
in (("defined-at"), (uu____2353)))
in (

let uu____2356 = (

let uu____2364 = (

let uu____2370 = (json_of_opt (fun _2372 -> FStar_Util.JsonStr (_2372)) lr.FStar_Interactive_QueryHelper.slr_typ)
in (("type"), (uu____2370)))
in (

let uu____2375 = (

let uu____2383 = (

let uu____2389 = (json_of_opt (fun _2391 -> FStar_Util.JsonStr (_2391)) lr.FStar_Interactive_QueryHelper.slr_doc)
in (("documentation"), (uu____2389)))
in (

let uu____2394 = (

let uu____2402 = (

let uu____2408 = (json_of_opt (fun _2410 -> FStar_Util.JsonStr (_2410)) lr.FStar_Interactive_QueryHelper.slr_def)
in (("definition"), (uu____2408)))
in (uu____2402)::[])
in (uu____2383)::uu____2394))
in (uu____2364)::uu____2375))
in (uu____2347)::uu____2356))
in ((("name"), (FStar_Util.JsonStr (lr.FStar_Interactive_QueryHelper.slr_name))))::uu____2339))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____2455 = (FStar_List.map (fun _2459 -> FStar_Util.JsonStr (_2459)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _2462 -> FStar_Util.JsonList (_2462)) uu____2455))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____2491 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____2502 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___3_2510 -> (match (uu___3_2510) with
| OptSet -> begin
""
end
| OptReadOnly -> begin
"read-only"
end))

type fstar_option =
{opt_name : Prims.string; opt_sig : Prims.string; opt_value : FStar_Options.option_val; opt_default : FStar_Options.option_val; opt_type : FStar_Options.opt_type; opt_snippets : Prims.string Prims.list; opt_documentation : Prims.string FStar_Pervasives_Native.option; opt_permission_level : fstar_option_permission_level}


let __proj__Mkfstar_option__item__opt_name : fstar_option  ->  Prims.string = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_name
end))


let __proj__Mkfstar_option__item__opt_sig : fstar_option  ->  Prims.string = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_sig
end))


let __proj__Mkfstar_option__item__opt_value : fstar_option  ->  FStar_Options.option_val = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_value
end))


let __proj__Mkfstar_option__item__opt_default : fstar_option  ->  FStar_Options.option_val = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_default
end))


let __proj__Mkfstar_option__item__opt_type : fstar_option  ->  FStar_Options.opt_type = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_type
end))


let __proj__Mkfstar_option__item__opt_snippets : fstar_option  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_snippets
end))


let __proj__Mkfstar_option__item__opt_documentation : fstar_option  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_documentation
end))


let __proj__Mkfstar_option__item__opt_permission_level : fstar_option  ->  fstar_option_permission_level = (fun projectee -> (match (projectee) with
| {opt_name = opt_name; opt_sig = opt_sig; opt_value = opt_value; opt_default = opt_default; opt_type = opt_type; opt_snippets = opt_snippets; opt_documentation = opt_documentation; opt_permission_level = opt_permission_level} -> begin
opt_permission_level
end))


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___4_2760 -> (match (uu___4_2760) with
| FStar_Options.Const (uu____2762) -> begin
"flag"
end
| FStar_Options.IntStr (uu____2764) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____2768) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____2771) -> begin
"string"
end
| FStar_Options.EnumStr (uu____2774) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____2779) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____2789, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____2799, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.op_Hat "${" (Prims.op_Hat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.op_Hat "--" (Prims.op_Hat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.op_Hat " " argstring)
end
| uu____2856 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____2871) -> begin
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
| FStar_Options.PostProcessed (uu____2909, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____2919, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____2927 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____2927))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___5_2938 -> (match (uu___5_2938) with
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

let uu____2950 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____2950))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____2966 = (

let uu____2974 = (

let uu____2982 = (

let uu____2988 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____2988)))
in (

let uu____2991 = (

let uu____2999 = (

let uu____3005 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____3005)))
in (

let uu____3008 = (

let uu____3016 = (

let uu____3022 = (json_of_opt (fun _3024 -> FStar_Util.JsonStr (_3024)) opt.opt_documentation)
in (("documentation"), (uu____3022)))
in (

let uu____3027 = (

let uu____3035 = (

let uu____3041 = (

let uu____3042 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____3042))
in (("type"), (uu____3041)))
in (uu____3035)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____3016)::uu____3027))
in (uu____2999)::uu____3008))
in (uu____2982)::uu____2991))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____2974)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____2966))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____3098 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____3098)))


let json_of_response : Prims.string  ->  query_status  ->  FStar_Util.json  ->  FStar_Util.json = (fun qid status response -> (

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
in FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("response"))))::((("query-id"), (qid1)))::((("status"), (status1)))::((("response"), (response)))::[]))))


let write_response : Prims.string  ->  query_status  ->  FStar_Util.json  ->  unit = (fun qid status response -> (FStar_Interactive_JsonHelper.write_json (json_of_response qid status response)))


let json_of_message : Prims.string  ->  FStar_Util.json  ->  FStar_Util.json = (fun level js_contents -> (

let uu____3194 = (

let uu____3202 = (

let uu____3210 = (

let uu____3216 = (

let uu____3217 = (FStar_ST.op_Bang repl_current_qid)
in (json_of_opt (fun _3247 -> FStar_Util.JsonStr (_3247)) uu____3217))
in (("query-id"), (uu____3216)))
in (uu____3210)::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (js_contents)))::[])
in ((("kind"), (FStar_Util.JsonStr ("message"))))::uu____3202)
in FStar_Util.JsonAssoc (uu____3194)))


let forward_message : 'Auu____3291 . (FStar_Util.json  ->  'Auu____3291)  ->  Prims.string  ->  FStar_Util.json  ->  'Auu____3291 = (fun callback level contents -> (

let uu____3314 = (json_of_message level contents)
in (callback uu____3314)))


let json_of_hello : FStar_Util.json = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3318 = (FStar_List.map (fun _3322 -> FStar_Util.JsonStr (_3322)) interactive_protocol_features)
in FStar_Util.JsonList (uu____3318))
in FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info)))


let write_hello : unit  ->  unit = (fun uu____3336 -> (FStar_Interactive_JsonHelper.write_json json_of_hello))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.op_Hat "--" name)
in (

let uu____3354 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____3354) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.op_Hat flag (Prims.op_Hat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____3370 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____3405 -> (match (uu____3405) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____3429 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____3429 (FStar_Util.map_option (fun default_value -> (

let uu____3441 = (sig_of_fstar_option name typ)
in (

let uu____3443 = (snippets_of_fstar_option name typ)
in (

let uu____3447 = (

let uu____3448 = (FStar_Options.settable name)
in (match (uu____3448) with
| true -> begin
OptSet
end
| uu____3451 -> begin
OptReadOnly
end))
in {opt_name = name; opt_sig = uu____3441; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____3443; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____3460 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____3447})))))))
end))))
in (FStar_All.pipe_right uu____3370 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___464_3487 = opt
in (

let uu____3488 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___464_3487.opt_name; opt_sig = uu___464_3487.opt_sig; opt_value = uu____3488; opt_default = uu___464_3487.opt_default; opt_type = uu___464_3487.opt_type; opt_snippets = uu___464_3487.opt_snippets; opt_documentation = uu___464_3487.opt_documentation; opt_permission_level = uu___464_3487.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____3504 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____3504)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____3531 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____3531)))
end
| uu____3535 -> begin
((""), (opt_name))
end)))


let json_of_repl_state : FStar_Interactive_JsonHelper.repl_state  ->  FStar_Util.json = (fun st -> (

let filenames = (fun uu____3562 -> (match (uu____3562) with
| (uu____3574, (task, uu____3576)) -> begin
(match (task) with
| FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) -> begin
(intf.FStar_Interactive_JsonHelper.tf_fname)::(impl.FStar_Interactive_JsonHelper.tf_fname)::[]
end
| FStar_Interactive_JsonHelper.LDSingle (intf_or_impl) -> begin
(intf_or_impl.FStar_Interactive_JsonHelper.tf_fname)::[]
end
| FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (intf) -> begin
(intf.FStar_Interactive_JsonHelper.tf_fname)::[]
end
| uu____3595 -> begin
[]
end)
end))
in (

let uu____3597 = (

let uu____3605 = (

let uu____3611 = (

let uu____3612 = (

let uu____3615 = (FStar_List.concatMap filenames st.FStar_Interactive_JsonHelper.repl_deps_stack)
in (FStar_List.map (fun _3629 -> FStar_Util.JsonStr (_3629)) uu____3615))
in FStar_Util.JsonList (uu____3612))
in (("loaded-dependencies"), (uu____3611)))
in (

let uu____3632 = (

let uu____3640 = (

let uu____3646 = (

let uu____3647 = (

let uu____3650 = (current_fstar_options (fun uu____3655 -> true))
in (FStar_List.map json_of_fstar_option uu____3650))
in FStar_Util.JsonList (uu____3647))
in (("options"), (uu____3646)))
in (uu____3640)::[])
in (uu____3605)::uu____3632))
in FStar_Util.JsonAssoc (uu____3597))))


let run_exit : 'Auu____3681 'Auu____3682 . 'Auu____3681  ->  ((query_status * FStar_Util.json) * ('Auu____3682, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____3719 'Auu____3720 . 'Auu____3719  ->  ((query_status * FStar_Util.json) * ('Auu____3719, 'Auu____3720) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____3751 . FStar_Interactive_JsonHelper.repl_state  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____3751) FStar_Util.either) = (fun st -> (

let uu____3769 = (

let uu____3774 = (json_of_repl_state st)
in ((QueryOK), (uu____3774)))
in ((uu____3769), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____3792 'Auu____3793 . 'Auu____3792  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____3792, 'Auu____3793) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_generic_error : 'Auu____3835 'Auu____3836 . 'Auu____3835  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____3835, 'Auu____3836) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let collect_errors : unit  ->  FStar_Errors.issue Prims.list = (fun uu____3876 -> (

let errors = (FStar_Errors.report_all ())
in ((FStar_Errors.clear ());
errors;
)))


let run_segment : 'Auu____3888 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____3888) FStar_Util.either) = (fun st code -> (

let frag = {FStar_Parser_ParseIt.frag_fname = "<input>"; FStar_Parser_ParseIt.frag_text = code; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let collect_decls = (fun uu____3924 -> (

let uu____3925 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____3925) with
| FStar_Parser_Driver.Empty -> begin
[]
end
| FStar_Parser_Driver.Decls (decls) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu____3931, decls)) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface (uu____3937, decls, uu____3939)) -> begin
decls
end)))
in (

let uu____3946 = (with_captured_errors st.FStar_Interactive_JsonHelper.repl_env FStar_Util.sigint_ignore (fun uu____3955 -> (

let uu____3956 = (collect_decls ())
in (FStar_All.pipe_left (fun _3967 -> FStar_Pervasives_Native.Some (_3967)) uu____3956))))
in (match (uu____3946) with
| FStar_Pervasives_Native.None -> begin
(

let errors = (

let uu____3985 = (collect_errors ())
in (FStar_All.pipe_right uu____3985 (FStar_List.map json_of_issue)))
in ((((QueryNOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl (st))))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let json_of_decl = (fun decl -> (

let uu____4011 = (

let uu____4019 = (

let uu____4025 = (FStar_Range.json_of_def_range (FStar_Parser_AST.decl_drange decl))
in (("def_range"), (uu____4025)))
in (uu____4019)::[])
in FStar_Util.JsonAssoc (uu____4011)))
in (

let js_decls = (

let uu____4039 = (FStar_List.map json_of_decl decls)
in (FStar_All.pipe_left (fun _4044 -> FStar_Util.JsonList (_4044)) uu____4039))
in ((((QueryOK), (FStar_Util.JsonAssoc (((("decls"), (js_decls)))::[])))), (FStar_Util.Inl (st)))))
end)))))


let run_vfs_add : 'Auu____4074 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____4074) FStar_Util.either) = (fun st opt_fname contents -> (

let fname = (FStar_Util.dflt st.FStar_Interactive_JsonHelper.repl_fname opt_fname)
in ((FStar_Parser_ParseIt.add_vfs_entry fname contents);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st)));
)))


let run_pop : 'Auu____4127 . FStar_Interactive_JsonHelper.repl_state  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____4127) FStar_Util.either) = (fun st -> (

let uu____4145 = (nothing_left_to_pop st)
in (match (uu____4145) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____4169 -> begin
(

let st' = (FStar_Interactive_PushHelper.pop_repl "pop_query" st)
in ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st'))))
end)))


let write_progress : Prims.string FStar_Pervasives_Native.option  ->  (Prims.string * FStar_Util.json) Prims.list  ->  unit = (fun stage contents_alist -> (

let stage1 = (match (stage) with
| FStar_Pervasives_Native.Some (s) -> begin
FStar_Util.JsonStr (s)
end
| FStar_Pervasives_Native.None -> begin
FStar_Util.JsonNull
end)
in (

let js_contents = ((("stage"), (stage1)))::contents_alist
in (

let uu____4232 = (json_of_message "progress" (FStar_Util.JsonAssoc (js_contents)))
in (FStar_Interactive_JsonHelper.write_json uu____4232)))))


let write_repl_ld_task_progress : FStar_Interactive_JsonHelper.repl_task  ->  unit = (fun task -> (match (task) with
| FStar_Interactive_JsonHelper.LDInterleaved (uu____4240, tf) -> begin
(

let modname = (FStar_Parser_Dep.module_name_of_file tf.FStar_Interactive_JsonHelper.tf_fname)
in (write_progress (FStar_Pervasives_Native.Some ("loading-dependency")) (((("modname"), (FStar_Util.JsonStr (modname))))::[])))
end
| FStar_Interactive_JsonHelper.LDSingle (tf) -> begin
(

let modname = (FStar_Parser_Dep.module_name_of_file tf.FStar_Interactive_JsonHelper.tf_fname)
in (write_progress (FStar_Pervasives_Native.Some ("loading-dependency")) (((("modname"), (FStar_Util.JsonStr (modname))))::[])))
end
| FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (tf) -> begin
(

let modname = (FStar_Parser_Dep.module_name_of_file tf.FStar_Interactive_JsonHelper.tf_fname)
in (write_progress (FStar_Pervasives_Native.Some ("loading-dependency")) (((("modname"), (FStar_Util.JsonStr (modname))))::[])))
end
| uu____4292 -> begin
()
end))


let load_deps : FStar_Interactive_JsonHelper.repl_state  ->  ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list), FStar_Interactive_JsonHelper.repl_state) FStar_Util.either = (fun st -> (

let uu____4310 = (with_captured_errors st.FStar_Interactive_JsonHelper.repl_env FStar_Util.sigint_ignore (fun _env -> (

let uu____4338 = (FStar_Interactive_PushHelper.deps_and_repl_ld_tasks_of_our_file st.FStar_Interactive_JsonHelper.repl_fname)
in (FStar_All.pipe_left (fun _4385 -> FStar_Pervasives_Native.Some (_4385)) uu____4338))))
in (match (uu____4310) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (st)
end
| FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___554_4440 = st
in (

let uu____4441 = (FStar_TypeChecker_Env.set_dep_graph st.FStar_Interactive_JsonHelper.repl_env dep_graph1)
in {FStar_Interactive_JsonHelper.repl_line = uu___554_4440.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___554_4440.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___554_4440.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___554_4440.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___554_4440.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu____4441; FStar_Interactive_JsonHelper.repl_stdin = uu___554_4440.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___554_4440.FStar_Interactive_JsonHelper.repl_names}))
in (

let uu____4442 = (run_repl_ld_transactions st1 tasks write_repl_ld_task_progress)
in (match (uu____4442) with
| FStar_Util.Inr (st2) -> begin
((write_progress FStar_Pervasives_Native.None []);
FStar_Util.Inr (st2);
)
end
| FStar_Util.Inl (st2) -> begin
((write_progress FStar_Pervasives_Native.None []);
FStar_Util.Inl (((st2), (deps)));
)
end)))
end)))


let rephrase_dependency_error : FStar_Errors.issue  ->  FStar_Errors.issue = (fun issue -> (

let uu___564_4497 = issue
in (

let uu____4498 = (FStar_Util.format1 "Error while computing or loading dependencies:\n%s" issue.FStar_Errors.issue_message)
in {FStar_Errors.issue_message = uu____4498; FStar_Errors.issue_level = uu___564_4497.FStar_Errors.issue_level; FStar_Errors.issue_range = uu___564_4497.FStar_Errors.issue_range; FStar_Errors.issue_number = uu___564_4497.FStar_Errors.issue_number})))


let run_push_without_deps : 'Auu____4508 . FStar_Interactive_JsonHelper.repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____4508) FStar_Util.either) = (fun st query -> (

let set_nosynth_flag = (fun st1 flag -> (

let uu___571_4544 = st1
in {FStar_Interactive_JsonHelper.repl_line = uu___571_4544.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___571_4544.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___571_4544.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___571_4544.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___571_4544.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = (

let uu___573_4546 = st1.FStar_Interactive_JsonHelper.repl_env
in {FStar_TypeChecker_Env.solver = uu___573_4546.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___573_4546.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___573_4546.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___573_4546.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___573_4546.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___573_4546.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___573_4546.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___573_4546.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___573_4546.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___573_4546.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___573_4546.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___573_4546.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___573_4546.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___573_4546.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___573_4546.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___573_4546.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___573_4546.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___573_4546.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___573_4546.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___573_4546.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___573_4546.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___573_4546.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___573_4546.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = flag; FStar_TypeChecker_Env.uvar_subtyping = uu___573_4546.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___573_4546.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___573_4546.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___573_4546.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___573_4546.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___573_4546.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___573_4546.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___573_4546.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___573_4546.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___573_4546.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___573_4546.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___573_4546.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___573_4546.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___573_4546.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___573_4546.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___573_4546.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___573_4546.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___573_4546.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___573_4546.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___573_4546.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___573_4546.FStar_TypeChecker_Env.erasable_types_tab}); FStar_Interactive_JsonHelper.repl_stdin = uu___571_4544.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___571_4544.FStar_Interactive_JsonHelper.repl_names}))
in (

let uu____4547 = query
in (match (uu____4547) with
| {push_kind = push_kind; push_code = text; push_line = line; push_column = column; push_peek_only = peek_only} -> begin
(

let frag = {FStar_Parser_ParseIt.frag_fname = "<input>"; FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in ((FStar_TypeChecker_Env.toggle_id_info st.FStar_Interactive_JsonHelper.repl_env true);
(

let st1 = (set_nosynth_flag st peek_only)
in (

let uu____4574 = (run_repl_transaction st1 push_kind peek_only (FStar_Interactive_JsonHelper.PushFragment (frag)))
in (match (uu____4574) with
| (success, st2) -> begin
(

let st3 = (set_nosynth_flag st2 false)
in (

let status = (match ((success || peek_only)) with
| true -> begin
QueryOK
end
| uu____4600 -> begin
QueryNOK
end)
in (

let json_errors = (

let uu____4603 = (

let uu____4606 = (collect_errors ())
in (FStar_All.pipe_right uu____4606 (FStar_List.map json_of_issue)))
in FStar_Util.JsonList (uu____4603))
in (

let st4 = (match (success) with
| true -> begin
(

let uu___592_4615 = st3
in {FStar_Interactive_JsonHelper.repl_line = line; FStar_Interactive_JsonHelper.repl_column = column; FStar_Interactive_JsonHelper.repl_fname = uu___592_4615.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___592_4615.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___592_4615.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu___592_4615.FStar_Interactive_JsonHelper.repl_env; FStar_Interactive_JsonHelper.repl_stdin = uu___592_4615.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___592_4615.FStar_Interactive_JsonHelper.repl_names})
end
| uu____4616 -> begin
st3
end)
in ((((status), (json_errors))), (FStar_Util.Inl (st4)))))))
end)));
))
end))))


let run_push_with_deps : 'Auu____4633 . FStar_Interactive_JsonHelper.repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____4633) FStar_Util.either) = (fun st query -> ((

let uu____4657 = (FStar_Options.debug_any ())
in (match (uu____4657) with
| true -> begin
(FStar_Util.print_string "Reloading dependencies")
end
| uu____4661 -> begin
()
end));
(FStar_TypeChecker_Env.toggle_id_info st.FStar_Interactive_JsonHelper.repl_env false);
(

let uu____4665 = (load_deps st)
in (match (uu____4665) with
| FStar_Util.Inr (st1) -> begin
(

let errors = (

let uu____4700 = (collect_errors ())
in (FStar_List.map rephrase_dependency_error uu____4700))
in (

let js_errors = (FStar_All.pipe_right errors (FStar_List.map json_of_issue))
in ((((QueryNOK), (FStar_Util.JsonList (js_errors)))), (FStar_Util.Inl (st1)))))
end
| FStar_Util.Inl (st1, deps) -> begin
((

let uu____4734 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____4734 (fun a2 -> ())));
(

let names1 = (FStar_Interactive_PushHelper.add_module_completions st1.FStar_Interactive_JsonHelper.repl_fname deps st1.FStar_Interactive_JsonHelper.repl_names)
in (run_push_without_deps (

let uu___610_4738 = st1
in {FStar_Interactive_JsonHelper.repl_line = uu___610_4738.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___610_4738.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___610_4738.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___610_4738.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___610_4738.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu___610_4738.FStar_Interactive_JsonHelper.repl_env; FStar_Interactive_JsonHelper.repl_stdin = uu___610_4738.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = names1}) query));
)
end));
))


let run_push : 'Auu____4746 . FStar_Interactive_JsonHelper.repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____4746) FStar_Util.either) = (fun st query -> (

let uu____4769 = (nothing_left_to_pop st)
in (match (uu____4769) with
| true -> begin
(run_push_with_deps st query)
end
| uu____4784 -> begin
(run_push_without_deps st query)
end)))


let run_symbol_lookup : FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____4836 = (FStar_Interactive_QueryHelper.symlookup st.FStar_Interactive_JsonHelper.repl_env symbol pos_opt requested_info)
in (match (uu____4836) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (result) -> begin
(

let uu____4871 = (

let uu____4884 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____4884)))
in FStar_Util.Inr (uu____4871))
end)))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____4939 = (trim_option_name opt_name)
in (match (uu____4939) with
| (uu____4963, trimmed_name) -> begin
(

let uu____4969 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____4969) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.op_Hat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____5004 = (

let uu____5017 = (

let uu____5025 = (update_option opt)
in (alist_of_fstar_option uu____5025))
in (("option"), (uu____5017)))
in FStar_Util.Inr (uu____5004))
end))
end)))


let run_module_lookup : FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____5083 = (FStar_Interactive_CompletionTable.find_module_or_ns st.FStar_Interactive_JsonHelper.repl_names query)
in (match (uu____5083) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____5118 = (

let uu____5131 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____5131)))
in FStar_Util.Inr (uu____5118))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____5162 = (

let uu____5175 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____5175)))
in FStar_Util.Inr (uu____5162))
end))))


let run_code_lookup : FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____5255 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____5255) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____5329) -> begin
(

let uu____5344 = (run_module_lookup st symbol)
in (match (uu____5344) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (err_msg) -> begin
FStar_Util.Inl ("No such symbol, module, or namespace.")
end))
end)))


let run_lookup' : FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  lookup_context  ->  FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol context pos_opt requested_info -> (match (context) with
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


let run_lookup : 'Auu____5532 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  lookup_context  ->  FStar_Interactive_QueryHelper.position FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____5532) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____5582 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____5582) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let run_code_autocomplete : 'Auu____5688 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____5688) FStar_Util.either) = (fun st search_term -> (

let result = (FStar_Interactive_QueryHelper.ck_completion st search_term)
in (

let js = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result result)
in ((((QueryOK), (FStar_Util.JsonList (js)))), (FStar_Util.Inl (st))))))


let run_module_autocomplete : 'Auu____5742 'Auu____5743 'Auu____5744 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  'Auu____5742  ->  'Auu____5743  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____5744) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.FStar_Interactive_JsonHelper.repl_names needle (fun _5791 -> FStar_Pervasives_Native.Some (_5791)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : 'Auu____5812 . Prims.int  ->  'Auu____5812  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____5832 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____5832) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____5867 -> begin
(Prims.op_Hat "(" (Prims.op_Hat explanation (Prims.op_Hat " " (Prims.op_Hat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____5894 'Auu____5895 'Auu____5896 . 'Auu____5894  ->  Prims.string  ->  'Auu____5895  ->  ((query_status * FStar_Util.json) * ('Auu____5894, 'Auu____5896) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____5926 = (trim_option_name search_term)
in (match (uu____5926) with
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
| (uu____5982, uu____5983) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____6006 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____6006) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_and_rewind : 'Auu____6058 'Auu____6059 . FStar_Interactive_JsonHelper.repl_state  ->  'Auu____6058  ->  (FStar_Interactive_JsonHelper.repl_state  ->  'Auu____6058)  ->  ('Auu____6058 * (FStar_Interactive_JsonHelper.repl_state, 'Auu____6059) FStar_Util.either) = (fun st sigint_default task -> (

let st1 = (FStar_Interactive_PushHelper.push_repl "run_and_rewind" FStar_Interactive_PushHelper.FullCheck FStar_Interactive_JsonHelper.Noop st)
in (

let results = (FStar_All.try_with (fun uu___725_6100 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler FStar_Util.sigint_raise (fun uu____6111 -> (

let uu____6112 = (task st1)
in (FStar_All.pipe_left (fun _6117 -> FStar_Util.Inl (_6117)) uu____6112))))
end)) (fun uu___724_6119 -> (match (uu___724_6119) with
| FStar_Util.SigInt -> begin
FStar_Util.Inl (sigint_default)
end
| e -> begin
FStar_Util.Inr (e)
end)))
in (

let st2 = (FStar_Interactive_PushHelper.pop_repl "run_and_rewind" st1)
in (match (results) with
| FStar_Util.Inl (results1) -> begin
((results1), (FStar_Util.Inl (st2)))
end
| FStar_Util.Inr (e) -> begin
(FStar_Exn.raise e)
end)))))


let run_with_parsed_and_tc_term : 'Auu____6166 'Auu____6167 'Auu____6168 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  'Auu____6166  ->  'Auu____6167  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (query_status * FStar_Util.json))  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____6168) FStar_Util.either) = (fun st term line column continuation -> (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_fname = "<input>"; FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____6270, ({FStar_Syntax_Syntax.lbname = uu____6271; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____6273; FStar_Syntax_Syntax.lbeff = uu____6274; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____6276; FStar_Syntax_Syntax.lbpos = uu____6277})::[]), uu____6278); FStar_Syntax_Syntax.sigrng = uu____6279; FStar_Syntax_Syntax.sigquals = uu____6280; FStar_Syntax_Syntax.sigmeta = uu____6281; FStar_Syntax_Syntax.sigattrs = uu____6282; FStar_Syntax_Syntax.sigopts = uu____6283})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____6324 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____6345 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____6345) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____6351) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____6372 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun env decls -> (

let uu____6390 = (

let uu____6395 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts decls)
in (uu____6395 env.FStar_TypeChecker_Env.dsenv))
in (FStar_Pervasives_Native.fst uu____6390)))
in (

let typecheck = (fun tcenv decls -> (

let uu____6417 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____6417) with
| (ses, uu____6431, uu____6432) -> begin
ses
end)))
in (run_and_rewind st ((QueryNOK), (FStar_Util.JsonStr ("Computation interrupted"))) (fun st1 -> (

let tcenv = st1.FStar_Interactive_JsonHelper.repl_env
in (

let frag = (dummy_let_fragment term)
in (

let uu____6453 = (parse1 frag)
in (match (uu____6453) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____6479 -> (

let decls1 = (desugar tcenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____6515 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____6515) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (continuation tcenv1 def1))
end))
end))))
in (

let uu____6527 = (FStar_Options.trace_error ())
in (match (uu____6527) with
| true -> begin
(aux ())
end
| uu____6534 -> begin
(FStar_All.try_with (fun uu___809_6541 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___808_6550 -> (

let uu____6555 = (FStar_Errors.issue_of_exn uu___808_6550)
in (match (uu____6555) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____6563 = (

let uu____6564 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____6564))
in ((QueryNOK), (uu____6563)))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise uu___808_6550)
end))))
end)))
end))))))))))))


let run_compute : 'Auu____6579 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____6579) FStar_Util.either) = (fun st term rules -> (

let rules1 = (FStar_List.append (match (rules) with
| FStar_Pervasives_Native.Some (rules1) -> begin
rules1
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Iota)::(FStar_TypeChecker_Env.Zeta)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]
end) ((FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.UnfoldTac)::(FStar_TypeChecker_Env.Primops)::[]))
in (

let normalize_term1 = (fun tcenv rules2 t -> (FStar_TypeChecker_Normalize.normalize rules2 tcenv t))
in (run_with_parsed_and_tc_term st term (Prims.parse_int "0") (Prims.parse_int "0") (fun tcenv def -> (

let normalized = (normalize_term1 tcenv rules1 def)
in (

let uu____6657 = (

let uu____6658 = (FStar_Interactive_QueryHelper.term_to_string tcenv normalized)
in FStar_Util.JsonStr (uu____6658))
in ((QueryOK), (uu____6657)))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____6693 -> begin
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
| uu____6715 -> begin
false
end))


let __proj__TypeContainsLid__item___0 : search_term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| TypeContainsLid (_0) -> begin
_0
end))


let __proj__Mksearch_term__item__st_negate : search_term  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {st_negate = st_negate; st_term = st_term} -> begin
st_negate
end))


let __proj__Mksearch_term__item__st_term : search_term  ->  search_term' = (fun projectee -> (match (projectee) with
| {st_negate = st_negate; st_term = st_term} -> begin
st_term
end))


let st_cost : search_term'  ->  Prims.int = (fun uu___6_6750 -> (match (uu___6_6750) with
| NameContainsStr (str) -> begin
(~- ((FStar_String.length str)))
end
| TypeContainsLid (lid) -> begin
(Prims.parse_int "1")
end))

type search_candidate =
{sc_lid : FStar_Ident.lid; sc_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref; sc_fvars : FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option FStar_ST.ref}


let __proj__Mksearch_candidate__item__sc_lid : search_candidate  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {sc_lid = sc_lid; sc_typ = sc_typ; sc_fvars = sc_fvars} -> begin
sc_lid
end))


let __proj__Mksearch_candidate__item__sc_typ : search_candidate  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {sc_lid = sc_lid; sc_typ = sc_typ; sc_fvars = sc_fvars} -> begin
sc_typ
end))


let __proj__Mksearch_candidate__item__sc_fvars : search_candidate  ->  FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option FStar_ST.ref = (fun projectee -> (match (projectee) with
| {sc_lid = sc_lid; sc_typ = sc_typ; sc_fvars = sc_fvars} -> begin
sc_fvars
end))


let sc_of_lid : FStar_Ident.lid  ->  search_candidate = (fun lid -> (

let uu____6884 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____6891 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____6884; sc_fvars = uu____6891})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____6915 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____6915) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____6943 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____6943) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____6962, typ), uu____6964) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lident FStar_Util.set = (fun tcenv sc -> (

let uu____7014 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____7014) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____7058 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____7058))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun tcenv sc -> (

let typ_str = (

let uu____7102 = (sc_typ tcenv sc)
in (FStar_Interactive_QueryHelper.term_to_string tcenv uu____7102))
in (

let uu____7103 = (

let uu____7111 = (

let uu____7117 = (

let uu____7118 = (

let uu____7120 = (FStar_Syntax_DsEnv.shorten_lid tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid)
in uu____7120.FStar_Ident.str)
in FStar_Util.JsonStr (uu____7118))
in (("lid"), (uu____7117)))
in (uu____7111)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____7103))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____7153) -> begin
true
end
| uu____7156 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____7166) -> begin
uu____7166
end))


let run_search : 'Auu____7175 . FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, 'Auu____7175) FStar_Util.either) = (fun st search_str -> (

let tcenv = st.FStar_Interactive_JsonHelper.repl_env
in (

let empty_fv_set = (FStar_Syntax_Syntax.new_fv_set ())
in (

let st_matches = (fun candidate term -> (

let found = (match (term.st_term) with
| NameContainsStr (str) -> begin
(FStar_Util.contains candidate.sc_lid.FStar_Ident.str str)
end
| TypeContainsLid (lid) -> begin
(

let uu____7222 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____7222))
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
| uu____7252 -> begin
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
| uu____7274 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____7281 = (

let uu____7282 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____7282))
in (FStar_Exn.raise uu____7281))
end
| uu____7285 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____7288 = (strip_quotes term1)
in NameContainsStr (uu____7288))
end
| uu____7290 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____7293 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____7293) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7296 = (

let uu____7297 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____7297))
in (FStar_Exn.raise uu____7296))
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

let uu____7325 = (match (term.st_term) with
| NameContainsStr (s) -> begin
(FStar_Util.format1 "\"%s\"" s)
end
| TypeContainsLid (l) -> begin
(FStar_Util.format1 "%s" l.FStar_Ident.str)
end)
in (Prims.op_Hat (match (term.st_negate) with
| true -> begin
"-"
end
| uu____7336 -> begin
""
end) uu____7325)))
in (

let results = (FStar_All.try_with (fun uu___922_7359 -> (match (()) with
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

let js = (FStar_List.map (json_of_search_result tcenv) sorted1)
in (match (results) with
| [] -> begin
(

let kwds = (

let uu____7407 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____7407))
in (

let uu____7413 = (

let uu____7414 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____7414))
in (FStar_Exn.raise uu____7413)))
end
| uu____7421 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___921_7426 -> (match (uu___921_7426) with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end)))
in ((results), (FStar_Util.Inl (st))))))))))


let run_query : FStar_Interactive_JsonHelper.repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, Prims.int) FStar_Util.either) = (fun st q -> (match (q) with
| Exit -> begin
(run_exit st)
end
| DescribeProtocol -> begin
(run_describe_protocol st)
end
| DescribeRepl -> begin
(run_describe_repl st)
end
| GenericError (message) -> begin
(run_generic_error st message)
end
| ProtocolViolation (query) -> begin
(run_protocol_violation st query)
end
| Segment (c) -> begin
(run_segment st c)
end
| VfsAdd (fname, contents) -> begin
(run_vfs_add st fname contents)
end
| Push (pquery) -> begin
(run_push st pquery)
end
| Pop -> begin
(run_pop st)
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
end))


let validate_query : FStar_Interactive_JsonHelper.repl_state  ->  query  ->  query = (fun st q -> (match (q.qq) with
| Push ({push_kind = FStar_Interactive_PushHelper.SyntaxCheck; push_code = uu____7552; push_line = uu____7553; push_column = uu____7554; push_peek_only = false}) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____7560 -> begin
(match (st.FStar_Interactive_JsonHelper.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = GenericError ("Current module unset"); qid = q.qid}
end
| uu____7562 -> begin
q
end)
end))


let validate_and_run_query : FStar_Interactive_JsonHelper.repl_state  ->  query  ->  ((query_status * FStar_Util.json) * (FStar_Interactive_JsonHelper.repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let query1 = (validate_query st query)
in ((FStar_ST.op_Colon_Equals repl_current_qid (FStar_Pervasives_Native.Some (query1.qid)));
(run_query st query1.qq);
)))


let js_repl_eval : FStar_Interactive_JsonHelper.repl_state  ->  query  ->  (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let uu____7635 = (validate_and_run_query st query)
in (match (uu____7635) with
| ((status, response), st_opt) -> begin
(

let js_response = (json_of_response query.qid status response)
in ((js_response), (st_opt)))
end)))


let js_repl_eval_js : FStar_Interactive_JsonHelper.repl_state  ->  FStar_Util.json  ->  (FStar_Util.json * (FStar_Interactive_JsonHelper.repl_state, Prims.int) FStar_Util.either) = (fun st query_js -> (

let uu____7701 = (deserialize_interactive_query query_js)
in (js_repl_eval st uu____7701)))


let js_repl_eval_str : FStar_Interactive_JsonHelper.repl_state  ->  Prims.string  ->  (Prims.string * (FStar_Interactive_JsonHelper.repl_state, Prims.int) FStar_Util.either) = (fun st query_str -> (

let uu____7725 = (

let uu____7735 = (parse_interactive_query query_str)
in (js_repl_eval st uu____7735))
in (match (uu____7725) with
| (js_response, st_opt) -> begin
(

let uu____7758 = (FStar_Util.string_of_json js_response)
in ((uu____7758), (st_opt)))
end)))


let js_repl_init_opts : unit  ->  unit = (fun uu____7771 -> (

let uu____7772 = (FStar_Options.parse_cmd_line ())
in (match (uu____7772) with
| (res, fnames) -> begin
(match (res) with
| FStar_Getopt.Error (msg) -> begin
(failwith (Prims.op_Hat "repl_init: " msg))
end
| FStar_Getopt.Help -> begin
(failwith "repl_init: --help unexpected")
end
| FStar_Getopt.Success -> begin
(match (fnames) with
| [] -> begin
(failwith "repl_init: No file name given in --ide invocation")
end
| (h)::(uu____7795)::uu____7796 -> begin
(failwith "repl_init: Too many file names given in --ide invocation")
end
| uu____7805 -> begin
()
end)
end)
end)))


let rec go : FStar_Interactive_JsonHelper.repl_state  ->  Prims.int = (fun st -> (

let query = (read_interactive_query st.FStar_Interactive_JsonHelper.repl_stdin)
in (

let uu____7818 = (validate_and_run_query st query)
in (match (uu____7818) with
| ((status, response), state_opt) -> begin
((write_response query.qid status response);
(match (state_opt) with
| FStar_Util.Inl (st') -> begin
(go st')
end
| FStar_Util.Inr (exitcode) -> begin
exitcode
end);
)
end))))


let interactive_error_handler : FStar_Errors.error_handler = (

let issues = (FStar_Util.mk_ref [])
in (

let add_one1 = (fun e -> (

let uu____7871 = (

let uu____7874 = (FStar_ST.op_Bang issues)
in (e)::uu____7874)
in (FStar_ST.op_Colon_Equals issues uu____7871)))
in (

let count_errors = (fun uu____7928 -> (

let uu____7929 = (

let uu____7932 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____7932))
in (FStar_List.length uu____7929)))
in (

let report = (fun uu____7967 -> (

let uu____7968 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____7968)))
in (

let clear1 = (fun uu____7999 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : (FStar_Util.json  ->  unit)  ->  FStar_Util.printer = (fun printer -> {FStar_Util.printer_prinfo = (fun s -> (forward_message printer "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (forward_message printer "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (forward_message printer "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label get_string get_json -> (

let uu____8060 = (get_json ())
in (forward_message printer label uu____8060)))})


let install_ide_mode_hooks : (FStar_Util.json  ->  unit)  ->  unit = (fun printer -> ((FStar_Util.set_printer (interactive_printer printer));
(FStar_Errors.set_handler interactive_error_handler);
))


let initial_range : FStar_Range.range = (

let uu____8074 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____8077 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____8074 uu____8077)))


let build_initial_repl_state : Prims.string  ->  FStar_Interactive_JsonHelper.repl_state = (fun filename -> (

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env initial_range)
in (

let uu____8091 = (FStar_Util.open_stdin ())
in {FStar_Interactive_JsonHelper.repl_line = (Prims.parse_int "1"); FStar_Interactive_JsonHelper.repl_column = (Prims.parse_int "0"); FStar_Interactive_JsonHelper.repl_fname = filename; FStar_Interactive_JsonHelper.repl_deps_stack = []; FStar_Interactive_JsonHelper.repl_curmod = FStar_Pervasives_Native.None; FStar_Interactive_JsonHelper.repl_env = env1; FStar_Interactive_JsonHelper.repl_stdin = uu____8091; FStar_Interactive_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty}))))


let interactive_mode' : 'Auu____8107 . FStar_Interactive_JsonHelper.repl_state  ->  'Auu____8107 = (fun init_st -> ((write_hello ());
(

let exit_code = (

let uu____8116 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____8116) with
| true -> begin
(

let uu____8120 = (

let uu____8122 = (FStar_Options.file_list ())
in (FStar_List.hd uu____8122))
in (FStar_SMTEncoding_Solver.with_hints_db uu____8120 (fun uu____8129 -> (go init_st))))
end
| uu____8130 -> begin
(go init_st)
end))
in (FStar_All.exit exit_code));
))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((install_ide_mode_hooks FStar_Interactive_JsonHelper.write_json);
(FStar_Util.set_sigint_handler FStar_Util.sigint_ignore);
(

let uu____8143 = (

let uu____8145 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____8145))
in (match (uu____8143) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("--ide: ignoring --codegen")))
end
| uu____8151 -> begin
()
end));
(

let init1 = (build_initial_repl_state filename)
in (

let uu____8154 = (FStar_Options.trace_error ())
in (match (uu____8154) with
| true -> begin
(interactive_mode' init1)
end
| uu____8157 -> begin
(FStar_All.try_with (fun uu___1070_8160 -> (match (()) with
| () -> begin
(interactive_mode' init1)
end)) (fun uu___1069_8163 -> ((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise uu___1069_8163);
)))
end)));
))




