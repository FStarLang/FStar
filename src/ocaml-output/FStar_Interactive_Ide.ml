
open Prims
open FStar_Pervasives

type repl_depth_t =
(FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)


let snapshot_env : FStar_TypeChecker_Env.env  ->  Prims.string  ->  (repl_depth_t * FStar_TypeChecker_Env.env_t) = (fun env msg -> (

let uu____60 = (FStar_TypeChecker_Tc.snapshot_context env msg)
in (match (uu____60) with
| (ctx_depth, env1) -> begin
(

let uu____104 = (FStar_Options.snapshot ())
in (match (uu____104) with
| (opt_depth, ()) -> begin
((((ctx_depth), (opt_depth))), (env1))
end))
end)))


let rollback_env : FStar_TypeChecker_Env.solver_t  ->  Prims.string  ->  ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) * Prims.int)  ->  FStar_TypeChecker_Env.env = (fun solver1 msg uu____150 -> (match (uu____150) with
| (ctx_depth, opt_depth) -> begin
(

let env = (FStar_TypeChecker_Tc.rollback_context solver1 msg (FStar_Pervasives_Native.Some (ctx_depth)))
in ((FStar_Options.rollback (FStar_Pervasives_Native.Some (opt_depth)));
env;
))
end))

type push_kind =
| SyntaxCheck
| LaxCheck
| FullCheck


let uu___is_SyntaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SyntaxCheck -> begin
true
end
| uu____217 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____228 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____239 -> begin
false
end))


let set_check_kind : FStar_TypeChecker_Env.env  ->  push_kind  ->  FStar_TypeChecker_Env.env = (fun env check_kind -> (

let uu___32_252 = env
in (

let uu____253 = (FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv (Prims.op_Equality check_kind SyntaxCheck))
in {FStar_TypeChecker_Env.solver = uu___32_252.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___32_252.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___32_252.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___32_252.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___32_252.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___32_252.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___32_252.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___32_252.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___32_252.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___32_252.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___32_252.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___32_252.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___32_252.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___32_252.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___32_252.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___32_252.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___32_252.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___32_252.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___32_252.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___32_252.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality check_kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___32_252.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___32_252.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___32_252.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___32_252.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___32_252.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___32_252.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___32_252.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___32_252.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___32_252.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___32_252.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___32_252.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___32_252.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___32_252.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___32_252.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___32_252.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___32_252.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___32_252.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___32_252.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___32_252.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___32_252.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu____253; FStar_TypeChecker_Env.nbe = uu___32_252.FStar_TypeChecker_Env.nbe})))


let with_captured_errors' : 'Auu____263 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____263 FStar_Pervasives_Native.option)  ->  'Auu____263 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (FStar_All.try_with (fun uu___38_293 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler sigint_handler (fun uu____299 -> (f env)))
end)) (fun uu___37_304 -> (match (uu___37_304) with
| FStar_All.Failure (msg) -> begin
(

let msg1 = (Prims.op_Hat "ASSERTION FAILURE: " (Prims.op_Hat msg (Prims.op_Hat "\n" (Prims.op_Hat "F* may be in an inconsistent state.\n" (Prims.op_Hat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____317 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.log_issue uu____317 ((FStar_Errors.Error_IDEAssertionFailure), (msg1))));
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

let uu____347 = (

let uu____357 = (

let uu____365 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____365)))
in (uu____357)::[])
in (FStar_TypeChecker_Err.add_errors env uu____347));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Stop -> begin
FStar_Pervasives_Native.None
end))))


let with_captured_errors : 'Auu____390 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____390 FStar_Pervasives_Native.option)  ->  'Auu____390 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (

let uu____417 = (FStar_Options.trace_error ())
in (match (uu____417) with
| true -> begin
(f env)
end
| uu____422 -> begin
(with_captured_errors' env sigint_handler f)
end)))

type timed_fname =
{tf_fname : Prims.string; tf_modtime : FStar_Util.time}


let __proj__Mktimed_fname__item__tf_fname : timed_fname  ->  Prims.string = (fun projectee -> (match (projectee) with
| {tf_fname = tf_fname; tf_modtime = tf_modtime} -> begin
tf_fname
end))


let __proj__Mktimed_fname__item__tf_modtime : timed_fname  ->  FStar_Util.time = (fun projectee -> (match (projectee) with
| {tf_fname = tf_fname; tf_modtime = tf_modtime} -> begin
tf_modtime
end))


let t0 : FStar_Util.time = (FStar_Util.now ())


let tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> (

let uu____464 = (FStar_Parser_ParseIt.get_file_last_modification_time fname)
in {tf_fname = fname; tf_modtime = uu____464}))


let dummy_tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> {tf_fname = fname; tf_modtime = t0})


let string_of_timed_fname : timed_fname  ->  Prims.string = (fun uu____479 -> (match (uu____479) with
| {tf_fname = fname; tf_modtime = modtime} -> begin
(match ((Prims.op_Equality modtime t0)) with
| true -> begin
(FStar_Util.format1 "{ %s }" fname)
end
| uu____487 -> begin
(

let uu____489 = (FStar_Util.string_of_time modtime)
in (FStar_Util.format2 "{ %s; %s }" fname uu____489))
end)
end))

type push_query =
{push_kind : push_kind; push_code : Prims.string; push_line : Prims.int; push_column : Prims.int; push_peek_only : Prims.bool}


let __proj__Mkpush_query__item__push_kind : push_query  ->  push_kind = (fun projectee -> (match (projectee) with
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


type optmod_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option

type repl_task =
| LDInterleaved of (timed_fname * timed_fname)
| LDSingle of timed_fname
| LDInterfaceOfCurrentFile of timed_fname
| PushFragment of FStar_Parser_ParseIt.input_frag
| Noop


let uu___is_LDInterleaved : repl_task  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LDInterleaved (_0) -> begin
true
end
| uu____644 -> begin
false
end))


let __proj__LDInterleaved__item___0 : repl_task  ->  (timed_fname * timed_fname) = (fun projectee -> (match (projectee) with
| LDInterleaved (_0) -> begin
_0
end))


let uu___is_LDSingle : repl_task  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LDSingle (_0) -> begin
true
end
| uu____675 -> begin
false
end))


let __proj__LDSingle__item___0 : repl_task  ->  timed_fname = (fun projectee -> (match (projectee) with
| LDSingle (_0) -> begin
_0
end))


let uu___is_LDInterfaceOfCurrentFile : repl_task  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LDInterfaceOfCurrentFile (_0) -> begin
true
end
| uu____694 -> begin
false
end))


let __proj__LDInterfaceOfCurrentFile__item___0 : repl_task  ->  timed_fname = (fun projectee -> (match (projectee) with
| LDInterfaceOfCurrentFile (_0) -> begin
_0
end))


let uu___is_PushFragment : repl_task  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PushFragment (_0) -> begin
true
end
| uu____713 -> begin
false
end))


let __proj__PushFragment__item___0 : repl_task  ->  FStar_Parser_ParseIt.input_frag = (fun projectee -> (match (projectee) with
| PushFragment (_0) -> begin
_0
end))


let uu___is_Noop : repl_task  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Noop -> begin
true
end
| uu____731 -> begin
false
end))


type env_t =
FStar_TypeChecker_Env.env

type repl_state =
{repl_line : Prims.int; repl_column : Prims.int; repl_fname : Prims.string; repl_deps_stack : (repl_depth_t * (repl_task * repl_state)) Prims.list; repl_curmod : optmod_t; repl_env : env_t; repl_stdin : FStar_Util.stream_reader; repl_names : FStar_Interactive_CompletionTable.table}


let __proj__Mkrepl_state__item__repl_line : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_line
end))


let __proj__Mkrepl_state__item__repl_column : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_column
end))


let __proj__Mkrepl_state__item__repl_fname : repl_state  ->  Prims.string = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_fname
end))


let __proj__Mkrepl_state__item__repl_deps_stack : repl_state  ->  (repl_depth_t * (repl_task * repl_state)) Prims.list = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_deps_stack
end))


let __proj__Mkrepl_state__item__repl_curmod : repl_state  ->  optmod_t = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_curmod
end))


let __proj__Mkrepl_state__item__repl_env : repl_state  ->  env_t = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_env
end))


let __proj__Mkrepl_state__item__repl_stdin : repl_state  ->  FStar_Util.stream_reader = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_stdin
end))


let __proj__Mkrepl_state__item__repl_names : repl_state  ->  FStar_Interactive_CompletionTable.table = (fun projectee -> (match (projectee) with
| {repl_line = repl_line; repl_column = repl_column; repl_fname = repl_fname; repl_deps_stack = repl_deps_stack; repl_curmod = repl_curmod; repl_env = repl_env; repl_stdin = repl_stdin; repl_names = repl_names} -> begin
repl_names
end))


type repl_stack_entry_t =
(repl_depth_t * (repl_task * repl_state))


type repl_stack_t =
(repl_depth_t * (repl_task * repl_state)) Prims.list


let repl_current_qid : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let repl_stack : repl_stack_t FStar_ST.ref = (FStar_Util.mk_ref [])


let pop_repl : Prims.string  ->  repl_state  ->  repl_state = (fun msg st -> (

let uu____1080 = (FStar_ST.op_Bang repl_stack)
in (match (uu____1080) with
| [] -> begin
(failwith "Too many pops")
end
| ((depth, (uu____1110, st')))::stack_tl -> begin
(

let env = (rollback_env st.repl_env.FStar_TypeChecker_Env.solver msg depth)
in ((FStar_ST.op_Colon_Equals repl_stack stack_tl);
(

let uu____1157 = (FStar_Util.physical_equality env st'.repl_env)
in (FStar_Common.runtime_assert uu____1157 "Inconsistent stack state"));
st';
))
end)))


let push_repl : Prims.string  ->  push_kind  ->  repl_task  ->  repl_state  ->  repl_state = (fun msg push_kind task st -> (

let uu____1183 = (snapshot_env st.repl_env msg)
in (match (uu____1183) with
| (depth, env) -> begin
((

let uu____1191 = (

let uu____1192 = (FStar_ST.op_Bang repl_stack)
in (((depth), (((task), (st)))))::uu____1192)
in (FStar_ST.op_Colon_Equals repl_stack uu____1191));
(

let uu___141_1253 = st
in (

let uu____1254 = (set_check_kind env push_kind)
in {repl_line = uu___141_1253.repl_line; repl_column = uu___141_1253.repl_column; repl_fname = uu___141_1253.repl_fname; repl_deps_stack = uu___141_1253.repl_deps_stack; repl_curmod = uu___141_1253.repl_curmod; repl_env = uu____1254; repl_stdin = uu___141_1253.repl_stdin; repl_names = uu___141_1253.repl_names}));
)
end)))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> (

let uu____1262 = (

let uu____1263 = (FStar_ST.op_Bang repl_stack)
in (FStar_List.length uu____1263))
in (Prims.op_Equality uu____1262 (FStar_List.length st.repl_deps_stack))))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding) FStar_Util.either


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____1363 -> begin
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
| uu____1404 -> begin
false
end))


let __proj__NTOpen__item___0 : name_tracking_event  ->  (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace) = (fun projectee -> (match (projectee) with
| NTOpen (_0) -> begin
_0
end))


let uu___is_NTInclude : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTInclude (_0) -> begin
true
end
| uu____1439 -> begin
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
| uu____1474 -> begin
false
end))


let __proj__NTBinding__item___0 : name_tracking_event  ->  (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding) FStar_Util.either = (fun projectee -> (match (projectee) with
| NTBinding (_0) -> begin
_0
end))


let query_of_ids : FStar_Ident.ident Prims.list  ->  FStar_Interactive_CompletionTable.query = (fun ids -> (FStar_List.map FStar_Ident.text_of_id ids))


let query_of_lid : FStar_Ident.lident  ->  FStar_Interactive_CompletionTable.query = (fun lid -> (query_of_ids (FStar_List.append lid.FStar_Ident.ns ((lid.FStar_Ident.ident)::[]))))


let update_names_from_event : Prims.string  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod_str table evt -> (

let is_cur_mod = (fun lid -> (Prims.op_Equality lid.FStar_Ident.str cur_mod_str))
in (match (evt) with
| NTAlias (host, id1, included) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1542 = (FStar_Ident.text_of_id id1)
in (

let uu____1544 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table uu____1542 [] uu____1544)))
end
| uu____1546 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1552 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_Syntax_DsEnv.Open_module) [] uu____1552))
end
| uu____1554 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____1558 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____1561 -> begin
(query_of_lid host)
end)
in (

let uu____1563 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____1558 uu____1563)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid (lid, uu____1575)) -> begin
(lid)::[]
end
| FStar_Util.Inr (lids, uu____1593) -> begin
lids
end
| uu____1598 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____1613 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (

let uu____1615 = (FStar_Ident.text_of_id lid.FStar_Ident.ident)
in (FStar_Interactive_CompletionTable.insert tbl ns_query uu____1615 lid)))) table lids))
end)))


let commit_name_tracking' : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____1646 = (FStar_Syntax_Syntax.mod_name md)
in uu____1646.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let commit_name_tracking : repl_state  ->  name_tracking_event Prims.list  ->  repl_state = (fun st name_events -> (

let names1 = (commit_name_tracking' st.repl_curmod st.repl_names name_events)
in (

let uu___201_1672 = st
in {repl_line = uu___201_1672.repl_line; repl_column = uu___201_1672.repl_column; repl_fname = uu___201_1672.repl_fname; repl_deps_stack = uu___201_1672.repl_deps_stack; repl_curmod = uu___201_1672.repl_curmod; repl_env = uu___201_1672.repl_env; repl_stdin = uu___201_1672.repl_stdin; repl_names = names1})))


let fresh_name_tracking_hooks : unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____1688 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____1702 = (

let uu____1705 = (FStar_ST.op_Bang events)
in (evt)::uu____1705)
in (FStar_ST.op_Colon_Equals events uu____1702)))
in ((events), ({FStar_Syntax_DsEnv.ds_push_open_hook = (fun dsenv1 op -> (

let uu____1766 = (

let uu____1767 = (

let uu____1772 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1772), (op)))
in NTOpen (uu____1767))
in (push_event uu____1766))); FStar_Syntax_DsEnv.ds_push_include_hook = (fun dsenv1 ns -> (

let uu____1778 = (

let uu____1779 = (

let uu____1784 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1784), (ns)))
in NTInclude (uu____1779))
in (push_event uu____1778))); FStar_Syntax_DsEnv.ds_push_module_abbrev_hook = (fun dsenv1 x l -> (

let uu____1792 = (

let uu____1793 = (

let uu____1800 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1800), (x), (l)))
in NTAlias (uu____1793))
in (push_event uu____1792)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____1805 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : env_t  ->  (env_t * (env_t  ->  (env_t * name_tracking_event Prims.list))) = (fun env -> (

let set_hooks = (fun dshooks tchooks env1 -> (

let uu____1859 = (FStar_Universal.with_dsenv_of_tcenv env1 (fun dsenv1 -> (

let uu____1867 = (FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks)
in ((()), (uu____1867)))))
in (match (uu____1859) with
| ((), tcenv') -> begin
(FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks)
end)))
in (

let uu____1869 = (

let uu____1874 = (FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv)
in (

let uu____1875 = (FStar_TypeChecker_Env.tc_hooks env)
in ((uu____1874), (uu____1875))))
in (match (uu____1869) with
| (old_dshooks, old_tchooks) -> begin
(

let uu____1891 = (fresh_name_tracking_hooks ())
in (match (uu____1891) with
| (events, new_dshooks, new_tchooks) -> begin
(

let uu____1926 = (set_hooks new_dshooks new_tchooks env)
in ((uu____1926), ((fun env1 -> (

let uu____1940 = (set_hooks old_dshooks old_tchooks env1)
in (

let uu____1941 = (

let uu____1944 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____1944))
in ((uu____1940), (uu____1941))))))))
end))
end))))


let string_of_repl_task : repl_task  ->  Prims.string = (fun uu___0_1978 -> (match (uu___0_1978) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1982 = (string_of_timed_fname intf)
in (

let uu____1984 = (string_of_timed_fname impl)
in (FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1982 uu____1984)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1988 = (string_of_timed_fname intf_or_impl)
in (FStar_Util.format1 "LDSingle %s" uu____1988))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1992 = (string_of_timed_fname intf)
in (FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1992))
end
| PushFragment (frag) -> begin
(FStar_Util.format1 "PushFragment { code = %s }" frag.FStar_Parser_ParseIt.frag_text)
end
| Noop -> begin
"Noop {}"
end))


let tc_one : env_t  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_TypeChecker_Env.env_t = (fun env intf_opt modf -> (

let uu____2022 = (

let uu____2027 = (

let uu____2028 = (

let uu____2034 = (FStar_TypeChecker_Env.dep_graph env)
in (FStar_Parser_Dep.parsing_data_of uu____2034))
in (FStar_All.pipe_right modf uu____2028))
in (FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____2027))
in (match (uu____2022) with
| (uu____2036, env1) -> begin
env1
end)))


let run_repl_task : optmod_t  ->  env_t  ->  repl_task  ->  (optmod_t * env_t) = (fun curmod env task -> (match (task) with
| LDInterleaved (intf, impl) -> begin
(

let uu____2064 = (tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname)) impl.tf_fname)
in ((curmod), (uu____2064)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____2067 = (tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname)
in ((curmod), (uu____2067)))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____2070 = (FStar_Universal.load_interface_decls env intf.tf_fname)
in ((curmod), (uu____2070)))
end
| PushFragment (frag) -> begin
(FStar_Universal.tc_one_fragment curmod env frag)
end
| Noop -> begin
((curmod), (env))
end))


let repl_ld_tasks_of_deps : Prims.string Prims.list  ->  repl_task Prims.list  ->  repl_task Prims.list = (fun deps final_tasks -> (

let wrap = dummy_tf_of_fname
in (

let rec aux = (fun deps1 final_tasks1 -> (match (deps1) with
| (intf)::(impl)::deps' when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____2136 = (aux deps' final_tasks1)
in (LDInterleaved ((((wrap intf)), ((wrap impl)))))::uu____2136)
end
| (intf_or_impl)::deps' -> begin
(

let uu____2146 = (aux deps' final_tasks1)
in (LDSingle ((wrap intf_or_impl)))::uu____2146)
end
| [] -> begin
final_tasks1
end))
in (aux deps final_tasks))))


let deps_and_repl_ld_tasks_of_our_file : Prims.string  ->  (Prims.string Prims.list * repl_task Prims.list * FStar_Parser_Dep.deps) = (fun filename -> (

let get_mod_name = (fun fname -> (FStar_Parser_Dep.lowercase_module_name fname))
in (

let our_mod_name = (get_mod_name filename)
in (

let has_our_mod_name = (fun f -> (

let uu____2200 = (get_mod_name f)
in (Prims.op_Equality uu____2200 our_mod_name)))
in (

let uu____2203 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]) FStar_CheckedFiles.load_parsing_data_from_cache)
in (match (uu____2203) with
| (deps, dep_graph1) -> begin
(

let uu____2232 = (FStar_List.partition has_our_mod_name deps)
in (match (uu____2232) with
| (same_name, real_deps) -> begin
(

let intf_tasks = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____2282 = (

let uu____2284 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____2284)))
in (match (uu____2282) with
| true -> begin
(

let uu____2287 = (

let uu____2293 = (FStar_Util.format1 "Expecting an interface, got %s" intf)
in ((FStar_Errors.Fatal_MissingInterface), (uu____2293)))
in (FStar_Errors.raise_err uu____2287))
end
| uu____2297 -> begin
()
end));
(

let uu____2300 = (

let uu____2302 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____2302)))
in (match (uu____2300) with
| true -> begin
(

let uu____2305 = (

let uu____2311 = (FStar_Util.format1 "Expecting an implementation, got %s" impl)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2311)))
in (FStar_Errors.raise_err uu____2305))
end
| uu____2315 -> begin
()
end));
(LDInterfaceOfCurrentFile ((dummy_tf_of_fname intf)))::[];
)
end
| (impl)::[] -> begin
[]
end
| uu____2321 -> begin
(

let mods_str = (FStar_String.concat " " same_name)
in (

let message = "Too many or too few files matching %s: %s"
in ((

let uu____2332 = (

let uu____2338 = (FStar_Util.format message ((our_mod_name)::(mods_str)::[]))
in ((FStar_Errors.Fatal_TooManyOrTooFewFileMatch), (uu____2338)))
in (FStar_Errors.raise_err uu____2332));
[];
)))
end)
in (

let tasks = (repl_ld_tasks_of_deps real_deps intf_tasks)
in ((real_deps), (tasks), (dep_graph1))))
end))
end))))))


let update_task_timestamps : repl_task  ->  repl_task = (fun uu___1_2357 -> (match (uu___1_2357) with
| LDInterleaved (intf, impl) -> begin
(

let uu____2360 = (

let uu____2365 = (tf_of_fname intf.tf_fname)
in (

let uu____2366 = (tf_of_fname impl.tf_fname)
in ((uu____2365), (uu____2366))))
in LDInterleaved (uu____2360))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____2368 = (tf_of_fname intf_or_impl.tf_fname)
in LDSingle (uu____2368))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____2370 = (tf_of_fname intf.tf_fname)
in LDInterfaceOfCurrentFile (uu____2370))
end
| other -> begin
other
end))


let run_repl_transaction : repl_state  ->  push_kind  ->  Prims.bool  ->  repl_task  ->  (Prims.bool * repl_state) = (fun st push_kind must_rollback task -> (

let st1 = (push_repl "run_repl_transaction" push_kind task st)
in (

let uu____2402 = (track_name_changes st1.repl_env)
in (match (uu____2402) with
| (env, finish_name_tracking) -> begin
(

let check_success = (fun uu____2447 -> ((

let uu____2450 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2450 (Prims.parse_int "0"))) && (not (must_rollback))))
in (

let uu____2454 = (

let uu____2462 = (with_captured_errors env FStar_Util.sigint_raise (fun env1 -> (

let uu____2476 = (run_repl_task st1.repl_curmod env1 task)
in (FStar_All.pipe_left (fun _2495 -> FStar_Pervasives_Native.Some (_2495)) uu____2476))))
in (match (uu____2462) with
| FStar_Pervasives_Native.Some (curmod, env1) when (check_success ()) -> begin
((curmod), (env1), (true))
end
| uu____2511 -> begin
((st1.repl_curmod), (env), (false))
end))
in (match (uu____2454) with
| (curmod, env1, success) -> begin
(

let uu____2530 = (finish_name_tracking env1)
in (match (uu____2530) with
| (env2, name_events) -> begin
(

let st2 = (match (success) with
| true -> begin
(

let st2 = (

let uu___341_2551 = st1
in {repl_line = uu___341_2551.repl_line; repl_column = uu___341_2551.repl_column; repl_fname = uu___341_2551.repl_fname; repl_deps_stack = uu___341_2551.repl_deps_stack; repl_curmod = curmod; repl_env = env2; repl_stdin = uu___341_2551.repl_stdin; repl_names = uu___341_2551.repl_names})
in (commit_name_tracking st2 name_events))
end
| uu____2552 -> begin
(pop_repl "run_repl_transaction" st1)
end)
in ((success), (st2)))
end))
end)))
end))))


let run_repl_ld_transactions : repl_state  ->  repl_task Prims.list  ->  (repl_task  ->  unit)  ->  (repl_state, repl_state) FStar_Util.either = (fun st tasks progress_callback -> (

let debug1 = (fun verb task -> (

let uu____2598 = (FStar_Options.debug_any ())
in (match (uu____2598) with
| true -> begin
(

let uu____2601 = (string_of_repl_task task)
in (FStar_Util.print2 "%s %s" verb uu____2601))
end
| uu____2604 -> begin
()
end)))
in (

let rec revert_many = (fun st1 uu___2_2626 -> (match (uu___2_2626) with
| [] -> begin
st1
end
| ((_id, (task, _st')))::entries -> begin
((debug1 "Reverting" task);
(

let st' = (pop_repl "run_repl_ls_transactions" st1)
in (

let dep_graph1 = (FStar_TypeChecker_Env.dep_graph st1.repl_env)
in (

let st'1 = (

let uu___367_2679 = st'
in (

let uu____2680 = (FStar_TypeChecker_Env.set_dep_graph st'.repl_env dep_graph1)
in {repl_line = uu___367_2679.repl_line; repl_column = uu___367_2679.repl_column; repl_fname = uu___367_2679.repl_fname; repl_deps_stack = uu___367_2679.repl_deps_stack; repl_curmod = uu___367_2679.repl_curmod; repl_env = uu____2680; repl_stdin = uu___367_2679.repl_stdin; repl_names = uu___367_2679.repl_names}))
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

let uu____2733 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____2733 (fun a1 -> ())));
(

let timestamped_task = (update_task_timestamps task)
in (

let push_kind = (

let uu____2737 = (FStar_Options.lax ())
in (match (uu____2737) with
| true -> begin
LaxCheck
end
| uu____2740 -> begin
FullCheck
end))
in (

let uu____2742 = (run_repl_transaction st1 push_kind false timestamped_task)
in (match (uu____2742) with
| (success, st2) -> begin
(match (success) with
| true -> begin
(

let uu____2762 = (

let uu___392_2763 = st2
in (

let uu____2764 = (FStar_ST.op_Bang repl_stack)
in {repl_line = uu___392_2763.repl_line; repl_column = uu___392_2763.repl_column; repl_fname = uu___392_2763.repl_fname; repl_deps_stack = uu____2764; repl_curmod = uu___392_2763.repl_curmod; repl_env = uu___392_2763.repl_env; repl_stdin = uu___392_2763.repl_stdin; repl_names = uu___392_2763.repl_names}))
in (aux uu____2762 tasks2 []))
end
| uu____2794 -> begin
FStar_Util.Inr (st2)
end)
end))));
)
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____2808 = (update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev)) uu____2808)) -> begin
((debug1 "Skipping" task);
(aux st1 tasks2 previous1);
)
end
| (tasks2, previous1) -> begin
(

let uu____2825 = (revert_many st1 previous1)
in (aux uu____2825 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.repl_deps_stack))))))


let json_debug : FStar_Util.json  ->  Prims.string = (fun uu___3_2840 -> (match (uu___3_2840) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____2849 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____2854 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____2854))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____2860) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____2864) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2890) -> begin
true
end
| uu____2897 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2915) -> begin
uu____2915
end))


let js_fail : 'Auu____2928 . Prims.string  ->  FStar_Util.json  ->  'Auu____2928 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___4_2948 -> (match (uu___4_2948) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___5_2961 -> (match (uu___5_2961) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____2975 . (FStar_Util.json  ->  'Auu____2975)  ->  FStar_Util.json  ->  'Auu____2975 Prims.list = (fun k uu___6_2990 -> (match (uu___6_2990) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___7_3012 -> (match (uu___7_3012) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____3043 = (js_str s)
in (match (uu____3043) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____3048 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Env.step = (fun s -> (

let uu____3057 = (js_str s)
in (match (uu____3057) with
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
| uu____3065 -> begin
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
| uu____3094 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____3107 -> begin
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
| uu____3135 -> begin
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

let uu____3173 = (js_str k1)
in (match (uu____3173) with
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
| uu____3201 -> begin
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
| uu____3213 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____3224 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____3235 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____3246 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____3259 = (js_str k1)
in (match (uu____3259) with
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
| uu____3269 -> begin
(js_fail "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)" k1)
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
| uu____3386 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____3397 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____3408 -> begin
false
end))


let uu___is_Segment : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
true
end
| uu____3421 -> begin
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
| uu____3442 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____3454 -> begin
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
| uu____3481 -> begin
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
| uu____3529 -> begin
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
| uu____3577 -> begin
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
| uu____3647 -> begin
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
| uu____3694 -> begin
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
| uu____3717 -> begin
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
| uu____3740 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___8_3778 -> (match (uu___8_3778) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Segment (uu____3783) -> begin
false
end
| Pop -> begin
false
end
| Push ({push_kind = uu____3787; push_code = uu____3788; push_line = uu____3789; push_column = uu____3790; push_peek_only = false}) -> begin
false
end
| VfsAdd (uu____3796) -> begin
false
end
| GenericError (uu____3806) -> begin
false
end
| ProtocolViolation (uu____3809) -> begin
false
end
| Push (uu____3812) -> begin
true
end
| AutoComplete (uu____3814) -> begin
true
end
| Lookup (uu____3821) -> begin
true
end
| Compute (uu____3837) -> begin
true
end
| Search (uu____3848) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::("segment")::("vfs-add")::("tactic-ranges")::("interrupt")::("progress")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3914) -> begin
true
end
| uu____3917 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3927) -> begin
uu____3927
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____3938 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____3949 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____3960 -> begin
false
end))


let try_assoc : 'Auu____3971 'Auu____3972 . 'Auu____3971  ->  ('Auu____3971 * 'Auu____3972) Prims.list  ->  'Auu____3972 FStar_Pervasives_Native.option = (fun key a -> (

let uu____3997 = (FStar_Util.try_find (fun uu____4011 -> (match (uu____4011) with
| (k, uu____4018) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____3997)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____4043 = (

let uu____4044 = (

let uu____4046 = (json_debug got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____4046))
in ProtocolViolation (uu____4044))
in {qq = uu____4043; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____4089 = (try_assoc key a)
in (match (uu____4089) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4094 = (

let uu____4095 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____4095))
in (FStar_Exn.raise uu____4094))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____4115 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____4115 js_str))
in (FStar_All.try_with (fun uu___544_4125 -> (match (()) with
| () -> begin
(

let query = (

let uu____4128 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____4128 js_str))
in (

let args = (

let uu____4140 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____4140 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____4169 = (try_assoc k args)
in (match (uu____4169) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____4178 = (match (query) with
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

let uu____4184 = (

let uu____4186 = (arg "code")
in (FStar_All.pipe_right uu____4186 js_str))
in Segment (uu____4184))
end
| "peek" -> begin
(

let uu____4190 = (

let uu____4191 = (

let uu____4192 = (arg "kind")
in (FStar_All.pipe_right uu____4192 js_pushkind))
in (

let uu____4194 = (

let uu____4196 = (arg "code")
in (FStar_All.pipe_right uu____4196 js_str))
in (

let uu____4199 = (

let uu____4201 = (arg "line")
in (FStar_All.pipe_right uu____4201 js_int))
in (

let uu____4204 = (

let uu____4206 = (arg "column")
in (FStar_All.pipe_right uu____4206 js_int))
in {push_kind = uu____4191; push_code = uu____4194; push_line = uu____4199; push_column = uu____4204; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____4190))
end
| "push" -> begin
(

let uu____4212 = (

let uu____4213 = (

let uu____4214 = (arg "kind")
in (FStar_All.pipe_right uu____4214 js_pushkind))
in (

let uu____4216 = (

let uu____4218 = (arg "code")
in (FStar_All.pipe_right uu____4218 js_str))
in (

let uu____4221 = (

let uu____4223 = (arg "line")
in (FStar_All.pipe_right uu____4223 js_int))
in (

let uu____4226 = (

let uu____4228 = (arg "column")
in (FStar_All.pipe_right uu____4228 js_int))
in {push_kind = uu____4213; push_code = uu____4216; push_line = uu____4221; push_column = uu____4226; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____4212))
end
| "autocomplete" -> begin
(

let uu____4234 = (

let uu____4240 = (

let uu____4242 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____4242 js_str))
in (

let uu____4245 = (

let uu____4246 = (try_arg "context")
in (FStar_All.pipe_right uu____4246 js_optional_completion_context))
in ((uu____4240), (uu____4245))))
in AutoComplete (uu____4234))
end
| "lookup" -> begin
(

let uu____4254 = (

let uu____4269 = (

let uu____4271 = (arg "symbol")
in (FStar_All.pipe_right uu____4271 js_str))
in (

let uu____4274 = (

let uu____4275 = (try_arg "context")
in (FStar_All.pipe_right uu____4275 js_optional_lookup_context))
in (

let uu____4281 = (

let uu____4284 = (

let uu____4294 = (try_arg "location")
in (FStar_All.pipe_right uu____4294 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____4284 (FStar_Util.map_option (fun loc -> (

let uu____4355 = (

let uu____4357 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____4357 js_str))
in (

let uu____4361 = (

let uu____4363 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____4363 js_int))
in (

let uu____4367 = (

let uu____4369 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____4369 js_int))
in ((uu____4355), (uu____4361), (uu____4367)))))))))
in (

let uu____4376 = (

let uu____4380 = (arg "requested-info")
in (FStar_All.pipe_right uu____4380 (js_list js_str)))
in ((uu____4269), (uu____4274), (uu____4281), (uu____4376))))))
in Lookup (uu____4254))
end
| "compute" -> begin
(

let uu____4393 = (

let uu____4403 = (

let uu____4405 = (arg "term")
in (FStar_All.pipe_right uu____4405 js_str))
in (

let uu____4408 = (

let uu____4413 = (try_arg "rules")
in (FStar_All.pipe_right uu____4413 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____4403), (uu____4408))))
in Compute (uu____4393))
end
| "search" -> begin
(

let uu____4431 = (

let uu____4433 = (arg "terms")
in (FStar_All.pipe_right uu____4433 js_str))
in Search (uu____4431))
end
| "vfs-add" -> begin
(

let uu____4437 = (

let uu____4446 = (

let uu____4450 = (try_arg "filename")
in (FStar_All.pipe_right uu____4450 (FStar_Util.map_option js_str)))
in (

let uu____4460 = (

let uu____4462 = (arg "contents")
in (FStar_All.pipe_right uu____4462 js_str))
in ((uu____4446), (uu____4460))))
in VfsAdd (uu____4437))
end
| uu____4469 -> begin
(

let uu____4471 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____4471))
end)
in {qq = uu____4178; qid = qid})))))
end)) (fun uu___543_4476 -> (match (uu___543_4476) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let deserialize_interactive_query : FStar_Util.json  ->  query = (fun js_query -> (FStar_All.try_with (fun uu___579_4490 -> (match (()) with
| () -> begin
(unpack_interactive_query js_query)
end)) (fun uu___578_4493 -> (match (uu___578_4493) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let parse_interactive_query : Prims.string  ->  query = (fun query_str -> (

let uu____4510 = (FStar_Util.json_of_string query_str)
in (match (uu____4510) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(deserialize_interactive_query request)
end)))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (

let uu____4522 = (FStar_Util.read_line stream)
in (match (uu____4522) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(parse_interactive_query line)
end)))


let json_of_opt : 'Auu____4538 . ('Auu____4538  ->  FStar_Util.json)  ->  'Auu____4538 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____4558 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____4558)))


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

let uu____4578 = (

let uu____4586 = (

let uu____4594 = (

let uu____4602 = (

let uu____4608 = (

let uu____4609 = (

let uu____4612 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____4618 = (FStar_Range.json_of_use_range r)
in (uu____4618)::[])
end)
in (

let uu____4619 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (

let uu____4625 = (FStar_Range.def_range r)
in (

let uu____4626 = (FStar_Range.use_range r)
in (Prims.op_disEquality uu____4625 uu____4626))) -> begin
(

let uu____4627 = (FStar_Range.json_of_def_range r)
in (uu____4627)::[])
end
| uu____4628 -> begin
[]
end)
in (FStar_List.append uu____4612 uu____4619)))
in FStar_Util.JsonList (uu____4609))
in (("ranges"), (uu____4608)))
in (uu____4602)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____4594)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____4586)
in FStar_Util.JsonAssoc (uu____4578)))

type symbol_lookup_result =
{slr_name : Prims.string; slr_def_range : FStar_Range.range FStar_Pervasives_Native.option; slr_typ : Prims.string FStar_Pervasives_Native.option; slr_doc : Prims.string FStar_Pervasives_Native.option; slr_def : Prims.string FStar_Pervasives_Native.option}


let __proj__Mksymbol_lookup_result__item__slr_name : symbol_lookup_result  ->  Prims.string = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_name
end))


let __proj__Mksymbol_lookup_result__item__slr_def_range : symbol_lookup_result  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_def_range
end))


let __proj__Mksymbol_lookup_result__item__slr_typ : symbol_lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_typ
end))


let __proj__Mksymbol_lookup_result__item__slr_doc : symbol_lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_doc
end))


let __proj__Mksymbol_lookup_result__item__slr_def : symbol_lookup_result  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {slr_name = slr_name; slr_def_range = slr_def_range; slr_typ = slr_typ; slr_doc = slr_doc; slr_def = slr_def} -> begin
slr_def
end))


let alist_of_symbol_lookup_result : symbol_lookup_result  ->  (Prims.string * FStar_Util.json) Prims.list = (fun lr -> (

let uu____4846 = (

let uu____4854 = (

let uu____4860 = (json_of_opt FStar_Range.json_of_def_range lr.slr_def_range)
in (("defined-at"), (uu____4860)))
in (

let uu____4863 = (

let uu____4871 = (

let uu____4877 = (json_of_opt (fun _4879 -> FStar_Util.JsonStr (_4879)) lr.slr_typ)
in (("type"), (uu____4877)))
in (

let uu____4882 = (

let uu____4890 = (

let uu____4896 = (json_of_opt (fun _4898 -> FStar_Util.JsonStr (_4898)) lr.slr_doc)
in (("documentation"), (uu____4896)))
in (

let uu____4901 = (

let uu____4909 = (

let uu____4915 = (json_of_opt (fun _4917 -> FStar_Util.JsonStr (_4917)) lr.slr_def)
in (("definition"), (uu____4915)))
in (uu____4909)::[])
in (uu____4890)::uu____4901))
in (uu____4871)::uu____4882))
in (uu____4854)::uu____4863))
in ((("name"), (FStar_Util.JsonStr (lr.slr_name))))::uu____4846))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4962 = (FStar_List.map (fun _4966 -> FStar_Util.JsonStr (_4966)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _4969 -> FStar_Util.JsonList (_4969)) uu____4962))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____4998 -> begin
false
end))


let uu___is_OptReset : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReset -> begin
true
end
| uu____5009 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____5020 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___9_5028 -> (match (uu___9_5028) with
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


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___10_5279 -> (match (uu___10_5279) with
| FStar_Options.Const (uu____5281) -> begin
"flag"
end
| FStar_Options.IntStr (uu____5283) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____5287) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____5290) -> begin
"string"
end
| FStar_Options.EnumStr (uu____5293) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____5298) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____5308, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____5318, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let rec snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.op_Hat "${" (Prims.op_Hat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.op_Hat "--" (Prims.op_Hat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.op_Hat " " argstring)
end
| uu____5375 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____5390) -> begin
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
| FStar_Options.PostProcessed (uu____5428, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____5438, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____5446 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____5446))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___11_5457 -> (match (uu___11_5457) with
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

let uu____5469 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____5469))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____5485 = (

let uu____5493 = (

let uu____5501 = (

let uu____5507 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____5507)))
in (

let uu____5510 = (

let uu____5518 = (

let uu____5524 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____5524)))
in (

let uu____5527 = (

let uu____5535 = (

let uu____5541 = (json_of_opt (fun _5543 -> FStar_Util.JsonStr (_5543)) opt.opt_documentation)
in (("documentation"), (uu____5541)))
in (

let uu____5546 = (

let uu____5554 = (

let uu____5560 = (

let uu____5561 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____5561))
in (("type"), (uu____5560)))
in (uu____5554)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____5535)::uu____5546))
in (uu____5518)::uu____5527))
in (uu____5501)::uu____5510))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____5493)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____5485))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____5617 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____5617)))


let write_json : FStar_Util.json  ->  unit = (fun json -> ((

let uu____5632 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____5632));
(FStar_Util.print_raw "\n");
))


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


let write_response : Prims.string  ->  query_status  ->  FStar_Util.json  ->  unit = (fun qid status response -> (write_json (json_of_response qid status response)))


let json_of_message : Prims.string  ->  FStar_Util.json  ->  FStar_Util.json = (fun level js_contents -> (

let uu____5723 = (

let uu____5731 = (

let uu____5739 = (

let uu____5745 = (

let uu____5746 = (FStar_ST.op_Bang repl_current_qid)
in (json_of_opt (fun _5776 -> FStar_Util.JsonStr (_5776)) uu____5746))
in (("query-id"), (uu____5745)))
in (uu____5739)::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (js_contents)))::[])
in ((("kind"), (FStar_Util.JsonStr ("message"))))::uu____5731)
in FStar_Util.JsonAssoc (uu____5723)))


let forward_message : 'Auu____5820 . (FStar_Util.json  ->  'Auu____5820)  ->  Prims.string  ->  FStar_Util.json  ->  'Auu____5820 = (fun callback level contents -> (

let uu____5843 = (json_of_message level contents)
in (callback uu____5843)))


let json_of_hello : FStar_Util.json = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____5847 = (FStar_List.map (fun _5851 -> FStar_Util.JsonStr (_5851)) interactive_protocol_features)
in FStar_Util.JsonList (uu____5847))
in FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info)))


let write_hello : unit  ->  unit = (fun uu____5865 -> (write_json json_of_hello))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.op_Hat "--" name)
in (

let uu____5883 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____5883) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.op_Hat flag (Prims.op_Hat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____5899 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____5934 -> (match (uu____5934) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____5958 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____5958 (FStar_Util.map_option (fun default_value -> (

let uu____5970 = (sig_of_fstar_option name typ)
in (

let uu____5972 = (snippets_of_fstar_option name typ)
in (

let uu____5976 = (

let uu____5977 = (FStar_Options.settable name)
in (match (uu____5977) with
| true -> begin
OptSet
end
| uu____5980 -> begin
(

let uu____5982 = (FStar_Options.resettable name)
in (match (uu____5982) with
| true -> begin
OptReset
end
| uu____5985 -> begin
OptReadOnly
end))
end))
in {opt_name = name; opt_sig = uu____5970; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____5972; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5994 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____5976})))))))
end))))
in (FStar_All.pipe_right uu____5899 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___768_6021 = opt
in (

let uu____6022 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___768_6021.opt_name; opt_sig = uu___768_6021.opt_sig; opt_value = uu____6022; opt_default = uu___768_6021.opt_default; opt_type = uu___768_6021.opt_type; opt_snippets = uu___768_6021.opt_snippets; opt_documentation = uu___768_6021.opt_documentation; opt_permission_level = uu___768_6021.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____6038 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____6038)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____6065 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____6065)))
end
| uu____6069 -> begin
((""), (opt_name))
end)))


let json_of_repl_state : repl_state  ->  FStar_Util.json = (fun st -> (

let filenames = (fun uu____6096 -> (match (uu____6096) with
| (uu____6108, (task, uu____6110)) -> begin
(match (task) with
| LDInterleaved (intf, impl) -> begin
(intf.tf_fname)::(impl.tf_fname)::[]
end
| LDSingle (intf_or_impl) -> begin
(intf_or_impl.tf_fname)::[]
end
| LDInterfaceOfCurrentFile (intf) -> begin
(intf.tf_fname)::[]
end
| uu____6129 -> begin
[]
end)
end))
in (

let uu____6131 = (

let uu____6139 = (

let uu____6145 = (

let uu____6146 = (

let uu____6149 = (FStar_List.concatMap filenames st.repl_deps_stack)
in (FStar_List.map (fun _6163 -> FStar_Util.JsonStr (_6163)) uu____6149))
in FStar_Util.JsonList (uu____6146))
in (("loaded-dependencies"), (uu____6145)))
in (

let uu____6166 = (

let uu____6174 = (

let uu____6180 = (

let uu____6181 = (

let uu____6184 = (current_fstar_options (fun uu____6189 -> true))
in (FStar_List.map json_of_fstar_option uu____6184))
in FStar_Util.JsonList (uu____6181))
in (("options"), (uu____6180)))
in (uu____6174)::[])
in (uu____6139)::uu____6166))
in FStar_Util.JsonAssoc (uu____6131))))


let with_printed_effect_args : 'Auu____6213 . (unit  ->  'Auu____6213)  ->  'Auu____6213 = (fun k -> (FStar_Options.with_saved_options (fun uu____6226 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____6244 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____6254 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____6262 'Auu____6263 . 'Auu____6262  ->  ((query_status * FStar_Util.json) * ('Auu____6263, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____6300 'Auu____6301 . 'Auu____6300  ->  ((query_status * FStar_Util.json) * ('Auu____6300, 'Auu____6301) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____6332 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6332) FStar_Util.either) = (fun st -> (

let uu____6350 = (

let uu____6355 = (json_of_repl_state st)
in ((QueryOK), (uu____6355)))
in ((uu____6350), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____6373 'Auu____6374 . 'Auu____6373  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____6373, 'Auu____6374) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_generic_error : 'Auu____6416 'Auu____6417 . 'Auu____6416  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____6416, 'Auu____6417) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let collect_errors : unit  ->  FStar_Errors.issue Prims.list = (fun uu____6457 -> (

let errors = (FStar_Errors.report_all ())
in ((FStar_Errors.clear ());
errors;
)))


let run_segment : 'Auu____6469 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6469) FStar_Util.either) = (fun st code -> (

let frag = {FStar_Parser_ParseIt.frag_text = code; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let collect_decls = (fun uu____6504 -> (

let uu____6505 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____6505) with
| FStar_Parser_Driver.Empty -> begin
[]
end
| FStar_Parser_Driver.Decls (decls) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu____6511, decls)) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface (uu____6517, decls, uu____6519)) -> begin
decls
end)))
in (

let uu____6526 = (with_captured_errors st.repl_env FStar_Util.sigint_ignore (fun uu____6535 -> (

let uu____6536 = (collect_decls ())
in (FStar_All.pipe_left (fun _6547 -> FStar_Pervasives_Native.Some (_6547)) uu____6536))))
in (match (uu____6526) with
| FStar_Pervasives_Native.None -> begin
(

let errors = (

let uu____6565 = (collect_errors ())
in (FStar_All.pipe_right uu____6565 (FStar_List.map json_of_issue)))
in ((((QueryNOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl (st))))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let json_of_decl = (fun decl -> (

let uu____6591 = (

let uu____6599 = (

let uu____6605 = (FStar_Range.json_of_def_range (FStar_Parser_AST.decl_drange decl))
in (("def_range"), (uu____6605)))
in (uu____6599)::[])
in FStar_Util.JsonAssoc (uu____6591)))
in (

let js_decls = (

let uu____6619 = (FStar_List.map json_of_decl decls)
in (FStar_All.pipe_left (fun _6624 -> FStar_Util.JsonList (_6624)) uu____6619))
in ((((QueryOK), (FStar_Util.JsonAssoc (((("decls"), (js_decls)))::[])))), (FStar_Util.Inl (st)))))
end)))))


let run_vfs_add : 'Auu____6654 . repl_state  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6654) FStar_Util.either) = (fun st opt_fname contents -> (

let fname = (FStar_Util.dflt st.repl_fname opt_fname)
in ((FStar_Parser_ParseIt.add_vfs_entry fname contents);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st)));
)))


let run_pop : 'Auu____6707 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6707) FStar_Util.either) = (fun st -> (

let uu____6725 = (nothing_left_to_pop st)
in (match (uu____6725) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____6749 -> begin
(

let st' = (pop_repl "pop_query" st)
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

let uu____6812 = (json_of_message "progress" (FStar_Util.JsonAssoc (js_contents)))
in (write_json uu____6812)))))


let write_repl_ld_task_progress : repl_task  ->  unit = (fun task -> (match (task) with
| LDInterleaved (uu____6820, tf) -> begin
(

let modname = (FStar_Parser_Dep.module_name_of_file tf.tf_fname)
in (write_progress (FStar_Pervasives_Native.Some ("loading-dependency")) (((("modname"), (FStar_Util.JsonStr (modname))))::[])))
end
| LDSingle (tf) -> begin
(

let modname = (FStar_Parser_Dep.module_name_of_file tf.tf_fname)
in (write_progress (FStar_Pervasives_Native.Some ("loading-dependency")) (((("modname"), (FStar_Util.JsonStr (modname))))::[])))
end
| LDInterfaceOfCurrentFile (tf) -> begin
(

let modname = (FStar_Parser_Dep.module_name_of_file tf.tf_fname)
in (write_progress (FStar_Pervasives_Native.Some ("loading-dependency")) (((("modname"), (FStar_Util.JsonStr (modname))))::[])))
end
| uu____6872 -> begin
()
end))


let load_deps : repl_state  ->  ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either = (fun st -> (

let uu____6890 = (with_captured_errors st.repl_env FStar_Util.sigint_ignore (fun _env -> (

let uu____6918 = (deps_and_repl_ld_tasks_of_our_file st.repl_fname)
in (FStar_All.pipe_left (fun _6965 -> FStar_Pervasives_Native.Some (_6965)) uu____6918))))
in (match (uu____6890) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (st)
end
| FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___866_7020 = st
in (

let uu____7021 = (FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1)
in {repl_line = uu___866_7020.repl_line; repl_column = uu___866_7020.repl_column; repl_fname = uu___866_7020.repl_fname; repl_deps_stack = uu___866_7020.repl_deps_stack; repl_curmod = uu___866_7020.repl_curmod; repl_env = uu____7021; repl_stdin = uu___866_7020.repl_stdin; repl_names = uu___866_7020.repl_names}))
in (

let uu____7022 = (run_repl_ld_transactions st1 tasks write_repl_ld_task_progress)
in (match (uu____7022) with
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

let uu___876_7077 = issue
in (

let uu____7078 = (FStar_Util.format1 "Error while computing or loading dependencies:\n%s" issue.FStar_Errors.issue_message)
in {FStar_Errors.issue_message = uu____7078; FStar_Errors.issue_level = uu___876_7077.FStar_Errors.issue_level; FStar_Errors.issue_range = uu___876_7077.FStar_Errors.issue_range; FStar_Errors.issue_number = uu___876_7077.FStar_Errors.issue_number})))


let run_push_without_deps : 'Auu____7088 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7088) FStar_Util.either) = (fun st query -> (

let set_nosynth_flag = (fun st1 flag -> (

let uu___883_7124 = st1
in {repl_line = uu___883_7124.repl_line; repl_column = uu___883_7124.repl_column; repl_fname = uu___883_7124.repl_fname; repl_deps_stack = uu___883_7124.repl_deps_stack; repl_curmod = uu___883_7124.repl_curmod; repl_env = (

let uu___885_7126 = st1.repl_env
in {FStar_TypeChecker_Env.solver = uu___885_7126.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___885_7126.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___885_7126.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___885_7126.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___885_7126.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___885_7126.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___885_7126.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___885_7126.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___885_7126.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___885_7126.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___885_7126.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___885_7126.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___885_7126.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___885_7126.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___885_7126.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___885_7126.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___885_7126.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___885_7126.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___885_7126.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___885_7126.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___885_7126.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___885_7126.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___885_7126.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___885_7126.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = flag; FStar_TypeChecker_Env.uvar_subtyping = uu___885_7126.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___885_7126.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___885_7126.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___885_7126.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___885_7126.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___885_7126.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___885_7126.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___885_7126.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___885_7126.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___885_7126.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___885_7126.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___885_7126.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___885_7126.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___885_7126.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___885_7126.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___885_7126.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___885_7126.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___885_7126.FStar_TypeChecker_Env.nbe}); repl_stdin = uu___883_7124.repl_stdin; repl_names = uu___883_7124.repl_names}))
in (

let uu____7127 = query
in (match (uu____7127) with
| {push_kind = push_kind; push_code = text; push_line = line; push_column = column; push_peek_only = peek_only} -> begin
(

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in ((FStar_TypeChecker_Env.toggle_id_info st.repl_env true);
(

let st1 = (set_nosynth_flag st peek_only)
in (

let uu____7153 = (run_repl_transaction st1 push_kind peek_only (PushFragment (frag)))
in (match (uu____7153) with
| (success, st2) -> begin
(

let st3 = (set_nosynth_flag st2 false)
in (

let status = (match ((success || peek_only)) with
| true -> begin
QueryOK
end
| uu____7179 -> begin
QueryNOK
end)
in (

let json_errors = (

let uu____7182 = (

let uu____7185 = (collect_errors ())
in (FStar_All.pipe_right uu____7185 (FStar_List.map json_of_issue)))
in FStar_Util.JsonList (uu____7182))
in (

let st4 = (match (success) with
| true -> begin
(

let uu___904_7194 = st3
in {repl_line = line; repl_column = column; repl_fname = uu___904_7194.repl_fname; repl_deps_stack = uu___904_7194.repl_deps_stack; repl_curmod = uu___904_7194.repl_curmod; repl_env = uu___904_7194.repl_env; repl_stdin = uu___904_7194.repl_stdin; repl_names = uu___904_7194.repl_names})
end
| uu____7195 -> begin
st3
end)
in ((((status), (json_errors))), (FStar_Util.Inl (st4)))))))
end)));
))
end))))


let capitalize : Prims.string  ->  Prims.string = (fun str -> (match ((Prims.op_Equality str "")) with
| true -> begin
str
end
| uu____7218 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____7224 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.op_Hat (FStar_String.uppercase first) uu____7224)))
end))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____7265 = (FStar_Util.psmap_empty ())
in (

let uu____7270 = (

let uu____7274 = (FStar_Options.prims ())
in (uu____7274)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____7290 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____7290 true))) uu____7265 uu____7270)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____7319 -> (match (uu____7319) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____7336 -> begin
(

let ns_query = (

let uu____7342 = (capitalize modname)
in (FStar_Util.split uu____7342 "."))
in (

let uu____7345 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____7345 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods)))))))


let run_push_with_deps : 'Auu____7360 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7360) FStar_Util.either) = (fun st query -> ((

let uu____7384 = (FStar_Options.debug_any ())
in (match (uu____7384) with
| true -> begin
(FStar_Util.print_string "Reloading dependencies")
end
| uu____7388 -> begin
()
end));
(FStar_TypeChecker_Env.toggle_id_info st.repl_env false);
(

let uu____7392 = (load_deps st)
in (match (uu____7392) with
| FStar_Util.Inr (st1) -> begin
(

let errors = (

let uu____7427 = (collect_errors ())
in (FStar_List.map rephrase_dependency_error uu____7427))
in (

let js_errors = (FStar_All.pipe_right errors (FStar_List.map json_of_issue))
in ((((QueryNOK), (FStar_Util.JsonList (js_errors)))), (FStar_Util.Inl (st1)))))
end
| FStar_Util.Inl (st1, deps) -> begin
((

let uu____7461 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____7461 (fun a2 -> ())));
(

let names1 = (add_module_completions st1.repl_fname deps st1.repl_names)
in (run_push_without_deps (

let uu___942_7465 = st1
in {repl_line = uu___942_7465.repl_line; repl_column = uu___942_7465.repl_column; repl_fname = uu___942_7465.repl_fname; repl_deps_stack = uu___942_7465.repl_deps_stack; repl_curmod = uu___942_7465.repl_curmod; repl_env = uu___942_7465.repl_env; repl_stdin = uu___942_7465.repl_stdin; repl_names = names1}) query));
)
end));
))


let run_push : 'Auu____7473 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7473) FStar_Util.either) = (fun st query -> (

let uu____7496 = (nothing_left_to_pop st)
in (match (uu____7496) with
| true -> begin
(run_push_with_deps st query)
end
| uu____7511 -> begin
(run_push_without_deps st query)
end)))


let run_symbol_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let tcenv = st.repl_env
in (

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____7604 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____7604))
in (

let lid1 = (

let uu____7610 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____7610))
in (

let uu____7615 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____7615 (FStar_Util.map_option (fun uu____7672 -> (match (uu____7672) with
| ((uu____7692, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____7714 = (FStar_Syntax_DsEnv.try_lookup_doc tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____7714 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____7780 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____7780 (fun uu___12_7825 -> (match (uu___12_7825) with
| (FStar_Util.Inr (se, uu____7848), uu____7849) -> begin
(

let uu____7878 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____7878))
end
| uu____7881 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____7939 -> (match (uu____7939) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____7998) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8059 -> begin
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

let uu____8155 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____8155))
end
| uu____8158 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____8172 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____8190 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range1 = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____8205 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {slr_name = name; slr_def_range = def_range1; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}
in (

let uu____8208 = (

let uu____8221 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____8221)))
in FStar_Pervasives_Native.Some (uu____8208))))))))
end)
in (match (response) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (info) -> begin
FStar_Util.Inr (info)
end)))))))))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____8356 = (trim_option_name opt_name)
in (match (uu____8356) with
| (uu____8380, trimmed_name) -> begin
(

let uu____8386 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____8386) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.op_Hat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____8421 = (

let uu____8434 = (

let uu____8442 = (update_option opt)
in (alist_of_fstar_option uu____8442))
in (("option"), (uu____8434)))
in FStar_Util.Inr (uu____8421))
end))
end)))


let run_module_lookup : repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____8500 = (FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names query)
in (match (uu____8500) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____8535 = (

let uu____8548 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____8548)))
in FStar_Util.Inr (uu____8535))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____8579 = (

let uu____8592 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____8592)))
in FStar_Util.Inr (uu____8579))
end))))


let run_code_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____8690 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____8690) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____8764) -> begin
(

let uu____8779 = (run_module_lookup st symbol)
in (match (uu____8779) with
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


let run_lookup : 'Auu____8985 . repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8985) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____9053 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____9053) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let code_autocomplete_mod_filter : 'Auu____9157 . ('Auu____9157 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____9157 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___13_9172 -> (match (uu___13_9172) with
| (uu____9177, FStar_Interactive_CompletionTable.Namespace (uu____9178)) -> begin
FStar_Pervasives_Native.None
end
| (uu____9183, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____9184; FStar_Interactive_CompletionTable.mod_path = uu____9185; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____9195 = (

let uu____9200 = (

let uu____9201 = (

let uu___1076_9202 = md
in (

let uu____9203 = (

let uu____9205 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.op_Hat uu____9205 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____9203; FStar_Interactive_CompletionTable.mod_path = uu___1076_9202.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___1076_9202.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____9201))
in ((pth), (uu____9200)))
in FStar_Pervasives_Native.Some (uu____9195))
end))


let run_code_autocomplete : 'Auu____9219 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____9219) FStar_Util.either) = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names needle)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result (FStar_List.append lids mods_and_nss))
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st))))))))


let run_module_autocomplete : 'Auu____9281 'Auu____9282 'Auu____9283 . repl_state  ->  Prims.string  ->  'Auu____9281  ->  'Auu____9282  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____9283) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle (fun _9330 -> FStar_Pervasives_Native.Some (_9330)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : Prims.int  ->  Prims.bool  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____9364 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReset -> begin
((is_reset), ("#reset-only"))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____9364) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____9402 -> begin
(Prims.op_Hat "(" (Prims.op_Hat explanation (Prims.op_Hat " " (Prims.op_Hat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____9427 'Auu____9428 . 'Auu____9427  ->  Prims.string  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * ('Auu____9427, 'Auu____9428) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____9460 = (trim_option_name search_term)
in (match (uu____9460) with
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
| (uu____9516, uu____9517) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____9540 . repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____9540) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_and_rewind : 'Auu____9591 'Auu____9592 . repl_state  ->  'Auu____9591  ->  (repl_state  ->  'Auu____9591)  ->  ('Auu____9591 * (repl_state, 'Auu____9592) FStar_Util.either) = (fun st sigint_default task -> (

let st1 = (push_repl "run_and_rewind" FullCheck Noop st)
in (

let results = (FStar_All.try_with (fun uu___1135_9633 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler FStar_Util.sigint_raise (fun uu____9644 -> (

let uu____9645 = (task st1)
in (FStar_All.pipe_left (fun _9650 -> FStar_Util.Inl (_9650)) uu____9645))))
end)) (fun uu___1134_9652 -> (match (uu___1134_9652) with
| FStar_Util.SigInt -> begin
FStar_Util.Inl (sigint_default)
end
| e -> begin
FStar_Util.Inr (e)
end)))
in (

let st2 = (pop_repl "run_and_rewind" st1)
in (match (results) with
| FStar_Util.Inl (results1) -> begin
((results1), (FStar_Util.Inl (st2)))
end
| FStar_Util.Inr (e) -> begin
(FStar_Exn.raise e)
end)))))


let run_with_parsed_and_tc_term : 'Auu____9699 'Auu____9700 'Auu____9701 . repl_state  ->  Prims.string  ->  'Auu____9699  ->  'Auu____9700  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (query_status * FStar_Util.json))  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____9701) FStar_Util.either) = (fun st term line column continuation -> (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____9802, ({FStar_Syntax_Syntax.lbname = uu____9803; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____9805; FStar_Syntax_Syntax.lbeff = uu____9806; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____9808; FStar_Syntax_Syntax.lbpos = uu____9809})::[]), uu____9810); FStar_Syntax_Syntax.sigrng = uu____9811; FStar_Syntax_Syntax.sigquals = uu____9812; FStar_Syntax_Syntax.sigmeta = uu____9813; FStar_Syntax_Syntax.sigattrs = uu____9814})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____9853 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____9874 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____9874) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____9880) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____9901 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun env decls -> (

let uu____9919 = (

let uu____9924 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts decls)
in (uu____9924 env.FStar_TypeChecker_Env.dsenv))
in (FStar_Pervasives_Native.fst uu____9919)))
in (

let typecheck = (fun tcenv decls -> (

let uu____9946 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____9946) with
| (ses, uu____9960, uu____9961) -> begin
ses
end)))
in (run_and_rewind st ((QueryNOK), (FStar_Util.JsonStr ("Computation interrupted"))) (fun st1 -> (

let tcenv = st1.repl_env
in (

let frag = (dummy_let_fragment term)
in (

let uu____9982 = (parse1 frag)
in (match (uu____9982) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____10008 -> (

let decls1 = (desugar tcenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____10044 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____10044) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (continuation tcenv1 def1))
end))
end))))
in (

let uu____10056 = (FStar_Options.trace_error ())
in (match (uu____10056) with
| true -> begin
(aux ())
end
| uu____10063 -> begin
(FStar_All.try_with (fun uu___1218_10070 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___1217_10079 -> (

let uu____10084 = (FStar_Errors.issue_of_exn uu___1217_10079)
in (match (uu____10084) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____10092 = (

let uu____10093 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____10093))
in ((QueryNOK), (uu____10092)))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise uu___1217_10079)
end))))
end)))
end))))))))))))


let run_compute : 'Auu____10108 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____10108) FStar_Util.either) = (fun st term rules -> (

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

let uu____10186 = (

let uu____10187 = (term_to_string tcenv normalized)
in FStar_Util.JsonStr (uu____10187))
in ((QueryOK), (uu____10186)))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____10222 -> begin
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
| uu____10244 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___14_10279 -> (match (uu___14_10279) with
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

let uu____10413 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____10420 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____10413; sc_fvars = uu____10420})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____10444 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____10444) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____10472 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____10472) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____10491, typ), uu____10493) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lident FStar_Util.set = (fun tcenv sc -> (

let uu____10543 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____10543) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____10587 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____10587))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun tcenv sc -> (

let typ_str = (

let uu____10631 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____10631))
in (

let uu____10632 = (

let uu____10640 = (

let uu____10646 = (

let uu____10647 = (

let uu____10649 = (FStar_Syntax_DsEnv.shorten_lid tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid)
in uu____10649.FStar_Ident.str)
in FStar_Util.JsonStr (uu____10647))
in (("lid"), (uu____10646)))
in (uu____10640)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____10632))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____10682) -> begin
true
end
| uu____10685 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____10695) -> begin
uu____10695
end))


let run_search : 'Auu____10704 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____10704) FStar_Util.either) = (fun st search_str -> (

let tcenv = st.repl_env
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

let uu____10751 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____10751))
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
| uu____10781 -> begin
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
| uu____10803 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____10810 = (

let uu____10811 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____10811))
in (FStar_Exn.raise uu____10810))
end
| uu____10814 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____10817 = (strip_quotes term1)
in NameContainsStr (uu____10817))
end
| uu____10819 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____10822 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____10822) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10825 = (

let uu____10826 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____10826))
in (FStar_Exn.raise uu____10825))
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

let uu____10854 = (match (term.st_term) with
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
| uu____10865 -> begin
""
end) uu____10854)))
in (

let results = (FStar_All.try_with (fun uu___1331_10888 -> (match (()) with
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

let uu____10936 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____10936))
in (

let uu____10942 = (

let uu____10943 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____10943))
in (FStar_Exn.raise uu____10942)))
end
| uu____10950 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___1330_10955 -> (match (uu___1330_10955) with
| InvalidSearch (s) -> begin
((QueryNOK), (FStar_Util.JsonStr (s)))
end)))
in ((results), (FStar_Util.Inl (st))))))))))


let run_query : repl_state  ->  query'  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st q -> (match (q) with
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


let validate_query : repl_state  ->  query  ->  query = (fun st q -> (match (q.qq) with
| Push ({push_kind = SyntaxCheck; push_code = uu____11081; push_line = uu____11082; push_column = uu____11083; push_peek_only = false}) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____11089 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = GenericError ("Current module unset"); qid = q.qid}
end
| uu____11091 -> begin
q
end)
end))


let validate_and_run_query : repl_state  ->  query  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let query1 = (validate_query st query)
in ((FStar_ST.op_Colon_Equals repl_current_qid (FStar_Pervasives_Native.Some (query1.qid)));
(run_query st query1.qq);
)))


let js_repl_eval : repl_state  ->  query  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let uu____11164 = (validate_and_run_query st query)
in (match (uu____11164) with
| ((status, response), st_opt) -> begin
(

let js_response = (json_of_response query.qid status response)
in ((js_response), (st_opt)))
end)))


let js_repl_eval_js : repl_state  ->  FStar_Util.json  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query_js -> (

let uu____11230 = (deserialize_interactive_query query_js)
in (js_repl_eval st uu____11230)))


let js_repl_eval_str : repl_state  ->  Prims.string  ->  (Prims.string * (repl_state, Prims.int) FStar_Util.either) = (fun st query_str -> (

let uu____11254 = (

let uu____11264 = (parse_interactive_query query_str)
in (js_repl_eval st uu____11264))
in (match (uu____11254) with
| (js_response, st_opt) -> begin
(

let uu____11287 = (FStar_Util.string_of_json js_response)
in ((uu____11287), (st_opt)))
end)))


let js_repl_init_opts : unit  ->  unit = (fun uu____11300 -> (

let uu____11301 = (FStar_Options.parse_cmd_line ())
in (match (uu____11301) with
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
| (h)::(uu____11324)::uu____11325 -> begin
(failwith "repl_init: Too many file names given in --ide invocation")
end
| uu____11334 -> begin
()
end)
end)
end)))


let rec go : repl_state  ->  Prims.int = (fun st -> (

let query = (read_interactive_query st.repl_stdin)
in (

let uu____11347 = (validate_and_run_query st query)
in (match (uu____11347) with
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

let uu____11400 = (

let uu____11403 = (FStar_ST.op_Bang issues)
in (e)::uu____11403)
in (FStar_ST.op_Colon_Equals issues uu____11400)))
in (

let count_errors = (fun uu____11457 -> (

let uu____11458 = (

let uu____11461 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____11461))
in (FStar_List.length uu____11458)))
in (

let report = (fun uu____11496 -> (

let uu____11497 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____11497)))
in (

let clear1 = (fun uu____11528 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : (FStar_Util.json  ->  unit)  ->  FStar_Util.printer = (fun printer -> {FStar_Util.printer_prinfo = (fun s -> (forward_message printer "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (forward_message printer "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (forward_message printer "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label get_string get_json -> (

let uu____11589 = (get_json ())
in (forward_message printer label uu____11589)))})


let install_ide_mode_hooks : (FStar_Util.json  ->  unit)  ->  unit = (fun printer -> ((FStar_Util.set_printer (interactive_printer printer));
(FStar_Errors.set_handler interactive_error_handler);
))


let initial_range : FStar_Range.range = (

let uu____11603 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____11606 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____11603 uu____11606)))


let build_initial_repl_state : Prims.string  ->  repl_state = (fun filename -> (

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env initial_range)
in (

let uu____11620 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_deps_stack = []; repl_curmod = FStar_Pervasives_Native.None; repl_env = env1; repl_stdin = uu____11620; repl_names = FStar_Interactive_CompletionTable.empty}))))


let interactive_mode' : 'Auu____11636 . repl_state  ->  'Auu____11636 = (fun init_st -> ((write_hello ());
(

let exit_code = (

let uu____11645 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____11645) with
| true -> begin
(

let uu____11649 = (

let uu____11651 = (FStar_Options.file_list ())
in (FStar_List.hd uu____11651))
in (FStar_SMTEncoding_Solver.with_hints_db uu____11649 (fun uu____11658 -> (go init_st))))
end
| uu____11659 -> begin
(go init_st)
end))
in (FStar_All.exit exit_code));
))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((install_ide_mode_hooks write_json);
(FStar_Util.set_sigint_handler FStar_Util.sigint_ignore);
(

let uu____11672 = (

let uu____11674 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____11674))
in (match (uu____11672) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("--ide: ignoring --codegen")))
end
| uu____11680 -> begin
()
end));
(

let init1 = (build_initial_repl_state filename)
in (

let uu____11683 = (FStar_Options.trace_error ())
in (match (uu____11683) with
| true -> begin
(interactive_mode' init1)
end
| uu____11686 -> begin
(FStar_All.try_with (fun uu___1479_11689 -> (match (()) with
| () -> begin
(interactive_mode' init1)
end)) (fun uu___1478_11692 -> ((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise uu___1478_11692);
)))
end)));
))




