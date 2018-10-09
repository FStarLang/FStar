
open Prims
open FStar_Pervasives

type repl_depth_t =
(FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)


let snapshot_env : FStar_TypeChecker_Env.env  ->  Prims.string  ->  (repl_depth_t * FStar_TypeChecker_Env.env_t) = (fun env msg -> (

let uu____23 = (FStar_TypeChecker_Tc.snapshot_context env msg)
in (match (uu____23) with
| (ctx_depth, env1) -> begin
(

let uu____58 = (FStar_Options.snapshot ())
in (match (uu____58) with
| (opt_depth, ()) -> begin
((((ctx_depth), (opt_depth))), (env1))
end))
end)))


let rollback_env : FStar_TypeChecker_Env.solver_t  ->  Prims.string  ->  ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) * Prims.int)  ->  FStar_TypeChecker_Env.env = (fun solver1 msg uu____94 -> (match (uu____94) with
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
| uu____140 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____146 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____152 -> begin
false
end))


let set_check_kind : FStar_TypeChecker_Env.env  ->  push_kind  ->  FStar_TypeChecker_Env.env = (fun env check_kind -> (

let uu___459_163 = env
in (

let uu____164 = (FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv (Prims.op_Equality check_kind SyntaxCheck))
in {FStar_TypeChecker_Env.solver = uu___459_163.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___459_163.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___459_163.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___459_163.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___459_163.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___459_163.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___459_163.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___459_163.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___459_163.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___459_163.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___459_163.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___459_163.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___459_163.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___459_163.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___459_163.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___459_163.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___459_163.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___459_163.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___459_163.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___459_163.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality check_kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___459_163.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___459_163.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___459_163.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___459_163.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___459_163.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___459_163.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___459_163.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___459_163.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___459_163.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___459_163.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___459_163.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___459_163.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___459_163.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___459_163.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___459_163.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___459_163.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___459_163.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___459_163.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___459_163.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___459_163.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu____164; FStar_TypeChecker_Env.nbe = uu___459_163.FStar_TypeChecker_Env.nbe})))


let with_captured_errors' : 'Auu____173 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____173 FStar_Pervasives_Native.option)  ->  'Auu____173 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (FStar_All.try_with (fun uu___461_203 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler sigint_handler (fun uu____209 -> (f env)))
end)) (fun uu___460_214 -> (match (uu___460_214) with
| FStar_All.Failure (msg) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____220 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.log_issue uu____220 ((FStar_Errors.Error_IDEAssertionFailure), (msg1))));
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

let uu____241 = (

let uu____250 = (

let uu____257 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____257)))
in (uu____250)::[])
in (FStar_TypeChecker_Err.add_errors env uu____241));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Stop -> begin
FStar_Pervasives_Native.None
end))))


let with_captured_errors : 'Auu____278 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____278 FStar_Pervasives_Native.option)  ->  'Auu____278 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (

let uu____305 = (FStar_Options.trace_error ())
in (match (uu____305) with
| true -> begin
(f env)
end
| uu____308 -> begin
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

let uu____338 = (FStar_Parser_ParseIt.get_file_last_modification_time fname)
in {tf_fname = fname; tf_modtime = uu____338}))


let dummy_tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> {tf_fname = fname; tf_modtime = t0})


let string_of_timed_fname : timed_fname  ->  Prims.string = (fun uu____348 -> (match (uu____348) with
| {tf_fname = fname; tf_modtime = modtime} -> begin
(match ((Prims.op_Equality modtime t0)) with
| true -> begin
(FStar_Util.format1 "{ %s }" fname)
end
| uu____351 -> begin
(

let uu____352 = (FStar_Util.string_of_time modtime)
in (FStar_Util.format2 "{ %s; %s }" fname uu____352))
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
| uu____464 -> begin
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
| uu____490 -> begin
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
| uu____504 -> begin
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
| uu____518 -> begin
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
| uu____531 -> begin
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

let uu____852 = (FStar_ST.op_Bang repl_stack)
in (match (uu____852) with
| [] -> begin
(failwith "Too many pops")
end
| ((depth, (uu____881, st')))::stack_tl -> begin
(

let env = (rollback_env st.repl_env.FStar_TypeChecker_Env.solver msg depth)
in ((FStar_ST.op_Colon_Equals repl_stack stack_tl);
(

let uu____928 = (FStar_Util.physical_equality env st'.repl_env)
in (FStar_Common.runtime_assert uu____928 "Inconsistent stack state"));
st';
))
end)))


let push_repl : Prims.string  ->  push_kind  ->  repl_task  ->  repl_state  ->  repl_state = (fun msg push_kind task st -> (

let uu____949 = (snapshot_env st.repl_env msg)
in (match (uu____949) with
| (depth, env) -> begin
((

let uu____957 = (

let uu____958 = (FStar_ST.op_Bang repl_stack)
in (((depth), (((task), (st)))))::uu____958)
in (FStar_ST.op_Colon_Equals repl_stack uu____957));
(

let uu___462_1019 = st
in (

let uu____1020 = (set_check_kind env push_kind)
in {repl_line = uu___462_1019.repl_line; repl_column = uu___462_1019.repl_column; repl_fname = uu___462_1019.repl_fname; repl_deps_stack = uu___462_1019.repl_deps_stack; repl_curmod = uu___462_1019.repl_curmod; repl_env = uu____1020; repl_stdin = uu___462_1019.repl_stdin; repl_names = uu___462_1019.repl_names}));
)
end)))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> (

let uu____1026 = (

let uu____1027 = (FStar_ST.op_Bang repl_stack)
in (FStar_List.length uu____1027))
in (Prims.op_Equality uu____1026 (FStar_List.length st.repl_deps_stack))))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding) FStar_Util.either


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____1127 -> begin
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
| uu____1163 -> begin
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
| uu____1193 -> begin
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
| uu____1223 -> begin
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

let uu____1281 = (FStar_Ident.text_of_id id1)
in (

let uu____1282 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table uu____1281 [] uu____1282)))
end
| uu____1283 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1287 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_Syntax_DsEnv.Open_module) [] uu____1287))
end
| uu____1288 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____1291 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____1292 -> begin
(query_of_lid host)
end)
in (

let uu____1293 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____1291 uu____1293)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid (lid, uu____1305)) -> begin
(lid)::[]
end
| FStar_Util.Inr (lids, uu____1323) -> begin
lids
end
| uu____1328 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____1340 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (

let uu____1341 = (FStar_Ident.text_of_id lid.FStar_Ident.ident)
in (FStar_Interactive_CompletionTable.insert tbl ns_query uu____1341 lid)))) table lids))
end)))


let commit_name_tracking' : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____1367 = (FStar_Syntax_Syntax.mod_name md)
in uu____1367.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let commit_name_tracking : repl_state  ->  name_tracking_event Prims.list  ->  repl_state = (fun st name_events -> (

let names1 = (commit_name_tracking' st.repl_curmod st.repl_names name_events)
in (

let uu___463_1392 = st
in {repl_line = uu___463_1392.repl_line; repl_column = uu___463_1392.repl_column; repl_fname = uu___463_1392.repl_fname; repl_deps_stack = uu___463_1392.repl_deps_stack; repl_curmod = uu___463_1392.repl_curmod; repl_env = uu___463_1392.repl_env; repl_stdin = uu___463_1392.repl_stdin; repl_names = names1})))


let fresh_name_tracking_hooks : unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____1407 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____1421 = (

let uu____1424 = (FStar_ST.op_Bang events)
in (evt)::uu____1424)
in (FStar_ST.op_Colon_Equals events uu____1421)))
in ((events), ({FStar_Syntax_DsEnv.ds_push_open_hook = (fun dsenv1 op -> (

let uu____1551 = (

let uu____1552 = (

let uu____1557 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1557), (op)))
in NTOpen (uu____1552))
in (push_event uu____1551))); FStar_Syntax_DsEnv.ds_push_include_hook = (fun dsenv1 ns -> (

let uu____1563 = (

let uu____1564 = (

let uu____1569 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1569), (ns)))
in NTInclude (uu____1564))
in (push_event uu____1563))); FStar_Syntax_DsEnv.ds_push_module_abbrev_hook = (fun dsenv1 x l -> (

let uu____1577 = (

let uu____1578 = (

let uu____1585 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1585), (x), (l)))
in NTAlias (uu____1578))
in (push_event uu____1577)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____1590 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : env_t  ->  (env_t * (env_t  ->  (env_t * name_tracking_event Prims.list))) = (fun env -> (

let set_hooks = (fun dshooks tchooks env1 -> (

let uu____1643 = (FStar_Universal.with_tcenv env1 (fun dsenv1 -> (

let uu____1651 = (FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks)
in ((()), (uu____1651)))))
in (match (uu____1643) with
| ((), tcenv') -> begin
(FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks)
end)))
in (

let uu____1653 = (

let uu____1658 = (FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv)
in (

let uu____1659 = (FStar_TypeChecker_Env.tc_hooks env)
in ((uu____1658), (uu____1659))))
in (match (uu____1653) with
| (old_dshooks, old_tchooks) -> begin
(

let uu____1675 = (fresh_name_tracking_hooks ())
in (match (uu____1675) with
| (events, new_dshooks, new_tchooks) -> begin
(

let uu____1710 = (set_hooks new_dshooks new_tchooks env)
in ((uu____1710), ((fun env1 -> (

let uu____1724 = (set_hooks old_dshooks old_tchooks env1)
in (

let uu____1725 = (

let uu____1728 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____1728))
in ((uu____1724), (uu____1725))))))))
end))
end))))


let string_of_repl_task : repl_task  ->  Prims.string = (fun uu___444_1782 -> (match (uu___444_1782) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1785 = (string_of_timed_fname intf)
in (

let uu____1786 = (string_of_timed_fname impl)
in (FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1785 uu____1786)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1788 = (string_of_timed_fname intf_or_impl)
in (FStar_Util.format1 "LDSingle %s" uu____1788))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1790 = (string_of_timed_fname intf)
in (FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1790))
end
| PushFragment (frag) -> begin
(FStar_Util.format1 "PushFragment { code = %s }" frag.FStar_Parser_ParseIt.frag_text)
end
| Noop -> begin
"Noop {}"
end))


let tc_one : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env intf_opt modf -> (

let uu____1811 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None intf_opt modf)
in (match (uu____1811) with
| (uu____1825, env1, delta1) -> begin
(

let env2 = (FStar_Universal.apply_delta_env env1 delta1)
in env2)
end)))


let run_repl_task : optmod_t  ->  env_t  ->  repl_task  ->  (optmod_t * env_t) = (fun curmod env task -> (match (task) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1864 = (tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname)) impl.tf_fname)
in ((curmod), (uu____1864)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1866 = (tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname)
in ((curmod), (uu____1866)))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1868 = (FStar_Universal.load_interface_decls env intf.tf_fname)
in ((curmod), (uu____1868)))
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

let uu____1923 = (aux deps' final_tasks1)
in (LDInterleaved ((((wrap intf)), ((wrap impl)))))::uu____1923)
end
| (intf_or_impl)::deps' -> begin
(

let uu____1930 = (aux deps' final_tasks1)
in (LDSingle ((wrap intf_or_impl)))::uu____1930)
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

let uu____1971 = (get_mod_name f)
in (Prims.op_Equality uu____1971 our_mod_name)))
in (

let uu____1972 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____1972) with
| (deps, dep_graph1) -> begin
(

let uu____1995 = (FStar_List.partition has_our_mod_name deps)
in (match (uu____1995) with
| (same_name, real_deps) -> begin
(

let intf_tasks = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____2032 = (

let uu____2033 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____2033)))
in (match (uu____2032) with
| true -> begin
(

let uu____2034 = (

let uu____2039 = (FStar_Util.format1 "Expecting an interface, got %s" intf)
in ((FStar_Errors.Fatal_MissingInterface), (uu____2039)))
in (FStar_Errors.raise_err uu____2034))
end
| uu____2040 -> begin
()
end));
(

let uu____2042 = (

let uu____2043 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____2043)))
in (match (uu____2042) with
| true -> begin
(

let uu____2044 = (

let uu____2049 = (FStar_Util.format1 "Expecting an implementation, got %s" impl)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2049)))
in (FStar_Errors.raise_err uu____2044))
end
| uu____2050 -> begin
()
end));
(LDInterfaceOfCurrentFile ((dummy_tf_of_fname intf)))::[];
)
end
| (impl)::[] -> begin
[]
end
| uu____2052 -> begin
(

let mods_str = (FStar_String.concat " " same_name)
in (

let message = "Too many or too few files matching %s: %s"
in ((

let uu____2058 = (

let uu____2063 = (FStar_Util.format message ((our_mod_name)::(mods_str)::[]))
in ((FStar_Errors.Fatal_TooManyOrTooFewFileMatch), (uu____2063)))
in (FStar_Errors.raise_err uu____2058));
[];
)))
end)
in (

let tasks = (repl_ld_tasks_of_deps real_deps intf_tasks)
in ((real_deps), (tasks), (dep_graph1))))
end))
end))))))


let update_task_timestamps : repl_task  ->  repl_task = (fun uu___445_2075 -> (match (uu___445_2075) with
| LDInterleaved (intf, impl) -> begin
(

let uu____2078 = (

let uu____2083 = (tf_of_fname intf.tf_fname)
in (

let uu____2084 = (tf_of_fname impl.tf_fname)
in ((uu____2083), (uu____2084))))
in LDInterleaved (uu____2078))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____2086 = (tf_of_fname intf_or_impl.tf_fname)
in LDSingle (uu____2086))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____2088 = (tf_of_fname intf.tf_fname)
in LDInterfaceOfCurrentFile (uu____2088))
end
| other -> begin
other
end))


let run_repl_transaction : repl_state  ->  push_kind  ->  Prims.bool  ->  repl_task  ->  (Prims.bool * repl_state) = (fun st push_kind must_rollback task -> (

let st1 = (push_repl "run_repl_transaction" push_kind task st)
in (

let uu____2115 = (track_name_changes st1.repl_env)
in (match (uu____2115) with
| (env, finish_name_tracking) -> begin
(

let check_success = (fun uu____2158 -> ((

let uu____2161 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2161 (Prims.parse_int "0"))) && (not (must_rollback))))
in (

let uu____2162 = (

let uu____2169 = (with_captured_errors env FStar_Util.sigint_raise (fun env1 -> (

let uu____2183 = (run_repl_task st1.repl_curmod env1 task)
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____2183))))
in (match (uu____2169) with
| FStar_Pervasives_Native.Some (curmod, env1) when (check_success ()) -> begin
((curmod), (env1), (true))
end
| uu____2214 -> begin
((st1.repl_curmod), (env), (false))
end))
in (match (uu____2162) with
| (curmod, env1, success) -> begin
(

let uu____2228 = (finish_name_tracking env1)
in (match (uu____2228) with
| (env2, name_events) -> begin
(

let st2 = (match (success) with
| true -> begin
(

let st2 = (

let uu___464_2247 = st1
in {repl_line = uu___464_2247.repl_line; repl_column = uu___464_2247.repl_column; repl_fname = uu___464_2247.repl_fname; repl_deps_stack = uu___464_2247.repl_deps_stack; repl_curmod = curmod; repl_env = env2; repl_stdin = uu___464_2247.repl_stdin; repl_names = uu___464_2247.repl_names})
in (commit_name_tracking st2 name_events))
end
| uu____2248 -> begin
(pop_repl "run_repl_transaction" st1)
end)
in ((success), (st2)))
end))
end)))
end))))


let run_repl_ld_transactions : repl_state  ->  repl_task Prims.list  ->  (repl_task  ->  unit)  ->  (repl_state, repl_state) FStar_Util.either = (fun st tasks progress_callback -> (

let debug1 = (fun verb task -> (

let uu____2288 = (FStar_Options.debug_any ())
in (match (uu____2288) with
| true -> begin
(

let uu____2289 = (string_of_repl_task task)
in (FStar_Util.print2 "%s %s" verb uu____2289))
end
| uu____2290 -> begin
()
end)))
in (

let rec revert_many = (fun st1 uu___446_2311 -> (match (uu___446_2311) with
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

let uu___465_2362 = st'
in (

let uu____2363 = (FStar_TypeChecker_Env.set_dep_graph st'.repl_env dep_graph1)
in {repl_line = uu___465_2362.repl_line; repl_column = uu___465_2362.repl_column; repl_fname = uu___465_2362.repl_fname; repl_deps_stack = uu___465_2362.repl_deps_stack; repl_curmod = uu___465_2362.repl_curmod; repl_env = uu____2363; repl_stdin = uu___465_2362.repl_stdin; repl_names = uu___465_2362.repl_names}))
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

let uu____2415 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____2415 (fun a1 -> ())));
(

let timestamped_task = (update_task_timestamps task)
in (

let push_kind = (

let uu____2418 = (FStar_Options.lax ())
in (match (uu____2418) with
| true -> begin
LaxCheck
end
| uu____2419 -> begin
FullCheck
end))
in (

let uu____2420 = (run_repl_transaction st1 push_kind false timestamped_task)
in (match (uu____2420) with
| (success, st2) -> begin
(match (success) with
| true -> begin
(

let uu____2435 = (

let uu___466_2436 = st2
in (

let uu____2437 = (FStar_ST.op_Bang repl_stack)
in {repl_line = uu___466_2436.repl_line; repl_column = uu___466_2436.repl_column; repl_fname = uu___466_2436.repl_fname; repl_deps_stack = uu____2437; repl_curmod = uu___466_2436.repl_curmod; repl_env = uu___466_2436.repl_env; repl_stdin = uu___466_2436.repl_stdin; repl_names = uu___466_2436.repl_names}))
in (aux uu____2435 tasks2 []))
end
| uu____2467 -> begin
FStar_Util.Inr (st2)
end)
end))));
)
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____2480 = (update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev)) uu____2480)) -> begin
((debug1 "Skipping" task);
(aux st1 tasks2 previous1);
)
end
| (tasks2, previous1) -> begin
(

let uu____2496 = (revert_many st1 previous1)
in (aux uu____2496 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.repl_deps_stack))))))


let json_debug : FStar_Util.json  ->  Prims.string = (fun uu___447_2509 -> (match (uu___447_2509) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____2511 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____2513 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____2513))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____2515) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____2518) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2538) -> begin
true
end
| uu____2543 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2558) -> begin
uu____2558
end))


let js_fail : 'Auu____2569 . Prims.string  ->  FStar_Util.json  ->  'Auu____2569 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___448_2584 -> (match (uu___448_2584) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___449_2591 -> (match (uu___449_2591) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____2600 . (FStar_Util.json  ->  'Auu____2600)  ->  FStar_Util.json  ->  'Auu____2600 Prims.list = (fun k uu___450_2615 -> (match (uu___450_2615) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___451_2634 -> (match (uu___451_2634) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____2660 = (js_str s)
in (match (uu____2660) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____2661 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Env.step = (fun s -> (

let uu____2667 = (js_str s)
in (match (uu____2667) with
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
| uu____2668 -> begin
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
| uu____2688 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____2695 -> begin
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
| uu____2713 -> begin
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

let uu____2743 = (js_str k1)
in (match (uu____2743) with
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
| uu____2744 -> begin
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
| uu____2750 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____2756 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____2762 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____2768 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____2779 = (js_str k1)
in (match (uu____2779) with
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
| uu____2780 -> begin
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
| uu____2877 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____2883 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____2889 -> begin
false
end))


let uu___is_Segment : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
true
end
| uu____2896 -> begin
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
| uu____2909 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____2916 -> begin
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
| uu____2936 -> begin
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
| uu____2972 -> begin
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
| uu____3010 -> begin
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
| uu____3068 -> begin
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
| uu____3106 -> begin
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
| uu____3120 -> begin
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
| uu____3134 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___452_3160 -> (match (uu___452_3160) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Segment (uu____3161) -> begin
false
end
| Pop -> begin
false
end
| Push ({push_kind = uu____3162; push_code = uu____3163; push_line = uu____3164; push_column = uu____3165; push_peek_only = false}) -> begin
false
end
| VfsAdd (uu____3166) -> begin
false
end
| GenericError (uu____3173) -> begin
false
end
| ProtocolViolation (uu____3174) -> begin
false
end
| Push (uu____3175) -> begin
true
end
| AutoComplete (uu____3176) -> begin
true
end
| Lookup (uu____3181) -> begin
true
end
| Compute (uu____3194) -> begin
true
end
| Search (uu____3203) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::("segment")::("vfs-add")::("tactic-ranges")::("interrupt")::("progress")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3215) -> begin
true
end
| uu____3216 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3223) -> begin
uu____3223
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____3229 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____3235 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____3241 -> begin
false
end))


let try_assoc : 'Auu____3250 'Auu____3251 . 'Auu____3250  ->  ('Auu____3250 * 'Auu____3251) Prims.list  ->  'Auu____3251 FStar_Pervasives_Native.option = (fun key a -> (

let uu____3276 = (FStar_Util.try_find (fun uu____3290 -> (match (uu____3290) with
| (k, uu____3296) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____3276)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____3316 = (

let uu____3317 = (

let uu____3318 = (json_debug got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____3318))
in ProtocolViolation (uu____3317))
in {qq = uu____3316; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____3352 = (try_assoc key a)
in (match (uu____3352) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3356 = (

let uu____3357 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____3357))
in (FStar_Exn.raise uu____3356))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____3372 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____3372 js_str))
in (FStar_All.try_with (fun uu___468_3379 -> (match (()) with
| () -> begin
(

let query = (

let uu____3381 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____3381 js_str))
in (

let args = (

let uu____3389 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____3389 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____3410 = (try_assoc k args)
in (match (uu____3410) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____3418 = (match (query) with
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

let uu____3419 = (

let uu____3420 = (arg "code")
in (FStar_All.pipe_right uu____3420 js_str))
in Segment (uu____3419))
end
| "peek" -> begin
(

let uu____3421 = (

let uu____3422 = (

let uu____3423 = (arg "kind")
in (FStar_All.pipe_right uu____3423 js_pushkind))
in (

let uu____3424 = (

let uu____3425 = (arg "code")
in (FStar_All.pipe_right uu____3425 js_str))
in (

let uu____3426 = (

let uu____3427 = (arg "line")
in (FStar_All.pipe_right uu____3427 js_int))
in (

let uu____3428 = (

let uu____3429 = (arg "column")
in (FStar_All.pipe_right uu____3429 js_int))
in {push_kind = uu____3422; push_code = uu____3424; push_line = uu____3426; push_column = uu____3428; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3421))
end
| "push" -> begin
(

let uu____3430 = (

let uu____3431 = (

let uu____3432 = (arg "kind")
in (FStar_All.pipe_right uu____3432 js_pushkind))
in (

let uu____3433 = (

let uu____3434 = (arg "code")
in (FStar_All.pipe_right uu____3434 js_str))
in (

let uu____3435 = (

let uu____3436 = (arg "line")
in (FStar_All.pipe_right uu____3436 js_int))
in (

let uu____3437 = (

let uu____3438 = (arg "column")
in (FStar_All.pipe_right uu____3438 js_int))
in {push_kind = uu____3431; push_code = uu____3433; push_line = uu____3435; push_column = uu____3437; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3430))
end
| "autocomplete" -> begin
(

let uu____3439 = (

let uu____3444 = (

let uu____3445 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____3445 js_str))
in (

let uu____3446 = (

let uu____3447 = (try_arg "context")
in (FStar_All.pipe_right uu____3447 js_optional_completion_context))
in ((uu____3444), (uu____3446))))
in AutoComplete (uu____3439))
end
| "lookup" -> begin
(

let uu____3452 = (

let uu____3465 = (

let uu____3466 = (arg "symbol")
in (FStar_All.pipe_right uu____3466 js_str))
in (

let uu____3467 = (

let uu____3468 = (try_arg "context")
in (FStar_All.pipe_right uu____3468 js_optional_lookup_context))
in (

let uu____3473 = (

let uu____3476 = (

let uu____3485 = (try_arg "location")
in (FStar_All.pipe_right uu____3485 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____3476 (FStar_Util.map_option (fun loc -> (

let uu____3537 = (

let uu____3538 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____3538 js_str))
in (

let uu____3539 = (

let uu____3540 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____3540 js_int))
in (

let uu____3541 = (

let uu____3542 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____3542 js_int))
in ((uu____3537), (uu____3539), (uu____3541)))))))))
in (

let uu____3543 = (

let uu____3546 = (arg "requested-info")
in (FStar_All.pipe_right uu____3546 (js_list js_str)))
in ((uu____3465), (uu____3467), (uu____3473), (uu____3543))))))
in Lookup (uu____3452))
end
| "compute" -> begin
(

let uu____3553 = (

let uu____3562 = (

let uu____3563 = (arg "term")
in (FStar_All.pipe_right uu____3563 js_str))
in (

let uu____3564 = (

let uu____3569 = (try_arg "rules")
in (FStar_All.pipe_right uu____3569 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____3562), (uu____3564))))
in Compute (uu____3553))
end
| "search" -> begin
(

let uu____3584 = (

let uu____3585 = (arg "terms")
in (FStar_All.pipe_right uu____3585 js_str))
in Search (uu____3584))
end
| "vfs-add" -> begin
(

let uu____3586 = (

let uu____3593 = (

let uu____3596 = (try_arg "filename")
in (FStar_All.pipe_right uu____3596 (FStar_Util.map_option js_str)))
in (

let uu____3603 = (

let uu____3604 = (arg "contents")
in (FStar_All.pipe_right uu____3604 js_str))
in ((uu____3593), (uu____3603))))
in VfsAdd (uu____3586))
end
| uu____3607 -> begin
(

let uu____3608 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____3608))
end)
in {qq = uu____3418; qid = qid})))))
end)) (fun uu___467_3611 -> (match (uu___467_3611) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let deserialize_interactive_query : FStar_Util.json  ->  query = (fun js_query -> (FStar_All.try_with (fun uu___470_3621 -> (match (()) with
| () -> begin
(unpack_interactive_query js_query)
end)) (fun uu___469_3624 -> (match (uu___469_3624) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let parse_interactive_query : Prims.string  ->  query = (fun query_str -> (

let uu____3633 = (FStar_Util.json_of_string query_str)
in (match (uu____3633) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(deserialize_interactive_query request)
end)))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (

let uu____3642 = (FStar_Util.read_line stream)
in (match (uu____3642) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(parse_interactive_query line)
end)))


let json_of_opt : 'Auu____3652 . ('Auu____3652  ->  FStar_Util.json)  ->  'Auu____3652 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____3672 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____3672)))


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

let uu____3685 = (

let uu____3692 = (

let uu____3699 = (

let uu____3706 = (

let uu____3711 = (

let uu____3712 = (

let uu____3715 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3721 = (FStar_Range.json_of_use_range r)
in (uu____3721)::[])
end)
in (

let uu____3722 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (

let uu____3728 = (FStar_Range.def_range r)
in (

let uu____3729 = (FStar_Range.use_range r)
in (Prims.op_disEquality uu____3728 uu____3729))) -> begin
(

let uu____3730 = (FStar_Range.json_of_def_range r)
in (uu____3730)::[])
end
| uu____3731 -> begin
[]
end)
in (FStar_List.append uu____3715 uu____3722)))
in FStar_Util.JsonList (uu____3712))
in (("ranges"), (uu____3711)))
in (uu____3706)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____3699)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____3692)
in FStar_Util.JsonAssoc (uu____3685)))

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

let uu____3900 = (

let uu____3907 = (

let uu____3912 = (json_of_opt FStar_Range.json_of_def_range lr.slr_def_range)
in (("defined-at"), (uu____3912)))
in (

let uu____3913 = (

let uu____3920 = (

let uu____3925 = (json_of_opt (fun _0_2 -> FStar_Util.JsonStr (_0_2)) lr.slr_typ)
in (("type"), (uu____3925)))
in (

let uu____3926 = (

let uu____3933 = (

let uu____3938 = (json_of_opt (fun _0_3 -> FStar_Util.JsonStr (_0_3)) lr.slr_doc)
in (("documentation"), (uu____3938)))
in (

let uu____3939 = (

let uu____3946 = (

let uu____3951 = (json_of_opt (fun _0_4 -> FStar_Util.JsonStr (_0_4)) lr.slr_def)
in (("definition"), (uu____3951)))
in (uu____3946)::[])
in (uu____3933)::uu____3939))
in (uu____3920)::uu____3926))
in (uu____3907)::uu____3913))
in ((("name"), (FStar_Util.JsonStr (lr.slr_name))))::uu____3900))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3984 = (FStar_List.map (fun _0_5 -> FStar_Util.JsonStr (_0_5)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_6 -> FStar_Util.JsonList (_0_6)) uu____3984))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____4006 -> begin
false
end))


let uu___is_OptReset : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReset -> begin
true
end
| uu____4012 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____4018 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___453_4023 -> (match (uu___453_4023) with
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


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___454_4216 -> (match (uu___454_4216) with
| FStar_Options.Const (uu____4217) -> begin
"flag"
end
| FStar_Options.IntStr (uu____4218) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____4219) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____4220) -> begin
"string"
end
| FStar_Options.EnumStr (uu____4221) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____4224) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____4231, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____4241, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let rec snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.strcat "${" (Prims.strcat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.strcat "--" (Prims.strcat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.strcat " " argstring)
end
| uu____4278 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____4289) -> begin
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
| FStar_Options.PostProcessed (uu____4302, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____4312, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____4320 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____4320))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___455_4327 -> (match (uu___455_4327) with
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

let uu____4335 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____4335))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____4349 = (

let uu____4356 = (

let uu____4363 = (

let uu____4368 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____4368)))
in (

let uu____4369 = (

let uu____4376 = (

let uu____4381 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____4381)))
in (

let uu____4382 = (

let uu____4389 = (

let uu____4394 = (json_of_opt (fun _0_7 -> FStar_Util.JsonStr (_0_7)) opt.opt_documentation)
in (("documentation"), (uu____4394)))
in (

let uu____4395 = (

let uu____4402 = (

let uu____4407 = (

let uu____4408 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____4408))
in (("type"), (uu____4407)))
in (uu____4402)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____4389)::uu____4395))
in (uu____4376)::uu____4382))
in (uu____4363)::uu____4369))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____4356)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____4349))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____4446 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____4446)))


let write_json : FStar_Util.json  ->  unit = (fun json -> ((

let uu____4459 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____4459));
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

let uu____4522 = (

let uu____4529 = (

let uu____4536 = (

let uu____4541 = (

let uu____4542 = (FStar_ST.op_Bang repl_current_qid)
in (json_of_opt (fun _0_8 -> FStar_Util.JsonStr (_0_8)) uu____4542))
in (("query-id"), (uu____4541)))
in (uu____4536)::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (js_contents)))::[])
in ((("kind"), (FStar_Util.JsonStr ("message"))))::uu____4529)
in FStar_Util.JsonAssoc (uu____4522)))


let forward_message : 'Auu____4596 . (FStar_Util.json  ->  'Auu____4596)  ->  Prims.string  ->  FStar_Util.json  ->  'Auu____4596 = (fun callback level contents -> (

let uu____4617 = (json_of_message level contents)
in (callback uu____4617)))


let json_of_hello : FStar_Util.json = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4620 = (FStar_List.map (fun _0_9 -> FStar_Util.JsonStr (_0_9)) interactive_protocol_features)
in FStar_Util.JsonList (uu____4620))
in FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info)))


let write_hello : unit  ->  unit = (fun uu____4631 -> (write_json json_of_hello))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.strcat "--" name)
in (

let uu____4643 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____4643) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.strcat flag (Prims.strcat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____4652 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____4683 -> (match (uu____4683) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____4701 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____4701 (FStar_Util.map_option (fun default_value -> (

let uu____4713 = (sig_of_fstar_option name typ)
in (

let uu____4714 = (snippets_of_fstar_option name typ)
in (

let uu____4717 = (

let uu____4718 = (FStar_Options.settable name)
in (match (uu____4718) with
| true -> begin
OptSet
end
| uu____4719 -> begin
(

let uu____4720 = (FStar_Options.resettable name)
in (match (uu____4720) with
| true -> begin
OptReset
end
| uu____4721 -> begin
OptReadOnly
end))
end))
in {opt_name = name; opt_sig = uu____4713; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____4714; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4724 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____4717})))))))
end))))
in (FStar_All.pipe_right uu____4652 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___471_4746 = opt
in (

let uu____4747 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___471_4746.opt_name; opt_sig = uu___471_4746.opt_sig; opt_value = uu____4747; opt_default = uu___471_4746.opt_default; opt_type = uu___471_4746.opt_type; opt_snippets = uu___471_4746.opt_snippets; opt_documentation = uu___471_4746.opt_documentation; opt_permission_level = uu___471_4746.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____4760 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____4760)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____4777 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____4777)))
end
| uu____4778 -> begin
((""), (opt_name))
end)))


let json_of_repl_state : repl_state  ->  FStar_Util.json = (fun st -> (

let filenames = (fun uu____4799 -> (match (uu____4799) with
| (uu____4810, (task, uu____4812)) -> begin
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
| uu____4823 -> begin
[]
end)
end))
in (

let uu____4824 = (

let uu____4831 = (

let uu____4836 = (

let uu____4837 = (

let uu____4840 = (FStar_List.concatMap filenames st.repl_deps_stack)
in (FStar_List.map (fun _0_10 -> FStar_Util.JsonStr (_0_10)) uu____4840))
in FStar_Util.JsonList (uu____4837))
in (("loaded-dependencies"), (uu____4836)))
in (

let uu____4851 = (

let uu____4858 = (

let uu____4863 = (

let uu____4864 = (

let uu____4867 = (current_fstar_options (fun uu____4872 -> true))
in (FStar_List.map json_of_fstar_option uu____4867))
in FStar_Util.JsonList (uu____4864))
in (("options"), (uu____4863)))
in (uu____4858)::[])
in (uu____4831)::uu____4851))
in FStar_Util.JsonAssoc (uu____4824))))


let with_printed_effect_args : 'Auu____4889 . (unit  ->  'Auu____4889)  ->  'Auu____4889 = (fun k -> (FStar_Options.with_saved_options (fun uu____4902 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____4915 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____4922 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____4929 'Auu____4930 . 'Auu____4929  ->  ((query_status * FStar_Util.json) * ('Auu____4930, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____4962 'Auu____4963 . 'Auu____4962  ->  ((query_status * FStar_Util.json) * ('Auu____4962, 'Auu____4963) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____4993 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4993) FStar_Util.either) = (fun st -> (

let uu____5011 = (

let uu____5016 = (json_of_repl_state st)
in ((QueryOK), (uu____5016)))
in ((uu____5011), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____5033 'Auu____5034 . 'Auu____5033  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____5033, 'Auu____5034) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_generic_error : 'Auu____5073 'Auu____5074 . 'Auu____5073  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____5073, 'Auu____5074) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let collect_errors : unit  ->  FStar_Errors.issue Prims.list = (fun uu____5111 -> (

let errors = (FStar_Errors.report_all ())
in ((FStar_Errors.clear ());
errors;
)))


let run_segment : 'Auu____5122 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5122) FStar_Util.either) = (fun st code -> (

let frag = {FStar_Parser_ParseIt.frag_text = code; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let collect_decls = (fun uu____5153 -> (

let uu____5154 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____5154) with
| FStar_Parser_Driver.Empty -> begin
[]
end
| FStar_Parser_Driver.Decls (decls) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu____5160, decls)) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface (uu____5166, decls, uu____5168)) -> begin
decls
end)))
in (

let uu____5173 = (with_captured_errors st.repl_env FStar_Util.sigint_ignore (fun uu____5182 -> (

let uu____5183 = (collect_decls ())
in (FStar_All.pipe_left (fun _0_11 -> FStar_Pervasives_Native.Some (_0_11)) uu____5183))))
in (match (uu____5173) with
| FStar_Pervasives_Native.None -> begin
(

let errors = (

let uu____5211 = (collect_errors ())
in (FStar_All.pipe_right uu____5211 (FStar_List.map json_of_issue)))
in ((((QueryNOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl (st))))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let json_of_decl = (fun decl -> (

let uu____5237 = (

let uu____5244 = (

let uu____5249 = (FStar_Range.json_of_def_range (FStar_Parser_AST.decl_drange decl))
in (("def_range"), (uu____5249)))
in (uu____5244)::[])
in FStar_Util.JsonAssoc (uu____5237)))
in (

let js_decls = (

let uu____5259 = (FStar_List.map json_of_decl decls)
in (FStar_All.pipe_left (fun _0_12 -> FStar_Util.JsonList (_0_12)) uu____5259))
in ((((QueryOK), (FStar_Util.JsonAssoc (((("decls"), (js_decls)))::[])))), (FStar_Util.Inl (st)))))
end)))))


let run_vfs_add : 'Auu____5288 . repl_state  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5288) FStar_Util.either) = (fun st opt_fname contents -> (

let fname = (FStar_Util.dflt st.repl_fname opt_fname)
in ((FStar_Parser_ParseIt.add_vfs_entry fname contents);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st)));
)))


let run_pop : 'Auu____5334 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5334) FStar_Util.either) = (fun st -> (

let uu____5352 = (nothing_left_to_pop st)
in (match (uu____5352) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____5373 -> begin
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

let uu____5422 = (json_of_message "progress" (FStar_Util.JsonAssoc (js_contents)))
in (write_json uu____5422)))))


let write_repl_ld_task_progress : repl_task  ->  unit = (fun task -> (match (task) with
| LDInterleaved (uu____5428, tf) -> begin
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
| uu____5459 -> begin
()
end))


let load_deps : repl_state  ->  ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either = (fun st -> (

let uu____5475 = (with_captured_errors st.repl_env FStar_Util.sigint_ignore (fun _env -> (

let uu____5501 = (deps_and_repl_ld_tasks_of_our_file st.repl_fname)
in (FStar_All.pipe_left (fun _0_13 -> FStar_Pervasives_Native.Some (_0_13)) uu____5501))))
in (match (uu____5475) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (st)
end
| FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___472_5592 = st
in (

let uu____5593 = (FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1)
in {repl_line = uu___472_5592.repl_line; repl_column = uu___472_5592.repl_column; repl_fname = uu___472_5592.repl_fname; repl_deps_stack = uu___472_5592.repl_deps_stack; repl_curmod = uu___472_5592.repl_curmod; repl_env = uu____5593; repl_stdin = uu___472_5592.repl_stdin; repl_names = uu___472_5592.repl_names}))
in (

let uu____5594 = (run_repl_ld_transactions st1 tasks write_repl_ld_task_progress)
in (match (uu____5594) with
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

let uu___473_5640 = issue
in (

let uu____5641 = (FStar_Util.format1 "Error while computing or loading dependencies:\n%s" issue.FStar_Errors.issue_message)
in {FStar_Errors.issue_message = uu____5641; FStar_Errors.issue_level = uu___473_5640.FStar_Errors.issue_level; FStar_Errors.issue_range = uu___473_5640.FStar_Errors.issue_range; FStar_Errors.issue_number = uu___473_5640.FStar_Errors.issue_number})))


let run_push_without_deps : 'Auu____5648 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5648) FStar_Util.either) = (fun st query -> (

let set_nosynth_flag = (fun st1 flag -> (

let uu___474_5682 = st1
in {repl_line = uu___474_5682.repl_line; repl_column = uu___474_5682.repl_column; repl_fname = uu___474_5682.repl_fname; repl_deps_stack = uu___474_5682.repl_deps_stack; repl_curmod = uu___474_5682.repl_curmod; repl_env = (

let uu___475_5684 = st1.repl_env
in {FStar_TypeChecker_Env.solver = uu___475_5684.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___475_5684.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___475_5684.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___475_5684.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___475_5684.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___475_5684.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___475_5684.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___475_5684.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___475_5684.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___475_5684.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___475_5684.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___475_5684.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___475_5684.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___475_5684.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___475_5684.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___475_5684.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___475_5684.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___475_5684.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___475_5684.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___475_5684.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___475_5684.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___475_5684.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___475_5684.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___475_5684.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = flag; FStar_TypeChecker_Env.uvar_subtyping = uu___475_5684.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___475_5684.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___475_5684.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___475_5684.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___475_5684.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___475_5684.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___475_5684.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___475_5684.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___475_5684.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___475_5684.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___475_5684.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___475_5684.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___475_5684.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___475_5684.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___475_5684.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___475_5684.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___475_5684.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___475_5684.FStar_TypeChecker_Env.nbe}); repl_stdin = uu___474_5682.repl_stdin; repl_names = uu___474_5682.repl_names}))
in (

let uu____5685 = query
in (match (uu____5685) with
| {push_kind = push_kind; push_code = text; push_line = line; push_column = column; push_peek_only = peek_only} -> begin
(

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in ((FStar_TypeChecker_Env.toggle_id_info st.repl_env true);
(

let st1 = (set_nosynth_flag st peek_only)
in (

let uu____5706 = (run_repl_transaction st1 push_kind peek_only (PushFragment (frag)))
in (match (uu____5706) with
| (success, st2) -> begin
(

let st3 = (set_nosynth_flag st2 false)
in (

let status = (match ((success || peek_only)) with
| true -> begin
QueryOK
end
| uu____5727 -> begin
QueryNOK
end)
in (

let json_errors = (

let uu____5729 = (

let uu____5732 = (collect_errors ())
in (FStar_All.pipe_right uu____5732 (FStar_List.map json_of_issue)))
in FStar_Util.JsonList (uu____5729))
in (

let st4 = (match (success) with
| true -> begin
(

let uu___476_5740 = st3
in {repl_line = line; repl_column = column; repl_fname = uu___476_5740.repl_fname; repl_deps_stack = uu___476_5740.repl_deps_stack; repl_curmod = uu___476_5740.repl_curmod; repl_env = uu___476_5740.repl_env; repl_stdin = uu___476_5740.repl_stdin; repl_names = uu___476_5740.repl_names})
end
| uu____5741 -> begin
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
| uu____5755 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____5757 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat (FStar_String.uppercase first) uu____5757)))
end))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____5787 = (FStar_Util.psmap_empty ())
in (

let uu____5790 = (

let uu____5793 = (FStar_Options.prims ())
in (uu____5793)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____5803 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____5803 true))) uu____5787 uu____5790)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____5821 -> (match (uu____5821) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____5829 -> begin
(

let ns_query = (

let uu____5833 = (capitalize modname)
in (FStar_Util.split uu____5833 "."))
in (

let uu____5834 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____5834 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods)))))))


let run_push_with_deps : 'Auu____5845 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5845) FStar_Util.either) = (fun st query -> ((

let uu____5869 = (FStar_Options.debug_any ())
in (match (uu____5869) with
| true -> begin
(FStar_Util.print_string "Reloading dependencies")
end
| uu____5870 -> begin
()
end));
(FStar_TypeChecker_Env.toggle_id_info st.repl_env false);
(

let uu____5872 = (load_deps st)
in (match (uu____5872) with
| FStar_Util.Inr (st1) -> begin
(

let errors = (

let uu____5905 = (collect_errors ())
in (FStar_List.map rephrase_dependency_error uu____5905))
in (

let js_errors = (FStar_All.pipe_right errors (FStar_List.map json_of_issue))
in ((((QueryNOK), (FStar_Util.JsonList (js_errors)))), (FStar_Util.Inl (st1)))))
end
| FStar_Util.Inl (st1, deps) -> begin
((

let uu____5936 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____5936 (fun a2 -> ())));
(

let names1 = (add_module_completions st1.repl_fname deps st1.repl_names)
in (run_push_without_deps (

let uu___477_5939 = st1
in {repl_line = uu___477_5939.repl_line; repl_column = uu___477_5939.repl_column; repl_fname = uu___477_5939.repl_fname; repl_deps_stack = uu___477_5939.repl_deps_stack; repl_curmod = uu___477_5939.repl_curmod; repl_env = uu___477_5939.repl_env; repl_stdin = uu___477_5939.repl_stdin; repl_names = names1}) query));
)
end));
))


let run_push : 'Auu____5946 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5946) FStar_Util.either) = (fun st query -> (

let uu____5969 = (nothing_left_to_pop st)
in (match (uu____5969) with
| true -> begin
(run_push_with_deps st query)
end
| uu____5982 -> begin
(run_push_without_deps st query)
end)))


let run_symbol_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let tcenv = st.repl_env
in (

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____6057 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____6057))
in (

let lid1 = (

let uu____6061 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____6061))
in (

let uu____6066 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____6066 (FStar_Util.map_option (fun uu____6121 -> (match (uu____6121) with
| ((uu____6140, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____6159 = (FStar_Syntax_DsEnv.try_lookup_doc tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____6159 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____6210 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____6210 (fun uu___456_6254 -> (match (uu___456_6254) with
| (FStar_Util.Inr (se, uu____6276), uu____6277) -> begin
(

let uu____6306 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____6306))
end
| uu____6307 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____6359 -> (match (uu____6359) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____6406) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6459 -> begin
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

let uu____6534 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____6534))
end
| uu____6535 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____6542 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____6553 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range1 = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____6563 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {slr_name = name; slr_def_range = def_range1; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}
in (

let uu____6565 = (

let uu____6576 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____6576)))
in FStar_Pervasives_Native.Some (uu____6565))))))))
end)
in (match (response) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (info) -> begin
FStar_Util.Inr (info)
end)))))))))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____6683 = (trim_option_name opt_name)
in (match (uu____6683) with
| (uu____6702, trimmed_name) -> begin
(

let uu____6704 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____6704) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.strcat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____6732 = (

let uu____6743 = (

let uu____6750 = (update_option opt)
in (alist_of_fstar_option uu____6750))
in (("option"), (uu____6743)))
in FStar_Util.Inr (uu____6732))
end))
end)))


let run_module_lookup : repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____6794 = (FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names query)
in (match (uu____6794) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____6822 = (

let uu____6833 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____6833)))
in FStar_Util.Inr (uu____6822))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____6857 = (

let uu____6868 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____6868)))
in FStar_Util.Inr (uu____6857))
end))))


let run_code_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____6945 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____6945) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____7005) -> begin
(

let uu____7016 = (run_module_lookup st symbol)
in (match (uu____7016) with
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


let run_lookup : 'Auu____7182 . repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7182) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____7240 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____7240) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let code_autocomplete_mod_filter : 'Auu____7326 . ('Auu____7326 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____7326 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___457_7341 -> (match (uu___457_7341) with
| (uu____7346, FStar_Interactive_CompletionTable.Namespace (uu____7347)) -> begin
FStar_Pervasives_Native.None
end
| (uu____7352, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____7353; FStar_Interactive_CompletionTable.mod_path = uu____7354; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____7361 = (

let uu____7366 = (

let uu____7367 = (

let uu___478_7368 = md
in (

let uu____7369 = (

let uu____7370 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.strcat uu____7370 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____7369; FStar_Interactive_CompletionTable.mod_path = uu___478_7368.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___478_7368.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____7367))
in ((pth), (uu____7366)))
in FStar_Pervasives_Native.Some (uu____7361))
end))


let run_code_autocomplete : 'Auu____7381 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7381) FStar_Util.either) = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names needle)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result (FStar_List.append lids mods_and_nss))
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st))))))))


let run_module_autocomplete : 'Auu____7438 'Auu____7439 'Auu____7440 . repl_state  ->  Prims.string  ->  'Auu____7438  ->  'Auu____7439  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7440) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : Prims.int  ->  Prims.bool  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____7511 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReset -> begin
((is_reset), ("#reset-only"))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____7511) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____7526 -> begin
(Prims.strcat "(" (Prims.strcat explanation (Prims.strcat " " (Prims.strcat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____7543 'Auu____7544 . 'Auu____7543  ->  Prims.string  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * ('Auu____7543, 'Auu____7544) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____7572 = (trim_option_name search_term)
in (match (uu____7572) with
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
| (uu____7627, uu____7628) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____7645 . repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7645) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_and_rewind : 'Auu____7686 'Auu____7687 . repl_state  ->  'Auu____7686  ->  (repl_state  ->  'Auu____7686)  ->  ('Auu____7686 * (repl_state, 'Auu____7687) FStar_Util.either) = (fun st sigint_default task -> (

let st1 = (push_repl "run_and_rewind" FullCheck Noop st)
in (

let results = (FStar_All.try_with (fun uu___480_7727 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler FStar_Util.sigint_raise (fun uu____7738 -> (

let uu____7739 = (task st1)
in (FStar_All.pipe_left (fun _0_15 -> FStar_Util.Inl (_0_15)) uu____7739))))
end)) (fun uu___479_7745 -> (match (uu___479_7745) with
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


let run_with_parsed_and_tc_term : 'Auu____7790 'Auu____7791 'Auu____7792 . repl_state  ->  Prims.string  ->  'Auu____7790  ->  'Auu____7791  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (query_status * FStar_Util.json))  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7792) FStar_Util.either) = (fun st term line column continuation -> (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____7885, ({FStar_Syntax_Syntax.lbname = uu____7886; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____7888; FStar_Syntax_Syntax.lbeff = uu____7889; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____7891; FStar_Syntax_Syntax.lbpos = uu____7892})::[]), uu____7893); FStar_Syntax_Syntax.sigrng = uu____7894; FStar_Syntax_Syntax.sigquals = uu____7895; FStar_Syntax_Syntax.sigmeta = uu____7896; FStar_Syntax_Syntax.sigattrs = uu____7897})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____7934 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____7955 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____7955) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____7961) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____7980 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun env decls -> (

let uu____7998 = (

let uu____8003 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts decls)
in (uu____8003 env.FStar_TypeChecker_Env.dsenv))
in (FStar_Pervasives_Native.fst uu____7998)))
in (

let typecheck = (fun tcenv decls -> (

let uu____8027 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____8027) with
| (ses, uu____8041, uu____8042) -> begin
ses
end)))
in (run_and_rewind st ((QueryNOK), (FStar_Util.JsonStr ("Computation interrupted"))) (fun st1 -> (

let tcenv = st1.repl_env
in (

let frag = (dummy_let_fragment term)
in (

let uu____8062 = (parse1 frag)
in (match (uu____8062) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____8087 -> (

let decls1 = (desugar tcenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____8122 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____8122) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (continuation tcenv1 def1))
end))
end))))
in (

let uu____8134 = (FStar_Options.trace_error ())
in (match (uu____8134) with
| true -> begin
(aux ())
end
| uu____8139 -> begin
(FStar_All.try_with (fun uu___482_8145 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___481_8154 -> (

let uu____8159 = (FStar_Errors.issue_of_exn uu___481_8154)
in (match (uu____8159) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____8167 = (

let uu____8168 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____8168))
in ((QueryNOK), (uu____8167)))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise uu___481_8154)
end))))
end)))
end))))))))))))


let run_compute : 'Auu____8181 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8181) FStar_Util.either) = (fun st term rules -> (

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

let uu____8253 = (

let uu____8254 = (term_to_string tcenv normalized)
in FStar_Util.JsonStr (uu____8254))
in ((QueryOK), (uu____8253)))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____8281 -> begin
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
| uu____8295 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___458_8321 -> (match (uu___458_8321) with
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

let uu____8536 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____8543 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____8536; sc_fvars = uu____8543})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____8610 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____8610) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____8638 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____8638) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____8657, typ), uu____8659) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lident FStar_Util.set = (fun tcenv sc -> (

let uu____8708 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____8708) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____8752 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____8752))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun tcenv sc -> (

let typ_str = (

let uu____8794 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____8794))
in (

let uu____8795 = (

let uu____8802 = (

let uu____8807 = (

let uu____8808 = (

let uu____8809 = (FStar_Syntax_DsEnv.shorten_lid tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid)
in uu____8809.FStar_Ident.str)
in FStar_Util.JsonStr (uu____8808))
in (("lid"), (uu____8807)))
in (uu____8802)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____8795))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____8831) -> begin
true
end
| uu____8832 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____8839) -> begin
uu____8839
end))


let run_search : 'Auu____8846 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8846) FStar_Util.either) = (fun st search_str -> (

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

let uu____8887 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____8887))
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
| uu____8906 -> begin
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
| uu____8915 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____8917 = (

let uu____8918 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____8918))
in (FStar_Exn.raise uu____8917))
end
| uu____8919 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____8920 = (strip_quotes term1)
in NameContainsStr (uu____8920))
end
| uu____8921 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____8923 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____8923) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8926 = (

let uu____8927 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____8927))
in (FStar_Exn.raise uu____8926))
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

let uu____8949 = (match (term.st_term) with
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
| uu____8952 -> begin
""
end) uu____8949)))
in (

let results = (FStar_All.try_with (fun uu___484_8973 -> (match (()) with
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

let uu____9018 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____9018))
in (

let uu____9021 = (

let uu____9022 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____9022))
in (FStar_Exn.raise uu____9021)))
end
| uu____9027 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___483_9032 -> (match (uu___483_9032) with
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
| Push ({push_kind = SyntaxCheck; push_code = uu____9125; push_line = uu____9126; push_column = uu____9127; push_peek_only = false}) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____9128 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = GenericError ("Current module unset"); qid = q.qid}
end
| uu____9129 -> begin
q
end)
end))


let validate_and_run_query : repl_state  ->  query  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let query1 = (validate_query st query)
in ((FStar_ST.op_Colon_Equals repl_current_qid (FStar_Pervasives_Native.Some (query1.qid)));
(run_query st query1.qq);
)))


let js_repl_eval : repl_state  ->  query  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let uu____9195 = (validate_and_run_query st query)
in (match (uu____9195) with
| ((status, response), st_opt) -> begin
(

let js_response = (json_of_response query.qid status response)
in ((js_response), (st_opt)))
end)))


let js_repl_eval_js : repl_state  ->  FStar_Util.json  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query_js -> (

let uu____9254 = (deserialize_interactive_query query_js)
in (js_repl_eval st uu____9254)))


let js_repl_eval_str : repl_state  ->  Prims.string  ->  (Prims.string * (repl_state, Prims.int) FStar_Util.either) = (fun st query_str -> (

let uu____9273 = (

let uu____9282 = (parse_interactive_query query_str)
in (js_repl_eval st uu____9282))
in (match (uu____9273) with
| (js_response, st_opt) -> begin
(

let uu____9301 = (FStar_Util.string_of_json js_response)
in ((uu____9301), (st_opt)))
end)))


let js_repl_init_opts : unit  ->  unit = (fun uu____9310 -> (

let uu____9311 = (FStar_Options.parse_cmd_line ())
in (match (uu____9311) with
| (res, fnames) -> begin
(match (res) with
| FStar_Getopt.Error (msg) -> begin
(failwith (Prims.strcat "repl_init: " msg))
end
| FStar_Getopt.Help -> begin
(failwith "repl_init: --help unexpected")
end
| FStar_Getopt.Success -> begin
(match (fnames) with
| [] -> begin
(failwith "repl_init: No file name given in --ide invocation")
end
| (h)::(uu____9326)::uu____9327 -> begin
(failwith "repl_init: Too many file names given in --ide invocation")
end
| uu____9330 -> begin
()
end)
end)
end)))


let rec go : repl_state  ->  Prims.int = (fun st -> (

let query = (read_interactive_query st.repl_stdin)
in (

let uu____9339 = (validate_and_run_query st query)
in (match (uu____9339) with
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

let uu____9383 = (

let uu____9386 = (FStar_ST.op_Bang issues)
in (e)::uu____9386)
in (FStar_ST.op_Colon_Equals issues uu____9383)))
in (

let count_errors = (fun uu____9484 -> (

let uu____9485 = (

let uu____9488 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____9488))
in (FStar_List.length uu____9485)))
in (

let report = (fun uu____9545 -> (

let uu____9546 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____9546)))
in (

let clear1 = (fun uu____9599 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : (FStar_Util.json  ->  unit)  ->  FStar_Util.printer = (fun printer -> {FStar_Util.printer_prinfo = (fun s -> (forward_message printer "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (forward_message printer "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (forward_message printer "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label get_string get_json -> (

let uu____9677 = (get_json ())
in (forward_message printer label uu____9677)))})


let install_ide_mode_hooks : (FStar_Util.json  ->  unit)  ->  unit = (fun printer -> ((FStar_Util.set_printer (interactive_printer printer));
(FStar_Errors.set_handler interactive_error_handler);
))


let initial_range : FStar_Range.range = (

let uu____9689 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____9690 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____9689 uu____9690)))


let build_initial_repl_state : Prims.string  ->  repl_state = (fun filename -> (

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env initial_range)
in (

let uu____9698 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_deps_stack = []; repl_curmod = FStar_Pervasives_Native.None; repl_env = env1; repl_stdin = uu____9698; repl_names = FStar_Interactive_CompletionTable.empty}))))


let interactive_mode' : 'Auu____9711 . repl_state  ->  'Auu____9711 = (fun init_st -> ((write_hello ());
(

let exit_code = (

let uu____9719 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____9719) with
| true -> begin
(

let uu____9720 = (

let uu____9721 = (FStar_Options.file_list ())
in (FStar_List.hd uu____9721))
in (FStar_SMTEncoding_Solver.with_hints_db uu____9720 (fun uu____9725 -> (go init_st))))
end
| uu____9726 -> begin
(go init_st)
end))
in (FStar_All.exit exit_code));
))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((install_ide_mode_hooks write_json);
(FStar_Util.set_sigint_handler FStar_Util.sigint_ignore);
(

let uu____9735 = (

let uu____9736 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____9736))
in (match (uu____9735) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("--ide: ignoring --codegen")))
end
| uu____9739 -> begin
()
end));
(

let init1 = (build_initial_repl_state filename)
in (

let uu____9741 = (FStar_Options.trace_error ())
in (match (uu____9741) with
| true -> begin
(interactive_mode' init1)
end
| uu____9742 -> begin
(FStar_All.try_with (fun uu___486_9744 -> (match (()) with
| () -> begin
(interactive_mode' init1)
end)) (fun uu___485_9747 -> ((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise uu___485_9747);
)))
end)));
))




