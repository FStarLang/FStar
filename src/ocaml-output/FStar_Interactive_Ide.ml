
open Prims
open FStar_Pervasives
exception ExitREPL of (Prims.int)


let uu___is_ExitREPL : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ExitREPL (uu____10) -> begin
true
end
| uu____11 -> begin
false
end))


let __proj__ExitREPL__item__uu___ : Prims.exn  ->  Prims.int = (fun projectee -> (match (projectee) with
| ExitREPL (uu____18) -> begin
uu____18
end))


let push : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (

let res = (FStar_Universal.push_context env msg)
in ((FStar_Options.push ());
res;
)))


let pop : FStar_TypeChecker_Env.env  ->  Prims.string  ->  unit = (fun env msg -> ((FStar_Universal.pop_context env msg);
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
| uu____47 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____53 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____59 -> begin
false
end))


let set_check_kind : FStar_TypeChecker_Env.env  ->  push_kind  ->  FStar_TypeChecker_Env.env = (fun env check_kind -> (

let uu___90_70 = env
in (

let uu____71 = (FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv (Prims.op_Equality check_kind SyntaxCheck))
in {FStar_TypeChecker_Env.solver = uu___90_70.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___90_70.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___90_70.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___90_70.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___90_70.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___90_70.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___90_70.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___90_70.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___90_70.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___90_70.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___90_70.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___90_70.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___90_70.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___90_70.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___90_70.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___90_70.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___90_70.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___90_70.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___90_70.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality check_kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___90_70.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___90_70.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___90_70.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___90_70.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___90_70.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___90_70.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___90_70.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___90_70.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___90_70.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___90_70.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___90_70.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___90_70.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___90_70.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___90_70.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___90_70.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___90_70.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu____71; FStar_TypeChecker_Env.dep_graph = uu___90_70.FStar_TypeChecker_Env.dep_graph})))


let with_captured_errors' : 'Auu____78 . FStar_TypeChecker_Env.env  ->  (FStar_TypeChecker_Env.env  ->  'Auu____78 FStar_Pervasives_Native.option)  ->  'Auu____78 FStar_Pervasives_Native.option = (fun env f -> (FStar_All.try_with (fun uu___92_103 -> (match (()) with
| () -> begin
(f env)
end)) (fun uu___91_110 -> (match (uu___91_110) with
| FStar_All.Failure (msg) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____116 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.log_issue uu____116 ((FStar_Errors.Error_IDEAssertionFailure), (msg1))));
FStar_Pervasives_Native.None;
))
end
| FStar_Errors.Error (e, msg, r) -> begin
((FStar_TypeChecker_Err.add_errors env ((((e), (msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (e, msg) -> begin
((

let uu____136 = (

let uu____145 = (

let uu____152 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____152)))
in (uu____145)::[])
in (FStar_TypeChecker_Err.add_errors env uu____136));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Stop -> begin
FStar_Pervasives_Native.None
end))))


let with_captured_errors : 'Auu____171 . FStar_TypeChecker_Env.env  ->  (FStar_TypeChecker_Env.env  ->  'Auu____171 FStar_Pervasives_Native.option)  ->  'Auu____171 FStar_Pervasives_Native.option = (fun env f -> (

let uu____193 = (FStar_Options.trace_error ())
in (match (uu____193) with
| true -> begin
(f env)
end
| uu____196 -> begin
(with_captured_errors' env f)
end)))

type timed_fname =
{tf_fname : Prims.string; tf_modtime : FStar_Util.time}


let __proj__Mktimed_fname__item__tf_fname : timed_fname  ->  Prims.string = (fun projectee -> (match (projectee) with
| {tf_fname = __fname__tf_fname; tf_modtime = __fname__tf_modtime} -> begin
__fname__tf_fname
end))


let __proj__Mktimed_fname__item__tf_modtime : timed_fname  ->  FStar_Util.time = (fun projectee -> (match (projectee) with
| {tf_fname = __fname__tf_fname; tf_modtime = __fname__tf_modtime} -> begin
__fname__tf_modtime
end))


let t0 : FStar_Util.time = (FStar_Util.now ())


let tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> (

let uu____226 = (FStar_Parser_ParseIt.get_file_last_modification_time fname)
in {tf_fname = fname; tf_modtime = uu____226}))


let dummy_tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> {tf_fname = fname; tf_modtime = t0})


let string_of_timed_fname : timed_fname  ->  Prims.string = (fun uu____236 -> (match (uu____236) with
| {tf_fname = fname; tf_modtime = modtime} -> begin
(match ((Prims.op_Equality modtime t0)) with
| true -> begin
(FStar_Util.format1 "{ %s }" fname)
end
| uu____239 -> begin
(

let uu____240 = (FStar_Util.string_of_time modtime)
in (FStar_Util.format2 "{ %s; %s }" fname uu____240))
end)
end))

type push_query =
{push_kind : push_kind; push_code : Prims.string; push_line : Prims.int; push_column : Prims.int; push_peek_only : Prims.bool}


let __proj__Mkpush_query__item__push_kind : push_query  ->  push_kind = (fun projectee -> (match (projectee) with
| {push_kind = __fname__push_kind; push_code = __fname__push_code; push_line = __fname__push_line; push_column = __fname__push_column; push_peek_only = __fname__push_peek_only} -> begin
__fname__push_kind
end))


let __proj__Mkpush_query__item__push_code : push_query  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push_kind = __fname__push_kind; push_code = __fname__push_code; push_line = __fname__push_line; push_column = __fname__push_column; push_peek_only = __fname__push_peek_only} -> begin
__fname__push_code
end))


let __proj__Mkpush_query__item__push_line : push_query  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push_kind = __fname__push_kind; push_code = __fname__push_code; push_line = __fname__push_line; push_column = __fname__push_column; push_peek_only = __fname__push_peek_only} -> begin
__fname__push_line
end))


let __proj__Mkpush_query__item__push_column : push_query  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push_kind = __fname__push_kind; push_code = __fname__push_code; push_line = __fname__push_line; push_column = __fname__push_column; push_peek_only = __fname__push_peek_only} -> begin
__fname__push_column
end))


let __proj__Mkpush_query__item__push_peek_only : push_query  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {push_kind = __fname__push_kind; push_code = __fname__push_code; push_line = __fname__push_line; push_column = __fname__push_column; push_peek_only = __fname__push_peek_only} -> begin
__fname__push_peek_only
end))


type optmod_t =
FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option

type repl_task =
| LDInterleaved of (timed_fname * timed_fname)
| LDSingle of timed_fname
| LDInterfaceOfCurrentFile of timed_fname
| PushFragment of FStar_Parser_ParseIt.input_frag


let uu___is_LDInterleaved : repl_task  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LDInterleaved (_0) -> begin
true
end
| uu____352 -> begin
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
| uu____378 -> begin
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
| uu____392 -> begin
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
| uu____406 -> begin
false
end))


let __proj__PushFragment__item___0 : repl_task  ->  FStar_Parser_ParseIt.input_frag = (fun projectee -> (match (projectee) with
| PushFragment (_0) -> begin
_0
end))


type env_t =
FStar_TypeChecker_Env.env

type repl_state =
{repl_line : Prims.int; repl_column : Prims.int; repl_fname : Prims.string; repl_deps_stack : (repl_task * repl_state) Prims.list; repl_curmod : optmod_t; repl_env : env_t; repl_stdin : FStar_Util.stream_reader; repl_names : FStar_Interactive_CompletionTable.table}


let __proj__Mkrepl_state__item__repl_line : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_line
end))


let __proj__Mkrepl_state__item__repl_column : repl_state  ->  Prims.int = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_column
end))


let __proj__Mkrepl_state__item__repl_fname : repl_state  ->  Prims.string = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_fname
end))


let __proj__Mkrepl_state__item__repl_deps_stack : repl_state  ->  (repl_task * repl_state) Prims.list = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_deps_stack
end))


let __proj__Mkrepl_state__item__repl_curmod : repl_state  ->  optmod_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_curmod
end))


let __proj__Mkrepl_state__item__repl_env : repl_state  ->  env_t = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_env
end))


let __proj__Mkrepl_state__item__repl_stdin : repl_state  ->  FStar_Util.stream_reader = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_stdin
end))


let __proj__Mkrepl_state__item__repl_names : repl_state  ->  FStar_Interactive_CompletionTable.table = (fun projectee -> (match (projectee) with
| {repl_line = __fname__repl_line; repl_column = __fname__repl_column; repl_fname = __fname__repl_fname; repl_deps_stack = __fname__repl_deps_stack; repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env; repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names} -> begin
__fname__repl_names
end))


type completed_repl_task =
(repl_task * repl_state)


type repl_stack_t =
(repl_task * repl_state) Prims.list


let repl_stack : repl_stack_t FStar_ST.ref = (FStar_Util.mk_ref [])


let pop_repl : repl_state  ->  repl_state = (fun st -> (

let uu____656 = (FStar_ST.op_Bang repl_stack)
in (match (uu____656) with
| [] -> begin
(failwith "Too many pops")
end
| ((uu____684, st'))::stack -> begin
((pop st.repl_env "#pop");
(FStar_ST.op_Colon_Equals repl_stack stack);
st';
)
end)))


let push_repl : push_kind  ->  repl_task  ->  repl_state  ->  FStar_TypeChecker_Env.env = (fun push_kind task st -> ((

let uu____738 = (

let uu____739 = (FStar_ST.op_Bang repl_stack)
in (((task), (st)))::uu____739)
in (FStar_ST.op_Colon_Equals repl_stack uu____738));
(

let uu____796 = (set_check_kind st.repl_env push_kind)
in (push uu____796 ""));
))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> (

let uu____802 = (

let uu____803 = (FStar_ST.op_Bang repl_stack)
in (FStar_List.length uu____803))
in (Prims.op_Equality uu____802 (FStar_List.length st.repl_deps_stack))))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding) FStar_Util.either


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____895 -> begin
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
| uu____931 -> begin
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
| uu____961 -> begin
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
| uu____991 -> begin
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

let uu____1049 = (FStar_Ident.text_of_id id1)
in (

let uu____1050 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table uu____1049 [] uu____1050)))
end
| uu____1051 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1055 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_Syntax_DsEnv.Open_module) [] uu____1055))
end
| uu____1056 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____1059 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____1060 -> begin
(query_of_lid host)
end)
in (

let uu____1061 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____1059 uu____1061)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid (lid, uu____1073)) -> begin
(lid)::[]
end
| FStar_Util.Inr (lids, uu____1091) -> begin
lids
end
| uu____1096 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____1108 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (

let uu____1109 = (FStar_Ident.text_of_id lid.FStar_Ident.ident)
in (FStar_Interactive_CompletionTable.insert tbl ns_query uu____1109 lid)))) table lids))
end)))


let commit_name_tracking' : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____1135 = (FStar_Syntax_Syntax.mod_name md)
in uu____1135.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let commit_name_tracking : repl_state  ->  name_tracking_event Prims.list  ->  repl_state = (fun st name_events -> (

let names1 = (commit_name_tracking' st.repl_curmod st.repl_names name_events)
in (

let uu___93_1160 = st
in {repl_line = uu___93_1160.repl_line; repl_column = uu___93_1160.repl_column; repl_fname = uu___93_1160.repl_fname; repl_deps_stack = uu___93_1160.repl_deps_stack; repl_curmod = uu___93_1160.repl_curmod; repl_env = uu___93_1160.repl_env; repl_stdin = uu___93_1160.repl_stdin; repl_names = names1})))


let fresh_name_tracking_hooks : unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____1175 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____1189 = (

let uu____1192 = (FStar_ST.op_Bang events)
in (evt)::uu____1192)
in (FStar_ST.op_Colon_Equals events uu____1189)))
in ((events), ({FStar_Syntax_DsEnv.ds_push_open_hook = (fun dsenv1 op -> (

let uu____1327 = (

let uu____1328 = (

let uu____1333 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1333), (op)))
in NTOpen (uu____1328))
in (push_event uu____1327))); FStar_Syntax_DsEnv.ds_push_include_hook = (fun dsenv1 ns -> (

let uu____1339 = (

let uu____1340 = (

let uu____1345 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1345), (ns)))
in NTInclude (uu____1340))
in (push_event uu____1339))); FStar_Syntax_DsEnv.ds_push_module_abbrev_hook = (fun dsenv1 x l -> (

let uu____1353 = (

let uu____1354 = (

let uu____1361 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1361), (x), (l)))
in NTAlias (uu____1354))
in (push_event uu____1353)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____1366 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : env_t  ->  (env_t * (env_t  ->  (env_t * name_tracking_event Prims.list))) = (fun env -> (

let set_hooks = (fun dshooks tchooks env1 -> (

let uu____1419 = (FStar_Universal.with_tcenv env1 (fun dsenv1 -> (

let uu____1427 = (FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks)
in ((()), (uu____1427)))))
in (match (uu____1419) with
| ((), tcenv') -> begin
(FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks)
end)))
in (

let uu____1429 = (

let uu____1434 = (FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv)
in (

let uu____1435 = (FStar_TypeChecker_Env.tc_hooks env)
in ((uu____1434), (uu____1435))))
in (match (uu____1429) with
| (old_dshooks, old_tchooks) -> begin
(

let uu____1451 = (fresh_name_tracking_hooks ())
in (match (uu____1451) with
| (events, new_dshooks, new_tchooks) -> begin
(

let uu____1486 = (set_hooks new_dshooks new_tchooks env)
in ((uu____1486), ((fun env1 -> (

let uu____1500 = (set_hooks old_dshooks old_tchooks env1)
in (

let uu____1501 = (

let uu____1504 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____1504))
in ((uu____1500), (uu____1501))))))))
end))
end))))


let string_of_repl_task : repl_task  ->  Prims.string = (fun uu___75_1562 -> (match (uu___75_1562) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1565 = (string_of_timed_fname intf)
in (

let uu____1566 = (string_of_timed_fname impl)
in (FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1565 uu____1566)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1568 = (string_of_timed_fname intf_or_impl)
in (FStar_Util.format1 "LDSingle %s" uu____1568))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1570 = (string_of_timed_fname intf)
in (FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1570))
end
| PushFragment (frag) -> begin
(FStar_Util.format1 "PushFragment { code = %s }" frag.FStar_Parser_ParseIt.frag_text)
end))


let tc_one : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env intf_opt modf -> (

let uu____1591 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None intf_opt modf)
in (match (uu____1591) with
| (uu____1605, env1, delta1) -> begin
(

let env2 = (FStar_Universal.apply_delta_env env1 delta1)
in env2)
end)))


let run_repl_task : optmod_t  ->  env_t  ->  repl_task  ->  (optmod_t * env_t) = (fun curmod env task -> (match (task) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1644 = (tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname)) impl.tf_fname)
in ((curmod), (uu____1644)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1646 = (tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname)
in ((curmod), (uu____1646)))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1648 = (FStar_Universal.load_interface_decls env intf.tf_fname)
in ((curmod), (uu____1648)))
end
| PushFragment (frag) -> begin
(FStar_Universal.tc_one_fragment curmod env frag)
end))


let repl_ld_tasks_of_deps : Prims.string Prims.list  ->  repl_task Prims.list  ->  repl_task Prims.list = (fun deps final_tasks -> (

let wrap = dummy_tf_of_fname
in (

let rec aux = (fun deps1 final_tasks1 -> (match (deps1) with
| (intf)::(impl)::deps' when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____1703 = (aux deps' final_tasks1)
in (LDInterleaved ((((wrap intf)), ((wrap impl)))))::uu____1703)
end
| (intf_or_impl)::deps' -> begin
(

let uu____1710 = (aux deps' final_tasks1)
in (LDSingle ((wrap intf_or_impl)))::uu____1710)
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

let uu____1751 = (get_mod_name f)
in (Prims.op_Equality uu____1751 our_mod_name)))
in (

let uu____1752 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____1752) with
| (deps, dep_graph1) -> begin
(

let uu____1775 = (FStar_List.partition has_our_mod_name deps)
in (match (uu____1775) with
| (same_name, real_deps) -> begin
(

let intf_tasks = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____1812 = (

let uu____1813 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____1813)))
in (match (uu____1812) with
| true -> begin
(

let uu____1814 = (

let uu____1819 = (FStar_Util.format1 "Expecting an interface, got %s" intf)
in ((FStar_Errors.Fatal_MissingInterface), (uu____1819)))
in (FStar_Errors.raise_err uu____1814))
end
| uu____1820 -> begin
()
end));
(

let uu____1822 = (

let uu____1823 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____1823)))
in (match (uu____1822) with
| true -> begin
(

let uu____1824 = (

let uu____1829 = (FStar_Util.format1 "Expecting an implementation, got %s" impl)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1829)))
in (FStar_Errors.raise_err uu____1824))
end
| uu____1830 -> begin
()
end));
(LDInterfaceOfCurrentFile ((dummy_tf_of_fname intf)))::[];
)
end
| (impl)::[] -> begin
[]
end
| uu____1832 -> begin
(

let mods_str = (FStar_String.concat " " same_name)
in (

let message = "Too many or too few files matching %s: %s"
in ((

let uu____1838 = (

let uu____1843 = (FStar_Util.format2 message our_mod_name mods_str)
in ((FStar_Errors.Fatal_TooManyOrTooFewFileMatch), (uu____1843)))
in (FStar_Errors.raise_err uu____1838));
[];
)))
end)
in (

let tasks = (repl_ld_tasks_of_deps real_deps intf_tasks)
in ((real_deps), (tasks), (dep_graph1))))
end))
end))))))


let update_task_timestamps : repl_task  ->  repl_task = (fun uu___76_1855 -> (match (uu___76_1855) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1858 = (

let uu____1863 = (tf_of_fname intf.tf_fname)
in (

let uu____1864 = (tf_of_fname impl.tf_fname)
in ((uu____1863), (uu____1864))))
in LDInterleaved (uu____1858))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1866 = (tf_of_fname intf_or_impl.tf_fname)
in LDSingle (uu____1866))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1868 = (tf_of_fname intf.tf_fname)
in LDInterfaceOfCurrentFile (uu____1868))
end
| PushFragment (frag) -> begin
PushFragment (frag)
end))


let run_repl_transaction : repl_state  ->  push_kind  ->  Prims.bool  ->  repl_task  ->  (Prims.bool * repl_state) = (fun st push_kind must_rollback task -> (

let env = (push_repl push_kind task st)
in (

let uu____1895 = (track_name_changes env)
in (match (uu____1895) with
| (env1, finish_name_tracking) -> begin
(

let check_success = (fun uu____1938 -> ((

let uu____1941 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1941 (Prims.parse_int "0"))) && (not (must_rollback))))
in (

let uu____1942 = (

let uu____1949 = (with_captured_errors env1 (fun env2 -> (

let uu____1963 = (run_repl_task st.repl_curmod env2 task)
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____1963))))
in (match (uu____1949) with
| FStar_Pervasives_Native.Some (curmod, env2) when (check_success ()) -> begin
((curmod), (env2), (true))
end
| uu____1994 -> begin
((st.repl_curmod), (env1), (false))
end))
in (match (uu____1942) with
| (curmod, env2, success) -> begin
(

let uu____2008 = (finish_name_tracking env2)
in (match (uu____2008) with
| (env', name_events) -> begin
(

let st1 = (

let uu___94_2026 = st
in {repl_line = uu___94_2026.repl_line; repl_column = uu___94_2026.repl_column; repl_fname = uu___94_2026.repl_fname; repl_deps_stack = uu___94_2026.repl_deps_stack; repl_curmod = curmod; repl_env = env2; repl_stdin = uu___94_2026.repl_stdin; repl_names = uu___94_2026.repl_names})
in (

let st2 = (match (success) with
| true -> begin
(commit_name_tracking st1 name_events)
end
| uu____2028 -> begin
(pop_repl st1)
end)
in ((success), (st2))))
end))
end)))
end))))


let run_repl_ld_transactions : repl_state  ->  repl_task Prims.list  ->  (repl_state, repl_state) FStar_Util.either = (fun st tasks -> (

let debug1 = (fun verb task -> (

let uu____2058 = (FStar_Options.debug_any ())
in (match (uu____2058) with
| true -> begin
(

let uu____2059 = (string_of_repl_task task)
in (FStar_Util.print2 "%s %s" verb uu____2059))
end
| uu____2060 -> begin
()
end)))
in (

let rec revert_many = (fun st1 uu___77_2077 -> (match (uu___77_2077) with
| [] -> begin
st1
end
| ((task, _st'))::entries -> begin
((debug1 "Reverting" task);
(

let uu____2104 = (pop_repl st1)
in (revert_many uu____2104 entries));
)
end))
in (

let rec aux = (fun st1 tasks1 previous -> (match (((tasks1), (previous))) with
| ([], []) -> begin
FStar_Util.Inl (st1)
end
| ((task)::tasks2, []) -> begin
((debug1 "Loading" task);
(

let uu____2155 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____2155 (fun a239 -> ())));
(

let timestamped_task = (update_task_timestamps task)
in (

let push_kind = (

let uu____2158 = (FStar_Options.lax ())
in (match (uu____2158) with
| true -> begin
LaxCheck
end
| uu____2159 -> begin
FullCheck
end))
in (

let uu____2160 = (run_repl_transaction st1 push_kind false timestamped_task)
in (match (uu____2160) with
| (success, st2) -> begin
(match (success) with
| true -> begin
(

let uu____2175 = (

let uu___95_2176 = st2
in (

let uu____2177 = (FStar_ST.op_Bang repl_stack)
in {repl_line = uu___95_2176.repl_line; repl_column = uu___95_2176.repl_column; repl_fname = uu___95_2176.repl_fname; repl_deps_stack = uu____2177; repl_curmod = uu___95_2176.repl_curmod; repl_env = uu___95_2176.repl_env; repl_stdin = uu___95_2176.repl_stdin; repl_names = uu___95_2176.repl_names}))
in (aux uu____2175 tasks2 []))
end
| uu____2207 -> begin
FStar_Util.Inr (st2)
end)
end))));
)
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____2220 = (update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst prev) uu____2220)) -> begin
((debug1 "Skipping" task);
(aux st1 tasks2 previous1);
)
end
| (tasks2, previous1) -> begin
(

let uu____2232 = (revert_many st1 previous1)
in (aux uu____2232 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.repl_deps_stack))))))


let json_to_str : FStar_Util.json  ->  Prims.string = (fun uu___78_2241 -> (match (uu___78_2241) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____2243 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____2245 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____2245))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____2247) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____2250) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2270) -> begin
true
end
| uu____2275 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2290) -> begin
uu____2290
end))


let js_fail : 'Auu____2301 . Prims.string  ->  FStar_Util.json  ->  'Auu____2301 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___79_2316 -> (match (uu___79_2316) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___80_2323 -> (match (uu___80_2323) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____2332 . (FStar_Util.json  ->  'Auu____2332)  ->  FStar_Util.json  ->  'Auu____2332 Prims.list = (fun k uu___81_2347 -> (match (uu___81_2347) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___82_2366 -> (match (uu___82_2366) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____2392 = (js_str s)
in (match (uu____2392) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____2393 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____2399 = (js_str s)
in (match (uu____2399) with
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
| uu____2400 -> begin
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
| uu____2420 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____2427 -> begin
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
| uu____2445 -> begin
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

let uu____2475 = (js_str k1)
in (match (uu____2475) with
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
| uu____2476 -> begin
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
| uu____2482 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____2488 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____2494 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____2500 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____2511 = (js_str k1)
in (match (uu____2511) with
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
| uu____2512 -> begin
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
| Compute of (Prims.string * FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option)
| Search of Prims.string
| GenericError of Prims.string
| ProtocolViolation of Prims.string 
 and query =
{qq : query'; qid : Prims.string}


let uu___is_Exit : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____2609 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____2615 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____2621 -> begin
false
end))


let uu___is_Segment : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
true
end
| uu____2628 -> begin
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
| uu____2641 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____2648 -> begin
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
| uu____2668 -> begin
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
| uu____2704 -> begin
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
| uu____2742 -> begin
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
| uu____2800 -> begin
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
| uu____2838 -> begin
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
| uu____2852 -> begin
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
| uu____2866 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___83_2892 -> (match (uu___83_2892) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Segment (uu____2893) -> begin
false
end
| Pop -> begin
false
end
| Push ({push_kind = uu____2894; push_code = uu____2895; push_line = uu____2896; push_column = uu____2897; push_peek_only = false}) -> begin
false
end
| VfsAdd (uu____2898) -> begin
false
end
| GenericError (uu____2905) -> begin
false
end
| ProtocolViolation (uu____2906) -> begin
false
end
| Push (uu____2907) -> begin
true
end
| AutoComplete (uu____2908) -> begin
true
end
| Lookup (uu____2913) -> begin
true
end
| Compute (uu____2926) -> begin
true
end
| Search (uu____2935) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::("segment")::("vfs-add")::("tactic-ranges")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2947) -> begin
true
end
| uu____2948 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____2955) -> begin
uu____2955
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____2961 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____2967 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____2973 -> begin
false
end))


let try_assoc : 'Auu____2982 'Auu____2983 . 'Auu____2982  ->  ('Auu____2982 * 'Auu____2983) Prims.list  ->  'Auu____2983 FStar_Pervasives_Native.option = (fun key a -> (

let uu____3008 = (FStar_Util.try_find (fun uu____3022 -> (match (uu____3022) with
| (k, uu____3028) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____3008)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____3048 = (

let uu____3049 = (

let uu____3050 = (json_to_str got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____3050))
in ProtocolViolation (uu____3049))
in {qq = uu____3048; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____3084 = (try_assoc key a)
in (match (uu____3084) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3088 = (

let uu____3089 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____3089))
in (FStar_Exn.raise uu____3088))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____3104 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____3104 js_str))
in (FStar_All.try_with (fun uu___97_3111 -> (match (()) with
| () -> begin
(

let query = (

let uu____3113 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____3113 js_str))
in (

let args = (

let uu____3121 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____3121 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____3142 = (try_assoc k args)
in (match (uu____3142) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____3150 = (match (query) with
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

let uu____3151 = (

let uu____3152 = (arg "code")
in (FStar_All.pipe_right uu____3152 js_str))
in Segment (uu____3151))
end
| "peek" -> begin
(

let uu____3153 = (

let uu____3154 = (

let uu____3155 = (arg "kind")
in (FStar_All.pipe_right uu____3155 js_pushkind))
in (

let uu____3156 = (

let uu____3157 = (arg "code")
in (FStar_All.pipe_right uu____3157 js_str))
in (

let uu____3158 = (

let uu____3159 = (arg "line")
in (FStar_All.pipe_right uu____3159 js_int))
in (

let uu____3160 = (

let uu____3161 = (arg "column")
in (FStar_All.pipe_right uu____3161 js_int))
in {push_kind = uu____3154; push_code = uu____3156; push_line = uu____3158; push_column = uu____3160; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3153))
end
| "push" -> begin
(

let uu____3162 = (

let uu____3163 = (

let uu____3164 = (arg "kind")
in (FStar_All.pipe_right uu____3164 js_pushkind))
in (

let uu____3165 = (

let uu____3166 = (arg "code")
in (FStar_All.pipe_right uu____3166 js_str))
in (

let uu____3167 = (

let uu____3168 = (arg "line")
in (FStar_All.pipe_right uu____3168 js_int))
in (

let uu____3169 = (

let uu____3170 = (arg "column")
in (FStar_All.pipe_right uu____3170 js_int))
in {push_kind = uu____3163; push_code = uu____3165; push_line = uu____3167; push_column = uu____3169; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3162))
end
| "autocomplete" -> begin
(

let uu____3171 = (

let uu____3176 = (

let uu____3177 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____3177 js_str))
in (

let uu____3178 = (

let uu____3179 = (try_arg "context")
in (FStar_All.pipe_right uu____3179 js_optional_completion_context))
in ((uu____3176), (uu____3178))))
in AutoComplete (uu____3171))
end
| "lookup" -> begin
(

let uu____3184 = (

let uu____3197 = (

let uu____3198 = (arg "symbol")
in (FStar_All.pipe_right uu____3198 js_str))
in (

let uu____3199 = (

let uu____3200 = (try_arg "context")
in (FStar_All.pipe_right uu____3200 js_optional_lookup_context))
in (

let uu____3205 = (

let uu____3208 = (

let uu____3217 = (try_arg "location")
in (FStar_All.pipe_right uu____3217 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____3208 (FStar_Util.map_option (fun loc -> (

let uu____3269 = (

let uu____3270 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____3270 js_str))
in (

let uu____3271 = (

let uu____3272 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____3272 js_int))
in (

let uu____3273 = (

let uu____3274 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____3274 js_int))
in ((uu____3269), (uu____3271), (uu____3273)))))))))
in (

let uu____3275 = (

let uu____3278 = (arg "requested-info")
in (FStar_All.pipe_right uu____3278 (js_list js_str)))
in ((uu____3197), (uu____3199), (uu____3205), (uu____3275))))))
in Lookup (uu____3184))
end
| "compute" -> begin
(

let uu____3285 = (

let uu____3294 = (

let uu____3295 = (arg "term")
in (FStar_All.pipe_right uu____3295 js_str))
in (

let uu____3296 = (

let uu____3301 = (try_arg "rules")
in (FStar_All.pipe_right uu____3301 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____3294), (uu____3296))))
in Compute (uu____3285))
end
| "search" -> begin
(

let uu____3316 = (

let uu____3317 = (arg "terms")
in (FStar_All.pipe_right uu____3317 js_str))
in Search (uu____3316))
end
| "vfs-add" -> begin
(

let uu____3318 = (

let uu____3325 = (

let uu____3328 = (try_arg "filename")
in (FStar_All.pipe_right uu____3328 (FStar_Util.map_option js_str)))
in (

let uu____3335 = (

let uu____3336 = (arg "contents")
in (FStar_All.pipe_right uu____3336 js_str))
in ((uu____3325), (uu____3335))))
in VfsAdd (uu____3318))
end
| uu____3339 -> begin
(

let uu____3340 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____3340))
end)
in {qq = uu____3150; qid = qid})))))
end)) (fun uu___96_3343 -> (match (uu___96_3343) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (FStar_All.try_with (fun uu___99_3354 -> (match (()) with
| () -> begin
(

let uu____3355 = (FStar_Util.read_line stream)
in (match (uu____3355) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (ExitREPL ((Prims.parse_int "0"))))
end
| FStar_Pervasives_Native.Some (line) -> begin
(

let uu____3359 = (FStar_Util.json_of_string line)
in (match (uu____3359) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(unpack_interactive_query request)
end))
end))
end)) (fun uu___98_3365 -> (match (uu___98_3365) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let json_of_opt : 'Auu____3375 . ('Auu____3375  ->  FStar_Util.json)  ->  'Auu____3375 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____3395 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____3395)))


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

let uu____3408 = (

let uu____3415 = (

let uu____3422 = (

let uu____3429 = (

let uu____3434 = (

let uu____3435 = (

let uu____3438 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3444 = (FStar_Range.json_of_use_range r)
in (uu____3444)::[])
end)
in (

let uu____3445 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (

let uu____3451 = (FStar_Range.def_range r)
in (

let uu____3452 = (FStar_Range.use_range r)
in (Prims.op_disEquality uu____3451 uu____3452))) -> begin
(

let uu____3453 = (FStar_Range.json_of_def_range r)
in (uu____3453)::[])
end
| uu____3454 -> begin
[]
end)
in (FStar_List.append uu____3438 uu____3445)))
in FStar_Util.JsonList (uu____3435))
in (("ranges"), (uu____3434)))
in (uu____3429)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____3422)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____3415)
in FStar_Util.JsonAssoc (uu____3408)))

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

let uu____3623 = (

let uu____3630 = (

let uu____3635 = (json_of_opt FStar_Range.json_of_def_range lr.slr_def_range)
in (("defined-at"), (uu____3635)))
in (

let uu____3636 = (

let uu____3643 = (

let uu____3648 = (json_of_opt (fun _0_18 -> FStar_Util.JsonStr (_0_18)) lr.slr_typ)
in (("type"), (uu____3648)))
in (

let uu____3649 = (

let uu____3656 = (

let uu____3661 = (json_of_opt (fun _0_19 -> FStar_Util.JsonStr (_0_19)) lr.slr_doc)
in (("documentation"), (uu____3661)))
in (

let uu____3662 = (

let uu____3669 = (

let uu____3674 = (json_of_opt (fun _0_20 -> FStar_Util.JsonStr (_0_20)) lr.slr_def)
in (("definition"), (uu____3674)))
in (uu____3669)::[])
in (uu____3656)::uu____3662))
in (uu____3643)::uu____3649))
in (uu____3630)::uu____3636))
in ((("name"), (FStar_Util.JsonStr (lr.slr_name))))::uu____3623))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____3707 = (FStar_List.map (fun _0_21 -> FStar_Util.JsonStr (_0_21)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_22 -> FStar_Util.JsonList (_0_22)) uu____3707))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____3729 -> begin
false
end))


let uu___is_OptReset : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReset -> begin
true
end
| uu____3735 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____3741 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___84_3746 -> (match (uu___84_3746) with
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


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___85_3939 -> (match (uu___85_3939) with
| FStar_Options.Const (uu____3940) -> begin
"flag"
end
| FStar_Options.IntStr (uu____3941) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____3942) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____3943) -> begin
"string"
end
| FStar_Options.EnumStr (uu____3944) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____3947) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____3954, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____3964, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let rec snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.strcat "${" (Prims.strcat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.strcat "--" (Prims.strcat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.strcat " " argstring)
end
| uu____4001 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____4012) -> begin
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
| FStar_Options.PostProcessed (uu____4025, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____4035, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____4043 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____4043))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___86_4050 -> (match (uu___86_4050) with
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

let uu____4058 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____4058))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____4072 = (

let uu____4079 = (

let uu____4086 = (

let uu____4091 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____4091)))
in (

let uu____4092 = (

let uu____4099 = (

let uu____4104 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____4104)))
in (

let uu____4105 = (

let uu____4112 = (

let uu____4117 = (json_of_opt (fun _0_23 -> FStar_Util.JsonStr (_0_23)) opt.opt_documentation)
in (("documentation"), (uu____4117)))
in (

let uu____4118 = (

let uu____4125 = (

let uu____4130 = (

let uu____4131 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____4131))
in (("type"), (uu____4130)))
in (uu____4125)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____4112)::uu____4118))
in (uu____4099)::uu____4105))
in (uu____4086)::uu____4092))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____4079)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____4072))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____4169 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____4169)))


let write_json : FStar_Util.json  ->  unit = (fun json -> ((

let uu____4182 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____4182));
(FStar_Util.print_raw "\n");
))


let write_response : Prims.string  ->  query_status  ->  FStar_Util.json  ->  unit = (fun qid status response -> (

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


let write_message : Prims.string  ->  FStar_Util.json  ->  unit = (fun level contents -> (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("message"))))::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (contents)))::[]))))


let write_hello : unit  ->  unit = (fun uu____4250 -> (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4253 = (FStar_List.map (fun _0_24 -> FStar_Util.JsonStr (_0_24)) interactive_protocol_features)
in FStar_Util.JsonList (uu____4253))
in (write_json (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info))))))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.strcat "--" name)
in (

let uu____4271 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____4271) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.strcat flag (Prims.strcat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____4280 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____4309 -> (match (uu____4309) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____4324 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____4324 (FStar_Util.map_option (fun default_value -> (

let uu____4336 = (sig_of_fstar_option name typ)
in (

let uu____4337 = (snippets_of_fstar_option name typ)
in (

let uu____4340 = (

let uu____4341 = (FStar_Options.settable name)
in (match (uu____4341) with
| true -> begin
OptSet
end
| uu____4342 -> begin
(

let uu____4343 = (FStar_Options.resettable name)
in (match (uu____4343) with
| true -> begin
OptReset
end
| uu____4344 -> begin
OptReadOnly
end))
end))
in {opt_name = name; opt_sig = uu____4336; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____4337; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4347 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____4340})))))))
end))))
in (FStar_All.pipe_right uu____4280 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___100_4369 = opt
in (

let uu____4370 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___100_4369.opt_name; opt_sig = uu___100_4369.opt_sig; opt_value = uu____4370; opt_default = uu___100_4369.opt_default; opt_type = uu___100_4369.opt_type; opt_snippets = uu___100_4369.opt_snippets; opt_documentation = uu___100_4369.opt_documentation; opt_permission_level = uu___100_4369.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____4383 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____4383)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____4400 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____4400)))
end
| uu____4401 -> begin
((""), (opt_name))
end)))


let json_of_repl_state : repl_state  ->  FStar_Util.json = (fun st -> (

let filenames = (fun uu____4418 -> (match (uu____4418) with
| (task, uu____4426) -> begin
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
| PushFragment (uu____4433) -> begin
[]
end)
end))
in (

let uu____4434 = (

let uu____4441 = (

let uu____4446 = (

let uu____4447 = (

let uu____4450 = (FStar_List.concatMap filenames st.repl_deps_stack)
in (FStar_List.map (fun _0_25 -> FStar_Util.JsonStr (_0_25)) uu____4450))
in FStar_Util.JsonList (uu____4447))
in (("loaded-dependencies"), (uu____4446)))
in (

let uu____4457 = (

let uu____4464 = (

let uu____4469 = (

let uu____4470 = (

let uu____4473 = (current_fstar_options (fun uu____4478 -> true))
in (FStar_List.map json_of_fstar_option uu____4473))
in FStar_Util.JsonList (uu____4470))
in (("options"), (uu____4469)))
in (uu____4464)::[])
in (uu____4441)::uu____4457))
in FStar_Util.JsonAssoc (uu____4434))))


let with_printed_effect_args : 'Auu____4495 . (unit  ->  'Auu____4495)  ->  'Auu____4495 = (fun k -> (FStar_Options.with_saved_options (fun uu____4508 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____4521 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____4528 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____4535 'Auu____4536 . 'Auu____4535  ->  ((query_status * FStar_Util.json) * ('Auu____4536, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____4568 'Auu____4569 . 'Auu____4568  ->  ((query_status * FStar_Util.json) * ('Auu____4568, 'Auu____4569) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____4599 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4599) FStar_Util.either) = (fun st -> (

let uu____4617 = (

let uu____4622 = (json_of_repl_state st)
in ((QueryOK), (uu____4622)))
in ((uu____4617), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____4639 'Auu____4640 . 'Auu____4639  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____4639, 'Auu____4640) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_generic_error : 'Auu____4679 'Auu____4680 . 'Auu____4679  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____4679, 'Auu____4680) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let collect_errors : unit  ->  FStar_Errors.issue Prims.list = (fun uu____4717 -> (

let errors = (FStar_Errors.report_all ())
in ((FStar_Errors.clear ());
errors;
)))


let run_segment : 'Auu____4728 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4728) FStar_Util.either) = (fun st code -> (

let frag = {FStar_Parser_ParseIt.frag_text = code; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let collect_decls = (fun uu____4759 -> (

let uu____4760 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____4760) with
| FStar_Parser_Driver.Empty -> begin
[]
end
| FStar_Parser_Driver.Decls (decls) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu____4766, decls)) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface (uu____4772, decls, uu____4774)) -> begin
decls
end)))
in (

let uu____4779 = (with_captured_errors st.repl_env (fun uu____4788 -> (

let uu____4789 = (collect_decls ())
in (FStar_All.pipe_left (fun _0_26 -> FStar_Pervasives_Native.Some (_0_26)) uu____4789))))
in (match (uu____4779) with
| FStar_Pervasives_Native.None -> begin
(

let errors = (

let uu____4817 = (collect_errors ())
in (FStar_All.pipe_right uu____4817 (FStar_List.map json_of_issue)))
in ((((QueryNOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl (st))))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let json_of_decl = (fun decl -> (

let uu____4843 = (

let uu____4850 = (

let uu____4855 = (FStar_Range.json_of_def_range (FStar_Parser_AST.decl_drange decl))
in (("def_range"), (uu____4855)))
in (uu____4850)::[])
in FStar_Util.JsonAssoc (uu____4843)))
in (

let js_decls = (

let uu____4865 = (FStar_List.map json_of_decl decls)
in (FStar_All.pipe_left (fun _0_27 -> FStar_Util.JsonList (_0_27)) uu____4865))
in ((((QueryOK), (FStar_Util.JsonAssoc (((("decls"), (js_decls)))::[])))), (FStar_Util.Inl (st)))))
end)))))


let run_vfs_add : 'Auu____4894 . repl_state  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4894) FStar_Util.either) = (fun st opt_fname contents -> (

let fname = (FStar_Util.dflt st.repl_fname opt_fname)
in ((FStar_Parser_ParseIt.add_vfs_entry fname contents);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st)));
)))


let run_pop : 'Auu____4940 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____4940) FStar_Util.either) = (fun st -> (

let uu____4958 = (nothing_left_to_pop st)
in (match (uu____4958) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____4979 -> begin
(

let st' = (pop_repl st)
in ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st'))))
end)))


let load_deps : repl_state  ->  ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either = (fun st -> (

let uu____5004 = (with_captured_errors st.repl_env (fun _env -> (

let uu____5030 = (deps_and_repl_ld_tasks_of_our_file st.repl_fname)
in (FStar_All.pipe_left (fun _0_28 -> FStar_Pervasives_Native.Some (_0_28)) uu____5030))))
in (match (uu____5004) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (st)
end
| FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___101_5121 = st
in (

let uu____5122 = (FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1)
in {repl_line = uu___101_5121.repl_line; repl_column = uu___101_5121.repl_column; repl_fname = uu___101_5121.repl_fname; repl_deps_stack = uu___101_5121.repl_deps_stack; repl_curmod = uu___101_5121.repl_curmod; repl_env = uu____5122; repl_stdin = uu___101_5121.repl_stdin; repl_names = uu___101_5121.repl_names}))
in (

let uu____5123 = (run_repl_ld_transactions st1 tasks)
in (match (uu____5123) with
| FStar_Util.Inr (st2) -> begin
FStar_Util.Inr (st2)
end
| FStar_Util.Inl (st2) -> begin
FStar_Util.Inl (((st2), (deps)))
end)))
end)))


let rephrase_dependency_error : FStar_Errors.issue  ->  FStar_Errors.issue = (fun issue -> (

let uu___102_5159 = issue
in (

let uu____5160 = (FStar_Util.format1 "Error while computing or loading dependencies:\n%s" issue.FStar_Errors.issue_message)
in {FStar_Errors.issue_message = uu____5160; FStar_Errors.issue_level = uu___102_5159.FStar_Errors.issue_level; FStar_Errors.issue_range = uu___102_5159.FStar_Errors.issue_range; FStar_Errors.issue_number = uu___102_5159.FStar_Errors.issue_number})))


let run_push_without_deps : 'Auu____5167 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5167) FStar_Util.either) = (fun st query -> (

let set_nosynth_flag = (fun st1 flag -> (

let uu___103_5201 = st1
in {repl_line = uu___103_5201.repl_line; repl_column = uu___103_5201.repl_column; repl_fname = uu___103_5201.repl_fname; repl_deps_stack = uu___103_5201.repl_deps_stack; repl_curmod = uu___103_5201.repl_curmod; repl_env = (

let uu___104_5203 = st1.repl_env
in {FStar_TypeChecker_Env.solver = uu___104_5203.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_5203.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_5203.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_5203.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___104_5203.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___104_5203.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_5203.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_5203.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_5203.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_5203.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_5203.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_5203.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_5203.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___104_5203.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___104_5203.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___104_5203.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___104_5203.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___104_5203.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_5203.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___104_5203.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___104_5203.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___104_5203.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = flag; FStar_TypeChecker_Env.tc_term = uu___104_5203.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___104_5203.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_5203.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___104_5203.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_5203.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___104_5203.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___104_5203.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___104_5203.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___104_5203.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___104_5203.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___104_5203.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___104_5203.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___104_5203.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___104_5203.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___104_5203.FStar_TypeChecker_Env.dep_graph}); repl_stdin = uu___103_5201.repl_stdin; repl_names = uu___103_5201.repl_names}))
in (

let uu____5204 = query
in (match (uu____5204) with
| {push_kind = push_kind; push_code = text; push_line = line; push_column = column; push_peek_only = peek_only} -> begin
(

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in ((FStar_TypeChecker_Env.toggle_id_info st.repl_env true);
(

let st1 = (set_nosynth_flag st peek_only)
in (

let uu____5225 = (run_repl_transaction st1 push_kind peek_only (PushFragment (frag)))
in (match (uu____5225) with
| (success, st2) -> begin
(

let st3 = (set_nosynth_flag st2 false)
in (

let status = (match ((success || peek_only)) with
| true -> begin
QueryOK
end
| uu____5246 -> begin
QueryNOK
end)
in (

let json_errors = (

let uu____5248 = (

let uu____5251 = (collect_errors ())
in (FStar_All.pipe_right uu____5251 (FStar_List.map json_of_issue)))
in FStar_Util.JsonList (uu____5248))
in (

let st4 = (match (success) with
| true -> begin
(

let uu___105_5259 = st3
in {repl_line = line; repl_column = column; repl_fname = uu___105_5259.repl_fname; repl_deps_stack = uu___105_5259.repl_deps_stack; repl_curmod = uu___105_5259.repl_curmod; repl_env = uu___105_5259.repl_env; repl_stdin = uu___105_5259.repl_stdin; repl_names = uu___105_5259.repl_names})
end
| uu____5260 -> begin
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
| uu____5274 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____5276 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat (FStar_String.uppercase first) uu____5276)))
end))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____5306 = (FStar_Util.psmap_empty ())
in (

let uu____5309 = (

let uu____5312 = (FStar_Options.prims ())
in (uu____5312)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____5322 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____5322 true))) uu____5306 uu____5309)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____5340 -> (match (uu____5340) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____5348 -> begin
(

let ns_query = (

let uu____5352 = (capitalize modname)
in (FStar_Util.split uu____5352 "."))
in (

let uu____5353 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____5353 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods)))))))


let run_push_with_deps : 'Auu____5364 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5364) FStar_Util.either) = (fun st query -> ((

let uu____5388 = (FStar_Options.debug_any ())
in (match (uu____5388) with
| true -> begin
(FStar_Util.print_string "Reloading dependencies")
end
| uu____5389 -> begin
()
end));
(FStar_TypeChecker_Env.toggle_id_info st.repl_env false);
(

let uu____5391 = (load_deps st)
in (match (uu____5391) with
| FStar_Util.Inr (st1) -> begin
(

let errors = (

let uu____5424 = (collect_errors ())
in (FStar_List.map rephrase_dependency_error uu____5424))
in (

let js_errors = (FStar_All.pipe_right errors (FStar_List.map json_of_issue))
in ((((QueryNOK), (FStar_Util.JsonList (js_errors)))), (FStar_Util.Inl (st1)))))
end
| FStar_Util.Inl (st1, deps) -> begin
((

let uu____5455 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____5455 (fun a240 -> ())));
(

let names1 = (add_module_completions st1.repl_fname deps st1.repl_names)
in (run_push_without_deps (

let uu___106_5458 = st1
in {repl_line = uu___106_5458.repl_line; repl_column = uu___106_5458.repl_column; repl_fname = uu___106_5458.repl_fname; repl_deps_stack = uu___106_5458.repl_deps_stack; repl_curmod = uu___106_5458.repl_curmod; repl_env = uu___106_5458.repl_env; repl_stdin = uu___106_5458.repl_stdin; repl_names = names1}) query));
)
end));
))


let run_push : 'Auu____5465 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5465) FStar_Util.either) = (fun st query -> (

let uu____5488 = (nothing_left_to_pop st)
in (match (uu____5488) with
| true -> begin
(run_push_with_deps st query)
end
| uu____5501 -> begin
(run_push_without_deps st query)
end)))


let run_symbol_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let tcenv = st.repl_env
in (

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____5576 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____5576))
in (

let lid1 = (

let uu____5580 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____5580))
in (

let uu____5585 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____5585 (FStar_Util.map_option (fun uu____5640 -> (match (uu____5640) with
| ((uu____5659, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____5678 = (FStar_Syntax_DsEnv.try_lookup_doc tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____5678 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____5729 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____5729 (fun uu___87_5773 -> (match (uu___87_5773) with
| (FStar_Util.Inr (se, uu____5795), uu____5796) -> begin
(

let uu____5825 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____5825))
end
| uu____5826 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____5878 -> (match (uu____5878) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____5925) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5978 -> begin
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

let uu____6053 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____6053))
end
| uu____6054 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____6061 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____6072 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range1 = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____6082 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {slr_name = name; slr_def_range = def_range1; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}
in (

let uu____6084 = (

let uu____6095 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____6095)))
in FStar_Pervasives_Native.Some (uu____6084))))))))
end)
in (match (response) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (info) -> begin
FStar_Util.Inr (info)
end)))))))))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____6202 = (trim_option_name opt_name)
in (match (uu____6202) with
| (uu____6221, trimmed_name) -> begin
(

let uu____6223 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____6223) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.strcat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____6251 = (

let uu____6262 = (

let uu____6269 = (update_option opt)
in (alist_of_fstar_option uu____6269))
in (("option"), (uu____6262)))
in FStar_Util.Inr (uu____6251))
end))
end)))


let run_module_lookup : repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____6313 = (FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names query)
in (match (uu____6313) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____6341 = (

let uu____6352 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____6352)))
in FStar_Util.Inr (uu____6341))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____6376 = (

let uu____6387 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____6387)))
in FStar_Util.Inr (uu____6376))
end))))


let run_code_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____6464 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____6464) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____6524) -> begin
(

let uu____6535 = (run_module_lookup st symbol)
in (match (uu____6535) with
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


let run_lookup : 'Auu____6701 . repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6701) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____6759 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____6759) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let code_autocomplete_mod_filter : 'Auu____6845 . ('Auu____6845 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____6845 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___88_6860 -> (match (uu___88_6860) with
| (uu____6865, FStar_Interactive_CompletionTable.Namespace (uu____6866)) -> begin
FStar_Pervasives_Native.None
end
| (uu____6871, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____6872; FStar_Interactive_CompletionTable.mod_path = uu____6873; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____6880 = (

let uu____6885 = (

let uu____6886 = (

let uu___107_6887 = md
in (

let uu____6888 = (

let uu____6889 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.strcat uu____6889 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____6888; FStar_Interactive_CompletionTable.mod_path = uu___107_6887.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___107_6887.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____6886))
in ((pth), (uu____6885)))
in FStar_Pervasives_Native.Some (uu____6880))
end))


let run_code_autocomplete : 'Auu____6900 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6900) FStar_Util.either) = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names needle)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result (FStar_List.append lids mods_and_nss))
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st))))))))


let run_module_autocomplete : 'Auu____6957 'Auu____6958 'Auu____6959 . repl_state  ->  Prims.string  ->  'Auu____6957  ->  'Auu____6958  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6959) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : Prims.int  ->  Prims.bool  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____7030 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReset -> begin
((is_reset), ("#reset-only"))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____7030) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____7045 -> begin
(Prims.strcat "(" (Prims.strcat explanation (Prims.strcat " " (Prims.strcat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____7062 'Auu____7063 . 'Auu____7062  ->  Prims.string  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * ('Auu____7062, 'Auu____7063) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____7091 = (trim_option_name search_term)
in (match (uu____7091) with
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
| (uu____7146, uu____7147) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____7164 . repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7164) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_and_rewind : 'Auu____7203 'Auu____7204 . repl_state  ->  (repl_state  ->  'Auu____7203)  ->  ('Auu____7203 * (repl_state, 'Auu____7204) FStar_Util.either) = (fun st task -> (

let env' = (push st.repl_env "#compute")
in (

let results = (FStar_All.try_with (fun uu___109_7240 -> (match (()) with
| () -> begin
(

let uu____7245 = (task st)
in (FStar_All.pipe_left (fun _0_30 -> FStar_Util.Inl (_0_30)) uu____7245))
end)) (fun uu___108_7252 -> (match (uu___108_7252) with
| e -> begin
FStar_Util.Inr (e)
end)))
in ((pop env' "#compute");
(match (results) with
| FStar_Util.Inl (results1) -> begin
((results1), (FStar_Util.Inl ((

let uu___110_7273 = st
in {repl_line = uu___110_7273.repl_line; repl_column = uu___110_7273.repl_column; repl_fname = uu___110_7273.repl_fname; repl_deps_stack = uu___110_7273.repl_deps_stack; repl_curmod = uu___110_7273.repl_curmod; repl_env = env'; repl_stdin = uu___110_7273.repl_stdin; repl_names = uu___110_7273.repl_names}))))
end
| FStar_Util.Inr (e) -> begin
(FStar_Exn.raise e)
end);
))))


let run_with_parsed_and_tc_term : 'Auu____7299 'Auu____7300 'Auu____7301 . repl_state  ->  Prims.string  ->  'Auu____7299  ->  'Auu____7300  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (query_status * FStar_Util.json))  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7301) FStar_Util.either) = (fun st term line column continuation -> (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____7394, ({FStar_Syntax_Syntax.lbname = uu____7395; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____7397; FStar_Syntax_Syntax.lbeff = uu____7398; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____7400; FStar_Syntax_Syntax.lbpos = uu____7401})::[]), uu____7402); FStar_Syntax_Syntax.sigrng = uu____7403; FStar_Syntax_Syntax.sigquals = uu____7404; FStar_Syntax_Syntax.sigmeta = uu____7405; FStar_Syntax_Syntax.sigattrs = uu____7406})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____7443 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____7464 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____7464) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____7470) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____7489 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun env decls -> (

let uu____7507 = (

let uu____7512 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts decls)
in (uu____7512 env.FStar_TypeChecker_Env.dsenv))
in (FStar_Pervasives_Native.fst uu____7507)))
in (

let typecheck = (fun tcenv decls -> (

let uu____7536 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____7536) with
| (ses, uu____7550, uu____7551) -> begin
ses
end)))
in (run_and_rewind st (fun st1 -> (

let tcenv = st1.repl_env
in (

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____7574 -> begin
(

let uu____7575 = (parse1 frag)
in (match (uu____7575) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____7600 -> (

let decls1 = (desugar tcenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____7635 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____7635) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (continuation tcenv1 def1))
end))
end))))
in (

let uu____7647 = (FStar_Options.trace_error ())
in (match (uu____7647) with
| true -> begin
(aux ())
end
| uu____7652 -> begin
(FStar_All.try_with (fun uu___112_7658 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___111_7666 -> (match (uu___111_7666) with
| e -> begin
(

let uu____7672 = (

let uu____7673 = (FStar_Errors.issue_of_exn e)
in (match (uu____7673) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____7677 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____7677))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise e)
end))
in ((QueryNOK), (uu____7672)))
end)))
end)))
end))
end)))))))))))


let run_compute : 'Auu____7686 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7686) FStar_Util.either) = (fun st term rules -> (

let rules1 = (FStar_List.append (match (rules) with
| FStar_Pervasives_Native.Some (rules1) -> begin
rules1
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end) ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Primops)::[]))
in (

let normalize_term1 = (fun tcenv rules2 t -> (FStar_TypeChecker_Normalize.normalize rules2 tcenv t))
in (run_with_parsed_and_tc_term st term (Prims.parse_int "0") (Prims.parse_int "0") (fun tcenv def -> (

let normalized = (normalize_term1 tcenv rules1 def)
in (

let uu____7758 = (

let uu____7759 = (term_to_string tcenv normalized)
in FStar_Util.JsonStr (uu____7759))
in ((QueryOK), (uu____7758)))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____7786 -> begin
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
| uu____7800 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___89_7826 -> (match (uu___89_7826) with
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

let uu____8041 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____8048 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____8041; sc_fvars = uu____8048})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____8115 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____8115) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____8147 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____8147) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____8166, typ), uu____8168) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____8221 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____8221) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____8269 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____8269))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun tcenv sc -> (

let typ_str = (

let uu____8315 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____8315))
in (

let uu____8316 = (

let uu____8323 = (

let uu____8328 = (

let uu____8329 = (

let uu____8330 = (FStar_Syntax_DsEnv.shorten_lid tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid)
in uu____8330.FStar_Ident.str)
in FStar_Util.JsonStr (uu____8329))
in (("lid"), (uu____8328)))
in (uu____8323)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____8316))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____8352) -> begin
true
end
| uu____8353 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____8360) -> begin
uu____8360
end))


let run_search : 'Auu____8367 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8367) FStar_Util.either) = (fun st search_str -> (

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

let uu____8408 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____8408))
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
| uu____8427 -> begin
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
| uu____8436 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____8438 = (

let uu____8439 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____8439))
in (FStar_Exn.raise uu____8438))
end
| uu____8440 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____8441 = (strip_quotes term1)
in NameContainsStr (uu____8441))
end
| uu____8442 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____8444 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____8444) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8447 = (

let uu____8448 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____8448))
in (FStar_Exn.raise uu____8447))
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

let uu____8470 = (match (term.st_term) with
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
| uu____8473 -> begin
""
end) uu____8470)))
in (

let results = (FStar_All.try_with (fun uu___114_8494 -> (match (()) with
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

let uu____8539 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____8539))
in (

let uu____8542 = (

let uu____8543 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____8543))
in (FStar_Exn.raise uu____8542)))
end
| uu____8548 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___113_8553 -> (match (uu___113_8553) with
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
| Push ({push_kind = SyntaxCheck; push_code = uu____8646; push_line = uu____8647; push_column = uu____8648; push_peek_only = false}) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____8649 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = GenericError ("Current module unset"); qid = q.qid}
end
| uu____8650 -> begin
q
end)
end))


let rec go : repl_state  ->  Prims.int = (fun st -> (

let rec loop = (fun st1 -> (

let query = (

let uu____8663 = (read_interactive_query st1.repl_stdin)
in (validate_query st1 uu____8663))
in (

let uu____8664 = (run_query st1 query.qq)
in (match (uu____8664) with
| ((status, response), state_opt) -> begin
((write_response query.qid status response);
(match (state_opt) with
| FStar_Util.Inl (st') -> begin
(loop st')
end
| FStar_Util.Inr (exitcode) -> begin
(FStar_Exn.raise (ExitREPL (exitcode)))
end);
)
end))))
in (

let uu____8695 = (FStar_Options.trace_error ())
in (match (uu____8695) with
| true -> begin
(loop st)
end
| uu____8696 -> begin
(FStar_All.try_with (fun uu___116_8698 -> (match (()) with
| () -> begin
(loop st)
end)) (fun uu___115_8701 -> (match (uu___115_8701) with
| ExitREPL (n1) -> begin
n1
end)))
end))))


let interactive_error_handler : FStar_Errors.error_handler = (

let issues = (FStar_Util.mk_ref [])
in (

let add_one1 = (fun e -> (

let uu____8716 = (

let uu____8719 = (FStar_ST.op_Bang issues)
in (e)::uu____8719)
in (FStar_ST.op_Colon_Equals issues uu____8716)))
in (

let count_errors = (fun uu____8825 -> (

let uu____8826 = (

let uu____8829 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____8829))
in (FStar_List.length uu____8826)))
in (

let report = (fun uu____8890 -> (

let uu____8891 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____8891)))
in (

let clear1 = (fun uu____8948 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : FStar_Util.printer = {FStar_Util.printer_prinfo = (fun s -> (write_message "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (write_message "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (write_message "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label get_string get_json -> (

let uu____9020 = (get_json ())
in (write_message label uu____9020)))}


let initial_range : FStar_Range.range = (

let uu____9021 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____9022 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____9021 uu____9022)))


let interactive_mode' : Prims.string  ->  unit = (fun filename -> ((write_hello ());
(

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env initial_range)
in (

let init_st = (

let uu____9032 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_deps_stack = []; repl_curmod = FStar_Pervasives_Native.None; repl_env = env1; repl_stdin = uu____9032; repl_names = FStar_Interactive_CompletionTable.empty})
in (

let exit_code = (

let uu____9038 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____9038) with
| true -> begin
(

let uu____9039 = (

let uu____9040 = (FStar_Options.file_list ())
in (FStar_List.hd uu____9040))
in (FStar_SMTEncoding_Solver.with_hints_db uu____9039 (fun uu____9044 -> (go init_st))))
end
| uu____9045 -> begin
(go init_st)
end))
in (FStar_All.exit exit_code)))));
))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((FStar_Util.set_printer interactive_printer);
(

let uu____9053 = (

let uu____9054 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____9054))
in (match (uu____9053) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("--ide: ignoring --codegen")))
end
| uu____9057 -> begin
()
end));
(

let uu____9058 = (FStar_Options.trace_error ())
in (match (uu____9058) with
| true -> begin
(interactive_mode' filename)
end
| uu____9059 -> begin
(FStar_All.try_with (fun uu___118_9062 -> (match (()) with
| () -> begin
((FStar_Errors.set_handler interactive_error_handler);
(interactive_mode' filename);
)
end)) (fun uu___117_9067 -> (match (uu___117_9067) with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise e);
)
end)))
end));
))




