
open Prims
open FStar_Pervasives

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
| uu____29 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____35 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____41 -> begin
false
end))


let set_check_kind : FStar_TypeChecker_Env.env  ->  push_kind  ->  FStar_TypeChecker_Env.env = (fun env check_kind -> (

let uu___91_52 = env
in (

let uu____53 = (FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv (Prims.op_Equality check_kind SyntaxCheck))
in {FStar_TypeChecker_Env.solver = uu___91_52.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___91_52.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___91_52.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___91_52.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___91_52.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___91_52.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___91_52.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___91_52.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___91_52.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___91_52.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___91_52.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___91_52.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___91_52.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___91_52.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___91_52.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___91_52.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___91_52.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___91_52.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality check_kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___91_52.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___91_52.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___91_52.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___91_52.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___91_52.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___91_52.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___91_52.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___91_52.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___91_52.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___91_52.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___91_52.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___91_52.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___91_52.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___91_52.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___91_52.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___91_52.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu____53; FStar_TypeChecker_Env.dep_graph = uu___91_52.FStar_TypeChecker_Env.dep_graph})))


let with_captured_errors' : 'Auu____60 . FStar_TypeChecker_Env.env  ->  (FStar_TypeChecker_Env.env  ->  'Auu____60 FStar_Pervasives_Native.option)  ->  'Auu____60 FStar_Pervasives_Native.option = (fun env f -> (FStar_All.try_with (fun uu___93_85 -> (match (()) with
| () -> begin
(f env)
end)) (fun uu___92_92 -> (match (uu___92_92) with
| FStar_All.Failure (msg) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____98 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.log_issue uu____98 ((FStar_Errors.Error_IDEAssertionFailure), (msg1))));
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

let uu____118 = (

let uu____127 = (

let uu____134 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____134)))
in (uu____127)::[])
in (FStar_TypeChecker_Err.add_errors env uu____118));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Stop -> begin
FStar_Pervasives_Native.None
end))))


let with_captured_errors : 'Auu____153 . FStar_TypeChecker_Env.env  ->  (FStar_TypeChecker_Env.env  ->  'Auu____153 FStar_Pervasives_Native.option)  ->  'Auu____153 FStar_Pervasives_Native.option = (fun env f -> (

let uu____175 = (FStar_Options.trace_error ())
in (match (uu____175) with
| true -> begin
(f env)
end
| uu____178 -> begin
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

let uu____208 = (FStar_Parser_ParseIt.get_file_last_modification_time fname)
in {tf_fname = fname; tf_modtime = uu____208}))


let dummy_tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> {tf_fname = fname; tf_modtime = t0})


let string_of_timed_fname : timed_fname  ->  Prims.string = (fun uu____218 -> (match (uu____218) with
| {tf_fname = fname; tf_modtime = modtime} -> begin
(match ((Prims.op_Equality modtime t0)) with
| true -> begin
(FStar_Util.format1 "{ %s }" fname)
end
| uu____221 -> begin
(

let uu____222 = (FStar_Util.string_of_time modtime)
in (FStar_Util.format2 "{ %s; %s }" fname uu____222))
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
| uu____334 -> begin
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
| uu____360 -> begin
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
| uu____374 -> begin
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
| uu____388 -> begin
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


let repl_current_qid : Prims.string FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let repl_stack : (repl_task * repl_state) Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pop_repl : repl_state  ->  repl_state = (fun st -> (

let uu____715 = (FStar_ST.op_Bang repl_stack)
in (match (uu____715) with
| [] -> begin
(failwith "Too many pops")
end
| ((uu____767, st'))::stack -> begin
((pop st.repl_env "#pop");
(FStar_ST.op_Colon_Equals repl_stack stack);
st';
)
end)))


let push_repl : push_kind  ->  repl_task  ->  repl_state  ->  FStar_TypeChecker_Env.env = (fun push_kind task st -> ((

let uu____839 = (

let uu____846 = (FStar_ST.op_Bang repl_stack)
in (((task), (st)))::uu____846)
in (FStar_ST.op_Colon_Equals repl_stack uu____839));
(

let uu____939 = (set_check_kind st.repl_env push_kind)
in (push uu____939 ""));
))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> (

let uu____945 = (

let uu____946 = (FStar_ST.op_Bang repl_stack)
in (FStar_List.length uu____946))
in (Prims.op_Equality uu____945 (FStar_List.length st.repl_deps_stack))))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of FStar_TypeChecker_Env.binding


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____1052 -> begin
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
| uu____1088 -> begin
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
| uu____1118 -> begin
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
| uu____1144 -> begin
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
| NTAlias (host, id1, included) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1190 = (FStar_Ident.text_of_id id1)
in (

let uu____1191 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table uu____1190 [] uu____1191)))
end
| uu____1192 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1200 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_Syntax_DsEnv.Open_module) [] uu____1200))
end
| uu____1201 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____1204 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____1205 -> begin
(query_of_lid host)
end)
in (

let uu____1206 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____1204 uu____1206)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_TypeChecker_Env.Binding_lid (lid, uu____1214) -> begin
(lid)::[]
end
| FStar_TypeChecker_Env.Binding_sig (lids, uu____1216) -> begin
lids
end
| FStar_TypeChecker_Env.Binding_sig_inst (lids, uu____1222, uu____1223) -> begin
lids
end
| uu____1228 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____1240 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (

let uu____1241 = (FStar_Ident.text_of_id lid.FStar_Ident.ident)
in (FStar_Interactive_CompletionTable.insert tbl ns_query uu____1241 lid)))) table lids))
end)))


let commit_name_tracking' : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____1267 = (FStar_Syntax_Syntax.mod_name md)
in uu____1267.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let commit_name_tracking : repl_state  ->  name_tracking_event Prims.list  ->  repl_state = (fun st name_events -> (

let names1 = (commit_name_tracking' st.repl_curmod st.repl_names name_events)
in (

let uu___94_1292 = st
in {repl_line = uu___94_1292.repl_line; repl_column = uu___94_1292.repl_column; repl_fname = uu___94_1292.repl_fname; repl_deps_stack = uu___94_1292.repl_deps_stack; repl_curmod = uu___94_1292.repl_curmod; repl_env = uu___94_1292.repl_env; repl_stdin = uu___94_1292.repl_stdin; repl_names = names1})))


let fresh_name_tracking_hooks : unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____1307 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____1321 = (

let uu____1324 = (FStar_ST.op_Bang events)
in (evt)::uu____1324)
in (FStar_ST.op_Colon_Equals events uu____1321)))
in ((events), ({FStar_Syntax_DsEnv.ds_push_open_hook = (fun dsenv1 op -> (

let uu____1615 = (

let uu____1616 = (

let uu____1621 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1621), (op)))
in NTOpen (uu____1616))
in (push_event uu____1615))); FStar_Syntax_DsEnv.ds_push_include_hook = (fun dsenv1 ns -> (

let uu____1627 = (

let uu____1628 = (

let uu____1633 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1633), (ns)))
in NTInclude (uu____1628))
in (push_event uu____1627))); FStar_Syntax_DsEnv.ds_push_module_abbrev_hook = (fun dsenv1 x l -> (

let uu____1641 = (

let uu____1642 = (

let uu____1649 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1649), (x), (l)))
in NTAlias (uu____1642))
in (push_event uu____1641)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____1654 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : env_t  ->  (env_t * (env_t  ->  (env_t * name_tracking_event Prims.list))) = (fun env -> (

let set_hooks = (fun dshooks tchooks env1 -> (

let uu____1703 = (FStar_Universal.with_tcenv env1 (fun dsenv1 -> (

let uu____1711 = (FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks)
in ((()), (uu____1711)))))
in (match (uu____1703) with
| ((), tcenv') -> begin
(FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks)
end)))
in (

let uu____1713 = (

let uu____1718 = (FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv)
in (

let uu____1719 = (FStar_TypeChecker_Env.tc_hooks env)
in ((uu____1718), (uu____1719))))
in (match (uu____1713) with
| (old_dshooks, old_tchooks) -> begin
(

let uu____1735 = (fresh_name_tracking_hooks ())
in (match (uu____1735) with
| (events, new_dshooks, new_tchooks) -> begin
(

let uu____1770 = (set_hooks new_dshooks new_tchooks env)
in ((uu____1770), ((fun env1 -> (

let uu____1784 = (set_hooks old_dshooks old_tchooks env1)
in (

let uu____1785 = (

let uu____1788 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____1788))
in ((uu____1784), (uu____1785))))))))
end))
end))))


let string_of_repl_task : repl_task  ->  Prims.string = (fun uu___76_1900 -> (match (uu___76_1900) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1903 = (string_of_timed_fname intf)
in (

let uu____1904 = (string_of_timed_fname impl)
in (FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1903 uu____1904)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1906 = (string_of_timed_fname intf_or_impl)
in (FStar_Util.format1 "LDSingle %s" uu____1906))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1908 = (string_of_timed_fname intf)
in (FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1908))
end
| PushFragment (frag) -> begin
(FStar_Util.format1 "PushFragment { code = %s }" frag.FStar_Parser_ParseIt.frag_text)
end))


let tc_one : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env intf_opt modf -> (

let uu____1929 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None intf_opt modf)
in (match (uu____1929) with
| (uu____1943, env1, delta1) -> begin
(

let env2 = (FStar_Universal.apply_delta_env env1 delta1)
in env2)
end)))


let run_repl_task : optmod_t  ->  env_t  ->  repl_task  ->  (optmod_t * env_t) = (fun curmod env task -> (match (task) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1982 = (tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname)) impl.tf_fname)
in ((curmod), (uu____1982)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1984 = (tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname)
in ((curmod), (uu____1984)))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1986 = (FStar_Universal.load_interface_decls env intf.tf_fname)
in ((curmod), (uu____1986)))
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

let uu____2041 = (aux deps' final_tasks1)
in (LDInterleaved ((((wrap intf)), ((wrap impl)))))::uu____2041)
end
| (intf_or_impl)::deps' -> begin
(

let uu____2048 = (aux deps' final_tasks1)
in (LDSingle ((wrap intf_or_impl)))::uu____2048)
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

let uu____2089 = (get_mod_name f)
in (Prims.op_Equality uu____2089 our_mod_name)))
in (

let uu____2090 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____2090) with
| (deps, dep_graph1) -> begin
(

let uu____2113 = (FStar_List.partition has_our_mod_name deps)
in (match (uu____2113) with
| (same_name, real_deps) -> begin
(

let intf_tasks = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____2150 = (

let uu____2151 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____2151)))
in (match (uu____2150) with
| true -> begin
(

let uu____2152 = (

let uu____2157 = (FStar_Util.format1 "Expecting an interface, got %s" intf)
in ((FStar_Errors.Fatal_MissingInterface), (uu____2157)))
in (FStar_Errors.raise_err uu____2152))
end
| uu____2158 -> begin
()
end));
(

let uu____2160 = (

let uu____2161 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____2161)))
in (match (uu____2160) with
| true -> begin
(

let uu____2162 = (

let uu____2167 = (FStar_Util.format1 "Expecting an implementation, got %s" impl)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2167)))
in (FStar_Errors.raise_err uu____2162))
end
| uu____2168 -> begin
()
end));
(LDInterfaceOfCurrentFile ((dummy_tf_of_fname intf)))::[];
)
end
| (impl)::[] -> begin
[]
end
| uu____2170 -> begin
(

let mods_str = (FStar_String.concat " " same_name)
in (

let message = "Too many or too few files matching %s: %s"
in ((

let uu____2176 = (

let uu____2181 = (FStar_Util.format message ((our_mod_name)::(mods_str)::[]))
in ((FStar_Errors.Fatal_TooManyOrTooFewFileMatch), (uu____2181)))
in (FStar_Errors.raise_err uu____2176));
[];
)))
end)
in (

let tasks = (repl_ld_tasks_of_deps real_deps intf_tasks)
in ((real_deps), (tasks), (dep_graph1))))
end))
end))))))


let update_task_timestamps : repl_task  ->  repl_task = (fun uu___77_2193 -> (match (uu___77_2193) with
| LDInterleaved (intf, impl) -> begin
(

let uu____2196 = (

let uu____2201 = (tf_of_fname intf.tf_fname)
in (

let uu____2202 = (tf_of_fname impl.tf_fname)
in ((uu____2201), (uu____2202))))
in LDInterleaved (uu____2196))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____2204 = (tf_of_fname intf_or_impl.tf_fname)
in LDSingle (uu____2204))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____2206 = (tf_of_fname intf.tf_fname)
in LDInterfaceOfCurrentFile (uu____2206))
end
| PushFragment (frag) -> begin
PushFragment (frag)
end))


let run_repl_transaction : repl_state  ->  push_kind  ->  Prims.bool  ->  repl_task  ->  (Prims.bool * repl_state) = (fun st push_kind must_rollback task -> (

let env = (push_repl push_kind task st)
in (

let uu____2233 = (track_name_changes env)
in (match (uu____2233) with
| (env1, finish_name_tracking) -> begin
(

let check_success = (fun uu____2276 -> ((

let uu____2279 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2279 (Prims.parse_int "0"))) && (not (must_rollback))))
in (

let uu____2280 = (

let uu____2287 = (with_captured_errors env1 (fun env2 -> (

let uu____2301 = (run_repl_task st.repl_curmod env2 task)
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____2301))))
in (match (uu____2287) with
| FStar_Pervasives_Native.Some (curmod, env2) when (check_success ()) -> begin
((curmod), (env2), (true))
end
| uu____2332 -> begin
((st.repl_curmod), (env1), (false))
end))
in (match (uu____2280) with
| (curmod, env2, success) -> begin
(

let uu____2346 = (finish_name_tracking env2)
in (match (uu____2346) with
| (env', name_events) -> begin
(

let st1 = (

let uu___95_2364 = st
in {repl_line = uu___95_2364.repl_line; repl_column = uu___95_2364.repl_column; repl_fname = uu___95_2364.repl_fname; repl_deps_stack = uu___95_2364.repl_deps_stack; repl_curmod = curmod; repl_env = env2; repl_stdin = uu___95_2364.repl_stdin; repl_names = uu___95_2364.repl_names})
in (

let st2 = (match (success) with
| true -> begin
(commit_name_tracking st1 name_events)
end
| uu____2366 -> begin
(pop_repl st1)
end)
in ((success), (st2))))
end))
end)))
end))))


let run_repl_ld_transactions : repl_state  ->  repl_task Prims.list  ->  (repl_state, repl_state) FStar_Util.either = (fun st tasks -> (

let debug1 = (fun verb task -> (

let uu____2396 = (FStar_Options.debug_any ())
in (match (uu____2396) with
| true -> begin
(

let uu____2397 = (string_of_repl_task task)
in (FStar_Util.print2 "%s %s" verb uu____2397))
end
| uu____2398 -> begin
()
end)))
in (

let rec revert_many = (fun st1 uu___78_2415 -> (match (uu___78_2415) with
| [] -> begin
st1
end
| ((task, _st'))::entries -> begin
((debug1 "Reverting" task);
(

let uu____2442 = (pop_repl st1)
in (revert_many uu____2442 entries));
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

let uu____2493 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____2493 (fun a240 -> ())));
(

let timestamped_task = (update_task_timestamps task)
in (

let push_kind = (

let uu____2496 = (FStar_Options.lax ())
in (match (uu____2496) with
| true -> begin
LaxCheck
end
| uu____2497 -> begin
FullCheck
end))
in (

let uu____2498 = (run_repl_transaction st1 push_kind false timestamped_task)
in (match (uu____2498) with
| (success, st2) -> begin
(match (success) with
| true -> begin
(

let uu____2513 = (

let uu___96_2514 = st2
in (

let uu____2515 = (FStar_ST.op_Bang repl_stack)
in {repl_line = uu___96_2514.repl_line; repl_column = uu___96_2514.repl_column; repl_fname = uu___96_2514.repl_fname; repl_deps_stack = uu____2515; repl_curmod = uu___96_2514.repl_curmod; repl_env = uu___96_2514.repl_env; repl_stdin = uu___96_2514.repl_stdin; repl_names = uu___96_2514.repl_names}))
in (aux uu____2513 tasks2 []))
end
| uu____2563 -> begin
FStar_Util.Inr (st2)
end)
end))));
)
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____2576 = (update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst prev) uu____2576)) -> begin
((debug1 "Skipping" task);
(aux st1 tasks2 previous1);
)
end
| (tasks2, previous1) -> begin
(

let uu____2588 = (revert_many st1 previous1)
in (aux uu____2588 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.repl_deps_stack))))))


let json_debug : FStar_Util.json  ->  Prims.string = (fun uu___79_2597 -> (match (uu___79_2597) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____2599 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____2601 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____2601))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____2603) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____2606) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2626) -> begin
true
end
| uu____2631 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2646) -> begin
uu____2646
end))


let js_fail : 'Auu____2657 . Prims.string  ->  FStar_Util.json  ->  'Auu____2657 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___80_2672 -> (match (uu___80_2672) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___81_2679 -> (match (uu___81_2679) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____2688 . (FStar_Util.json  ->  'Auu____2688)  ->  FStar_Util.json  ->  'Auu____2688 Prims.list = (fun k uu___82_2703 -> (match (uu___82_2703) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___83_2722 -> (match (uu___83_2722) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____2748 = (js_str s)
in (match (uu____2748) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____2749 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____2755 = (js_str s)
in (match (uu____2755) with
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
| uu____2756 -> begin
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
| uu____2776 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____2783 -> begin
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
| uu____2801 -> begin
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

let uu____2831 = (js_str k1)
in (match (uu____2831) with
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
| uu____2832 -> begin
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
| uu____2838 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____2844 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____2850 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____2856 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____2867 = (js_str k1)
in (match (uu____2867) with
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
| uu____2868 -> begin
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
| uu____2965 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____2971 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____2977 -> begin
false
end))


let uu___is_Segment : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
true
end
| uu____2984 -> begin
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
| uu____2997 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____3004 -> begin
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
| uu____3024 -> begin
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
| uu____3060 -> begin
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
| uu____3098 -> begin
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
| uu____3156 -> begin
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
| uu____3194 -> begin
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
| uu____3208 -> begin
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
| uu____3222 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___84_3248 -> (match (uu___84_3248) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Segment (uu____3249) -> begin
false
end
| Pop -> begin
false
end
| Push ({push_kind = uu____3250; push_code = uu____3251; push_line = uu____3252; push_column = uu____3253; push_peek_only = false}) -> begin
false
end
| VfsAdd (uu____3254) -> begin
false
end
| GenericError (uu____3261) -> begin
false
end
| ProtocolViolation (uu____3262) -> begin
false
end
| Push (uu____3263) -> begin
true
end
| AutoComplete (uu____3264) -> begin
true
end
| Lookup (uu____3269) -> begin
true
end
| Compute (uu____3282) -> begin
true
end
| Search (uu____3291) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::("segment")::("vfs-add")::("tactic-ranges")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3303) -> begin
true
end
| uu____3304 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3311) -> begin
uu____3311
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____3317 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____3323 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____3329 -> begin
false
end))


let try_assoc : 'Auu____3338 'Auu____3339 . 'Auu____3338  ->  ('Auu____3338 * 'Auu____3339) Prims.list  ->  'Auu____3339 FStar_Pervasives_Native.option = (fun key a -> (

let uu____3364 = (FStar_Util.try_find (fun uu____3378 -> (match (uu____3378) with
| (k, uu____3384) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____3364)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____3404 = (

let uu____3405 = (

let uu____3406 = (json_debug got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____3406))
in ProtocolViolation (uu____3405))
in {qq = uu____3404; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____3440 = (try_assoc key a)
in (match (uu____3440) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3444 = (

let uu____3445 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____3445))
in (FStar_Exn.raise uu____3444))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____3460 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____3460 js_str))
in (FStar_All.try_with (fun uu___98_3467 -> (match (()) with
| () -> begin
(

let query = (

let uu____3469 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____3469 js_str))
in (

let args = (

let uu____3477 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____3477 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____3498 = (try_assoc k args)
in (match (uu____3498) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____3506 = (match (query) with
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

let uu____3507 = (

let uu____3508 = (arg "code")
in (FStar_All.pipe_right uu____3508 js_str))
in Segment (uu____3507))
end
| "peek" -> begin
(

let uu____3509 = (

let uu____3510 = (

let uu____3511 = (arg "kind")
in (FStar_All.pipe_right uu____3511 js_pushkind))
in (

let uu____3512 = (

let uu____3513 = (arg "code")
in (FStar_All.pipe_right uu____3513 js_str))
in (

let uu____3514 = (

let uu____3515 = (arg "line")
in (FStar_All.pipe_right uu____3515 js_int))
in (

let uu____3516 = (

let uu____3517 = (arg "column")
in (FStar_All.pipe_right uu____3517 js_int))
in {push_kind = uu____3510; push_code = uu____3512; push_line = uu____3514; push_column = uu____3516; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3509))
end
| "push" -> begin
(

let uu____3518 = (

let uu____3519 = (

let uu____3520 = (arg "kind")
in (FStar_All.pipe_right uu____3520 js_pushkind))
in (

let uu____3521 = (

let uu____3522 = (arg "code")
in (FStar_All.pipe_right uu____3522 js_str))
in (

let uu____3523 = (

let uu____3524 = (arg "line")
in (FStar_All.pipe_right uu____3524 js_int))
in (

let uu____3525 = (

let uu____3526 = (arg "column")
in (FStar_All.pipe_right uu____3526 js_int))
in {push_kind = uu____3519; push_code = uu____3521; push_line = uu____3523; push_column = uu____3525; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3518))
end
| "autocomplete" -> begin
(

let uu____3527 = (

let uu____3532 = (

let uu____3533 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____3533 js_str))
in (

let uu____3534 = (

let uu____3535 = (try_arg "context")
in (FStar_All.pipe_right uu____3535 js_optional_completion_context))
in ((uu____3532), (uu____3534))))
in AutoComplete (uu____3527))
end
| "lookup" -> begin
(

let uu____3540 = (

let uu____3553 = (

let uu____3554 = (arg "symbol")
in (FStar_All.pipe_right uu____3554 js_str))
in (

let uu____3555 = (

let uu____3556 = (try_arg "context")
in (FStar_All.pipe_right uu____3556 js_optional_lookup_context))
in (

let uu____3561 = (

let uu____3570 = (

let uu____3579 = (try_arg "location")
in (FStar_All.pipe_right uu____3579 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____3570 (FStar_Util.map_option (fun loc -> (

let uu____3637 = (

let uu____3638 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____3638 js_str))
in (

let uu____3639 = (

let uu____3640 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____3640 js_int))
in (

let uu____3641 = (

let uu____3642 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____3642 js_int))
in ((uu____3637), (uu____3639), (uu____3641)))))))))
in (

let uu____3643 = (

let uu____3646 = (arg "requested-info")
in (FStar_All.pipe_right uu____3646 (js_list js_str)))
in ((uu____3553), (uu____3555), (uu____3561), (uu____3643))))))
in Lookup (uu____3540))
end
| "compute" -> begin
(

let uu____3659 = (

let uu____3668 = (

let uu____3669 = (arg "term")
in (FStar_All.pipe_right uu____3669 js_str))
in (

let uu____3670 = (

let uu____3675 = (try_arg "rules")
in (FStar_All.pipe_right uu____3675 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____3668), (uu____3670))))
in Compute (uu____3659))
end
| "search" -> begin
(

let uu____3690 = (

let uu____3691 = (arg "terms")
in (FStar_All.pipe_right uu____3691 js_str))
in Search (uu____3690))
end
| "vfs-add" -> begin
(

let uu____3692 = (

let uu____3699 = (

let uu____3702 = (try_arg "filename")
in (FStar_All.pipe_right uu____3702 (FStar_Util.map_option js_str)))
in (

let uu____3709 = (

let uu____3710 = (arg "contents")
in (FStar_All.pipe_right uu____3710 js_str))
in ((uu____3699), (uu____3709))))
in VfsAdd (uu____3692))
end
| uu____3713 -> begin
(

let uu____3714 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____3714))
end)
in {qq = uu____3506; qid = qid})))))
end)) (fun uu___97_3717 -> (match (uu___97_3717) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let deserialize_interactive_query : FStar_Util.json  ->  query = (fun js_query -> (FStar_All.try_with (fun uu___100_3727 -> (match (()) with
| () -> begin
(unpack_interactive_query js_query)
end)) (fun uu___99_3730 -> (match (uu___99_3730) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let parse_interactive_query : Prims.string  ->  query = (fun query_str -> (

let uu____3739 = (FStar_Util.json_of_string query_str)
in (match (uu____3739) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(deserialize_interactive_query request)
end)))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (

let uu____3748 = (FStar_Util.read_line stream)
in (match (uu____3748) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(parse_interactive_query line)
end)))


let json_of_opt : 'Auu____3758 . ('Auu____3758  ->  FStar_Util.json)  ->  'Auu____3758 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____3778 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____3778)))


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

let uu____3791 = (

let uu____3798 = (

let uu____3805 = (

let uu____3812 = (

let uu____3817 = (

let uu____3818 = (

let uu____3821 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3827 = (FStar_Range.json_of_use_range r)
in (uu____3827)::[])
end)
in (

let uu____3828 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (

let uu____3834 = (FStar_Range.def_range r)
in (

let uu____3835 = (FStar_Range.use_range r)
in (Prims.op_disEquality uu____3834 uu____3835))) -> begin
(

let uu____3836 = (FStar_Range.json_of_def_range r)
in (uu____3836)::[])
end
| uu____3837 -> begin
[]
end)
in (FStar_List.append uu____3821 uu____3828)))
in FStar_Util.JsonList (uu____3818))
in (("ranges"), (uu____3817)))
in (uu____3812)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____3805)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____3798)
in FStar_Util.JsonAssoc (uu____3791)))

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

let uu____4006 = (

let uu____4013 = (

let uu____4018 = (json_of_opt FStar_Range.json_of_def_range lr.slr_def_range)
in (("defined-at"), (uu____4018)))
in (

let uu____4019 = (

let uu____4026 = (

let uu____4031 = (json_of_opt (fun _0_18 -> FStar_Util.JsonStr (_0_18)) lr.slr_typ)
in (("type"), (uu____4031)))
in (

let uu____4032 = (

let uu____4039 = (

let uu____4044 = (json_of_opt (fun _0_19 -> FStar_Util.JsonStr (_0_19)) lr.slr_doc)
in (("documentation"), (uu____4044)))
in (

let uu____4045 = (

let uu____4052 = (

let uu____4057 = (json_of_opt (fun _0_20 -> FStar_Util.JsonStr (_0_20)) lr.slr_def)
in (("definition"), (uu____4057)))
in (uu____4052)::[])
in (uu____4039)::uu____4045))
in (uu____4026)::uu____4032))
in (uu____4013)::uu____4019))
in ((("name"), (FStar_Util.JsonStr (lr.slr_name))))::uu____4006))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4090 = (FStar_List.map (fun _0_21 -> FStar_Util.JsonStr (_0_21)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_22 -> FStar_Util.JsonList (_0_22)) uu____4090))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____4112 -> begin
false
end))


let uu___is_OptReset : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReset -> begin
true
end
| uu____4118 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____4124 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___85_4129 -> (match (uu___85_4129) with
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


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___86_4322 -> (match (uu___86_4322) with
| FStar_Options.Const (uu____4323) -> begin
"flag"
end
| FStar_Options.IntStr (uu____4324) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____4325) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____4326) -> begin
"string"
end
| FStar_Options.EnumStr (uu____4327) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____4330) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____4337, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____4347, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let rec snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.strcat "${" (Prims.strcat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.strcat "--" (Prims.strcat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.strcat " " argstring)
end
| uu____4384 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____4395) -> begin
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
| FStar_Options.PostProcessed (uu____4408, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____4418, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____4426 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____4426))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___87_4433 -> (match (uu___87_4433) with
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

let uu____4441 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____4441))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____4455 = (

let uu____4462 = (

let uu____4469 = (

let uu____4474 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____4474)))
in (

let uu____4475 = (

let uu____4482 = (

let uu____4487 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____4487)))
in (

let uu____4488 = (

let uu____4495 = (

let uu____4500 = (json_of_opt (fun _0_23 -> FStar_Util.JsonStr (_0_23)) opt.opt_documentation)
in (("documentation"), (uu____4500)))
in (

let uu____4501 = (

let uu____4508 = (

let uu____4513 = (

let uu____4514 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____4514))
in (("type"), (uu____4513)))
in (uu____4508)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____4495)::uu____4501))
in (uu____4482)::uu____4488))
in (uu____4469)::uu____4475))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____4462)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____4455))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____4552 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____4552)))


let write_json : FStar_Util.json  ->  unit = (fun json -> ((

let uu____4565 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____4565));
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

let uu____4628 = (

let uu____4635 = (

let uu____4642 = (

let uu____4647 = (

let uu____4648 = (FStar_ST.op_Bang repl_current_qid)
in (json_of_opt (fun _0_24 -> FStar_Util.JsonStr (_0_24)) uu____4648))
in (("query-id"), (uu____4647)))
in (uu____4642)::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (js_contents)))::[])
in ((("kind"), (FStar_Util.JsonStr ("message"))))::uu____4635)
in FStar_Util.JsonAssoc (uu____4628)))


let forward_message : 'Auu____4712 . (FStar_Util.json  ->  'Auu____4712)  ->  Prims.string  ->  FStar_Util.json  ->  'Auu____4712 = (fun callback level contents -> (

let uu____4733 = (json_of_message level contents)
in (callback uu____4733)))


let json_of_hello : FStar_Util.json = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4736 = (FStar_List.map (fun _0_25 -> FStar_Util.JsonStr (_0_25)) interactive_protocol_features)
in FStar_Util.JsonList (uu____4736))
in FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info)))


let write_hello : unit  ->  unit = (fun uu____4747 -> (write_json json_of_hello))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.strcat "--" name)
in (

let uu____4759 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____4759) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.strcat flag (Prims.strcat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____4768 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____4797 -> (match (uu____4797) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____4812 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____4812 (FStar_Util.map_option (fun default_value -> (

let uu____4824 = (sig_of_fstar_option name typ)
in (

let uu____4825 = (snippets_of_fstar_option name typ)
in (

let uu____4828 = (

let uu____4829 = (FStar_Options.settable name)
in (match (uu____4829) with
| true -> begin
OptSet
end
| uu____4830 -> begin
(

let uu____4831 = (FStar_Options.resettable name)
in (match (uu____4831) with
| true -> begin
OptReset
end
| uu____4832 -> begin
OptReadOnly
end))
end))
in {opt_name = name; opt_sig = uu____4824; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____4825; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4835 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____4828})))))))
end))))
in (FStar_All.pipe_right uu____4768 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___101_4857 = opt
in (

let uu____4858 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___101_4857.opt_name; opt_sig = uu___101_4857.opt_sig; opt_value = uu____4858; opt_default = uu___101_4857.opt_default; opt_type = uu___101_4857.opt_type; opt_snippets = uu___101_4857.opt_snippets; opt_documentation = uu___101_4857.opt_documentation; opt_permission_level = uu___101_4857.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____4871 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____4871)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____4888 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____4888)))
end
| uu____4889 -> begin
((""), (opt_name))
end)))


let json_of_repl_state : repl_state  ->  FStar_Util.json = (fun st -> (

let filenames = (fun uu____4906 -> (match (uu____4906) with
| (task, uu____4914) -> begin
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
| PushFragment (uu____4921) -> begin
[]
end)
end))
in (

let uu____4922 = (

let uu____4929 = (

let uu____4934 = (

let uu____4935 = (

let uu____4938 = (FStar_List.concatMap filenames st.repl_deps_stack)
in (FStar_List.map (fun _0_26 -> FStar_Util.JsonStr (_0_26)) uu____4938))
in FStar_Util.JsonList (uu____4935))
in (("loaded-dependencies"), (uu____4934)))
in (

let uu____4945 = (

let uu____4952 = (

let uu____4957 = (

let uu____4958 = (

let uu____4961 = (current_fstar_options (fun uu____4966 -> true))
in (FStar_List.map json_of_fstar_option uu____4961))
in FStar_Util.JsonList (uu____4958))
in (("options"), (uu____4957)))
in (uu____4952)::[])
in (uu____4929)::uu____4945))
in FStar_Util.JsonAssoc (uu____4922))))


let with_printed_effect_args : 'Auu____4983 . (unit  ->  'Auu____4983)  ->  'Auu____4983 = (fun k -> (FStar_Options.with_saved_options (fun uu____4996 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____5009 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____5016 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____5023 'Auu____5024 . 'Auu____5023  ->  ((query_status * FStar_Util.json) * ('Auu____5024, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____5056 'Auu____5057 . 'Auu____5056  ->  ((query_status * FStar_Util.json) * ('Auu____5056, 'Auu____5057) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____5087 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5087) FStar_Util.either) = (fun st -> (

let uu____5105 = (

let uu____5110 = (json_of_repl_state st)
in ((QueryOK), (uu____5110)))
in ((uu____5105), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____5127 'Auu____5128 . 'Auu____5127  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____5127, 'Auu____5128) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_generic_error : 'Auu____5167 'Auu____5168 . 'Auu____5167  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____5167, 'Auu____5168) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let collect_errors : unit  ->  FStar_Errors.issue Prims.list = (fun uu____5205 -> (

let errors = (FStar_Errors.report_all ())
in ((FStar_Errors.clear ());
errors;
)))


let run_segment : 'Auu____5216 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5216) FStar_Util.either) = (fun st code -> (

let frag = {FStar_Parser_ParseIt.frag_text = code; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let collect_decls = (fun uu____5247 -> (

let uu____5248 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____5248) with
| FStar_Parser_Driver.Empty -> begin
[]
end
| FStar_Parser_Driver.Decls (decls) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu____5254, decls)) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface (uu____5260, decls, uu____5262)) -> begin
decls
end)))
in (

let uu____5267 = (with_captured_errors st.repl_env (fun uu____5276 -> (

let uu____5277 = (collect_decls ())
in (FStar_All.pipe_left (fun _0_27 -> FStar_Pervasives_Native.Some (_0_27)) uu____5277))))
in (match (uu____5267) with
| FStar_Pervasives_Native.None -> begin
(

let errors = (

let uu____5305 = (collect_errors ())
in (FStar_All.pipe_right uu____5305 (FStar_List.map json_of_issue)))
in ((((QueryNOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl (st))))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let json_of_decl = (fun decl -> (

let uu____5331 = (

let uu____5338 = (

let uu____5343 = (FStar_Range.json_of_def_range (FStar_Parser_AST.decl_drange decl))
in (("def_range"), (uu____5343)))
in (uu____5338)::[])
in FStar_Util.JsonAssoc (uu____5331)))
in (

let js_decls = (

let uu____5353 = (FStar_List.map json_of_decl decls)
in (FStar_All.pipe_left (fun _0_28 -> FStar_Util.JsonList (_0_28)) uu____5353))
in ((((QueryOK), (FStar_Util.JsonAssoc (((("decls"), (js_decls)))::[])))), (FStar_Util.Inl (st)))))
end)))))


let run_vfs_add : 'Auu____5382 . repl_state  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5382) FStar_Util.either) = (fun st opt_fname contents -> (

let fname = (FStar_Util.dflt st.repl_fname opt_fname)
in ((FStar_Parser_ParseIt.add_vfs_entry fname contents);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st)));
)))


let run_pop : 'Auu____5428 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5428) FStar_Util.either) = (fun st -> (

let uu____5446 = (nothing_left_to_pop st)
in (match (uu____5446) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____5467 -> begin
(

let st' = (pop_repl st)
in ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st'))))
end)))


let load_deps : repl_state  ->  ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either = (fun st -> (

let uu____5492 = (with_captured_errors st.repl_env (fun _env -> (

let uu____5518 = (deps_and_repl_ld_tasks_of_our_file st.repl_fname)
in (FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) uu____5518))))
in (match (uu____5492) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (st)
end
| FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___102_5609 = st
in (

let uu____5610 = (FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1)
in {repl_line = uu___102_5609.repl_line; repl_column = uu___102_5609.repl_column; repl_fname = uu___102_5609.repl_fname; repl_deps_stack = uu___102_5609.repl_deps_stack; repl_curmod = uu___102_5609.repl_curmod; repl_env = uu____5610; repl_stdin = uu___102_5609.repl_stdin; repl_names = uu___102_5609.repl_names}))
in (

let uu____5611 = (run_repl_ld_transactions st1 tasks)
in (match (uu____5611) with
| FStar_Util.Inr (st2) -> begin
FStar_Util.Inr (st2)
end
| FStar_Util.Inl (st2) -> begin
FStar_Util.Inl (((st2), (deps)))
end)))
end)))


let rephrase_dependency_error : FStar_Errors.issue  ->  FStar_Errors.issue = (fun issue -> (

let uu___103_5647 = issue
in (

let uu____5648 = (FStar_Util.format1 "Error while computing or loading dependencies:\n%s" issue.FStar_Errors.issue_message)
in {FStar_Errors.issue_message = uu____5648; FStar_Errors.issue_level = uu___103_5647.FStar_Errors.issue_level; FStar_Errors.issue_range = uu___103_5647.FStar_Errors.issue_range; FStar_Errors.issue_number = uu___103_5647.FStar_Errors.issue_number})))


let run_push_without_deps : 'Auu____5655 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5655) FStar_Util.either) = (fun st query -> (

let set_nosynth_flag = (fun st1 flag -> (

let uu___104_5689 = st1
in {repl_line = uu___104_5689.repl_line; repl_column = uu___104_5689.repl_column; repl_fname = uu___104_5689.repl_fname; repl_deps_stack = uu___104_5689.repl_deps_stack; repl_curmod = uu___104_5689.repl_curmod; repl_env = (

let uu___105_5691 = st1.repl_env
in {FStar_TypeChecker_Env.solver = uu___105_5691.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_5691.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_5691.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_5691.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_5691.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_5691.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_5691.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_5691.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_5691.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_5691.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_5691.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_5691.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_5691.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___105_5691.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_5691.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___105_5691.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___105_5691.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_5691.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_5691.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_5691.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___105_5691.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = flag; FStar_TypeChecker_Env.tc_term = uu___105_5691.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___105_5691.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_5691.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___105_5691.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_5691.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___105_5691.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___105_5691.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___105_5691.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___105_5691.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___105_5691.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___105_5691.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___105_5691.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___105_5691.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___105_5691.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___105_5691.FStar_TypeChecker_Env.dep_graph}); repl_stdin = uu___104_5689.repl_stdin; repl_names = uu___104_5689.repl_names}))
in (

let uu____5692 = query
in (match (uu____5692) with
| {push_kind = push_kind; push_code = text; push_line = line; push_column = column; push_peek_only = peek_only} -> begin
(

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in ((FStar_TypeChecker_Env.toggle_id_info st.repl_env true);
(

let st1 = (set_nosynth_flag st peek_only)
in (

let uu____5713 = (run_repl_transaction st1 push_kind peek_only (PushFragment (frag)))
in (match (uu____5713) with
| (success, st2) -> begin
(

let st3 = (set_nosynth_flag st2 false)
in (

let status = (match ((success || peek_only)) with
| true -> begin
QueryOK
end
| uu____5734 -> begin
QueryNOK
end)
in (

let json_errors = (

let uu____5736 = (

let uu____5739 = (collect_errors ())
in (FStar_All.pipe_right uu____5739 (FStar_List.map json_of_issue)))
in FStar_Util.JsonList (uu____5736))
in (

let st4 = (match (success) with
| true -> begin
(

let uu___106_5747 = st3
in {repl_line = line; repl_column = column; repl_fname = uu___106_5747.repl_fname; repl_deps_stack = uu___106_5747.repl_deps_stack; repl_curmod = uu___106_5747.repl_curmod; repl_env = uu___106_5747.repl_env; repl_stdin = uu___106_5747.repl_stdin; repl_names = uu___106_5747.repl_names})
end
| uu____5748 -> begin
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
| uu____5762 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____5764 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat (FStar_String.uppercase first) uu____5764)))
end))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____5794 = (FStar_Util.psmap_empty ())
in (

let uu____5797 = (

let uu____5800 = (FStar_Options.prims ())
in (uu____5800)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____5810 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____5810 true))) uu____5794 uu____5797)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____5828 -> (match (uu____5828) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____5836 -> begin
(

let ns_query = (

let uu____5840 = (capitalize modname)
in (FStar_Util.split uu____5840 "."))
in (

let uu____5841 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____5841 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods)))))))


let run_push_with_deps : 'Auu____5852 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5852) FStar_Util.either) = (fun st query -> ((

let uu____5876 = (FStar_Options.debug_any ())
in (match (uu____5876) with
| true -> begin
(FStar_Util.print_string "Reloading dependencies")
end
| uu____5877 -> begin
()
end));
(FStar_TypeChecker_Env.toggle_id_info st.repl_env false);
(

let uu____5879 = (load_deps st)
in (match (uu____5879) with
| FStar_Util.Inr (st1) -> begin
(

let errors = (

let uu____5912 = (collect_errors ())
in (FStar_List.map rephrase_dependency_error uu____5912))
in (

let js_errors = (FStar_All.pipe_right errors (FStar_List.map json_of_issue))
in ((((QueryNOK), (FStar_Util.JsonList (js_errors)))), (FStar_Util.Inl (st1)))))
end
| FStar_Util.Inl (st1, deps) -> begin
((

let uu____5943 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____5943 (fun a241 -> ())));
(

let names1 = (add_module_completions st1.repl_fname deps st1.repl_names)
in (run_push_without_deps (

let uu___107_5946 = st1
in {repl_line = uu___107_5946.repl_line; repl_column = uu___107_5946.repl_column; repl_fname = uu___107_5946.repl_fname; repl_deps_stack = uu___107_5946.repl_deps_stack; repl_curmod = uu___107_5946.repl_curmod; repl_env = uu___107_5946.repl_env; repl_stdin = uu___107_5946.repl_stdin; repl_names = names1}) query));
)
end));
))


let run_push : 'Auu____5953 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5953) FStar_Util.either) = (fun st query -> (

let uu____5976 = (nothing_left_to_pop st)
in (match (uu____5976) with
| true -> begin
(run_push_with_deps st query)
end
| uu____5989 -> begin
(run_push_without_deps st query)
end)))


let run_symbol_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let tcenv = st.repl_env
in (

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____6064 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____6064))
in (

let lid1 = (

let uu____6068 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____6068))
in (

let uu____6073 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____6073 (FStar_Util.map_option (fun uu____6128 -> (match (uu____6128) with
| ((uu____6147, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____6166 = (FStar_Syntax_DsEnv.try_lookup_doc tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____6166 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____6197 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____6197 (fun uu___88_6241 -> (match (uu___88_6241) with
| (FStar_Util.Inr (se, uu____6263), uu____6264) -> begin
(

let uu____6293 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____6293))
end
| uu____6294 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____6346 -> (match (uu____6346) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____6393) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6446 -> begin
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

let uu____6521 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____6521))
end
| uu____6522 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____6529 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____6540 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range1 = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____6550 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {slr_name = name; slr_def_range = def_range1; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}
in (

let uu____6552 = (

let uu____6563 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____6563)))
in FStar_Pervasives_Native.Some (uu____6552))))))))
end)
in (match (response) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (info) -> begin
FStar_Util.Inr (info)
end)))))))))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____6670 = (trim_option_name opt_name)
in (match (uu____6670) with
| (uu____6689, trimmed_name) -> begin
(

let uu____6691 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____6691) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.strcat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____6719 = (

let uu____6730 = (

let uu____6737 = (update_option opt)
in (alist_of_fstar_option uu____6737))
in (("option"), (uu____6730)))
in FStar_Util.Inr (uu____6719))
end))
end)))


let run_module_lookup : repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____6781 = (FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names query)
in (match (uu____6781) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____6809 = (

let uu____6820 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____6820)))
in FStar_Util.Inr (uu____6809))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____6844 = (

let uu____6855 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____6855)))
in FStar_Util.Inr (uu____6844))
end))))


let run_code_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____6932 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____6932) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____6992) -> begin
(

let uu____7003 = (run_module_lookup st symbol)
in (match (uu____7003) with
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


let run_lookup : 'Auu____7169 . repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7169) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____7227 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____7227) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let code_autocomplete_mod_filter : 'Auu____7313 . ('Auu____7313 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____7313 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___89_7328 -> (match (uu___89_7328) with
| (uu____7333, FStar_Interactive_CompletionTable.Namespace (uu____7334)) -> begin
FStar_Pervasives_Native.None
end
| (uu____7339, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____7340; FStar_Interactive_CompletionTable.mod_path = uu____7341; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____7348 = (

let uu____7353 = (

let uu____7354 = (

let uu___108_7355 = md
in (

let uu____7356 = (

let uu____7357 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.strcat uu____7357 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____7356; FStar_Interactive_CompletionTable.mod_path = uu___108_7355.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___108_7355.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____7354))
in ((pth), (uu____7353)))
in FStar_Pervasives_Native.Some (uu____7348))
end))


let run_code_autocomplete : 'Auu____7368 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7368) FStar_Util.either) = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names needle)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result (FStar_List.append lids mods_and_nss))
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st))))))))


let run_module_autocomplete : 'Auu____7425 'Auu____7426 'Auu____7427 . repl_state  ->  Prims.string  ->  'Auu____7425  ->  'Auu____7426  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7427) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle (fun _0_30 -> FStar_Pervasives_Native.Some (_0_30)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : Prims.int  ->  Prims.bool  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____7498 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReset -> begin
((is_reset), ("#reset-only"))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____7498) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____7513 -> begin
(Prims.strcat "(" (Prims.strcat explanation (Prims.strcat " " (Prims.strcat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____7530 'Auu____7531 . 'Auu____7530  ->  Prims.string  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * ('Auu____7530, 'Auu____7531) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____7559 = (trim_option_name search_term)
in (match (uu____7559) with
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
| (uu____7614, uu____7615) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____7632 . repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7632) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_and_rewind : 'Auu____7671 'Auu____7672 . repl_state  ->  (repl_state  ->  'Auu____7671)  ->  ('Auu____7671 * (repl_state, 'Auu____7672) FStar_Util.either) = (fun st task -> (

let env' = (push st.repl_env "#compute")
in (

let results = (FStar_All.try_with (fun uu___110_7708 -> (match (()) with
| () -> begin
(

let uu____7713 = (task st)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Util.Inl (_0_31)) uu____7713))
end)) (fun uu___109_7720 -> (match (uu___109_7720) with
| e -> begin
FStar_Util.Inr (e)
end)))
in ((pop env' "#compute");
(match (results) with
| FStar_Util.Inl (results1) -> begin
((results1), (FStar_Util.Inl ((

let uu___111_7741 = st
in {repl_line = uu___111_7741.repl_line; repl_column = uu___111_7741.repl_column; repl_fname = uu___111_7741.repl_fname; repl_deps_stack = uu___111_7741.repl_deps_stack; repl_curmod = uu___111_7741.repl_curmod; repl_env = env'; repl_stdin = uu___111_7741.repl_stdin; repl_names = uu___111_7741.repl_names}))))
end
| FStar_Util.Inr (e) -> begin
(FStar_Exn.raise e)
end);
))))


let run_with_parsed_and_tc_term : 'Auu____7767 'Auu____7768 'Auu____7769 . repl_state  ->  Prims.string  ->  'Auu____7767  ->  'Auu____7768  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (query_status * FStar_Util.json))  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7769) FStar_Util.either) = (fun st term line column continuation -> (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____7862, ({FStar_Syntax_Syntax.lbname = uu____7863; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____7865; FStar_Syntax_Syntax.lbeff = uu____7866; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____7868; FStar_Syntax_Syntax.lbpos = uu____7869})::[]), uu____7870); FStar_Syntax_Syntax.sigrng = uu____7871; FStar_Syntax_Syntax.sigquals = uu____7872; FStar_Syntax_Syntax.sigmeta = uu____7873; FStar_Syntax_Syntax.sigattrs = uu____7874})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____7917 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____7938 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____7938) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____7944) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____7969 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun env decls -> (

let uu____7987 = (

let uu____7992 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts decls)
in (uu____7992 env.FStar_TypeChecker_Env.dsenv))
in (FStar_Pervasives_Native.fst uu____7987)))
in (

let typecheck = (fun tcenv decls -> (

let uu____8016 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____8016) with
| (ses, uu____8030, uu____8031) -> begin
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
| uu____8054 -> begin
(

let uu____8055 = (parse1 frag)
in (match (uu____8055) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____8080 -> (

let decls1 = (desugar tcenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____8115 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____8115) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (continuation tcenv1 def1))
end))
end))))
in (

let uu____8127 = (FStar_Options.trace_error ())
in (match (uu____8127) with
| true -> begin
(aux ())
end
| uu____8132 -> begin
(FStar_All.try_with (fun uu___113_8138 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___112_8146 -> (match (uu___112_8146) with
| e -> begin
(

let uu____8152 = (

let uu____8153 = (FStar_Errors.issue_of_exn e)
in (match (uu____8153) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____8157 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____8157))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise e)
end))
in ((QueryNOK), (uu____8152)))
end)))
end)))
end))
end)))))))))))


let run_compute : 'Auu____8166 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8166) FStar_Util.either) = (fun st term rules -> (

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

let uu____8238 = (

let uu____8239 = (term_to_string tcenv normalized)
in FStar_Util.JsonStr (uu____8239))
in ((QueryOK), (uu____8238)))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____8266 -> begin
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
| uu____8280 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___90_8306 -> (match (uu___90_8306) with
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

let uu____8761 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____8768 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____8761; sc_fvars = uu____8768})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____8931 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____8931) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____8971 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____8971) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____8992, typ), uu____8994) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____9055 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____9055) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____9109 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____9109))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun tcenv sc -> (

let typ_str = (

let uu____9161 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____9161))
in (

let uu____9162 = (

let uu____9169 = (

let uu____9174 = (

let uu____9175 = (

let uu____9176 = (FStar_Syntax_DsEnv.shorten_lid tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid)
in uu____9176.FStar_Ident.str)
in FStar_Util.JsonStr (uu____9175))
in (("lid"), (uu____9174)))
in (uu____9169)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____9162))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____9198) -> begin
true
end
| uu____9199 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____9206) -> begin
uu____9206
end))


let run_search : 'Auu____9213 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____9213) FStar_Util.either) = (fun st search_str -> (

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

let uu____9254 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____9254))
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
| uu____9273 -> begin
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
| uu____9282 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____9284 = (

let uu____9285 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____9285))
in (FStar_Exn.raise uu____9284))
end
| uu____9286 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____9287 = (strip_quotes term1)
in NameContainsStr (uu____9287))
end
| uu____9288 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____9290 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____9290) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9293 = (

let uu____9294 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____9294))
in (FStar_Exn.raise uu____9293))
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

let uu____9316 = (match (term.st_term) with
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
| uu____9319 -> begin
""
end) uu____9316)))
in (

let results = (FStar_All.try_with (fun uu___115_9340 -> (match (()) with
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

let uu____9385 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____9385))
in (

let uu____9388 = (

let uu____9389 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____9389))
in (FStar_Exn.raise uu____9388)))
end
| uu____9394 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___114_9399 -> (match (uu___114_9399) with
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
| Push ({push_kind = SyntaxCheck; push_code = uu____9492; push_line = uu____9493; push_column = uu____9494; push_peek_only = false}) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____9495 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = GenericError ("Current module unset"); qid = q.qid}
end
| uu____9496 -> begin
q
end)
end))


let validate_and_run_query : repl_state  ->  query  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let query1 = (validate_query st query)
in ((FStar_ST.op_Colon_Equals repl_current_qid (FStar_Pervasives_Native.Some (query1.qid)));
(run_query st query1.qq);
)))


let js_repl_eval : repl_state  ->  query  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let uu____9572 = (validate_and_run_query st query)
in (match (uu____9572) with
| ((status, response), st_opt) -> begin
(

let js_response = (json_of_response query.qid status response)
in ((js_response), (st_opt)))
end)))


let js_repl_eval_js : repl_state  ->  FStar_Util.json  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query_js -> (

let uu____9631 = (deserialize_interactive_query query_js)
in (js_repl_eval st uu____9631)))


let js_repl_eval_str : repl_state  ->  Prims.string  ->  (Prims.string * (repl_state, Prims.int) FStar_Util.either) = (fun st query_str -> (

let uu____9650 = (

let uu____9659 = (parse_interactive_query query_str)
in (js_repl_eval st uu____9659))
in (match (uu____9650) with
| (js_response, st_opt) -> begin
(

let uu____9678 = (FStar_Util.string_of_json js_response)
in ((uu____9678), (st_opt)))
end)))


let js_repl_init_opts : unit  ->  unit = (fun uu____9687 -> (

let uu____9688 = (FStar_Options.parse_cmd_line ())
in (match (uu____9688) with
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
| (h)::(uu____9703)::uu____9704 -> begin
(failwith "repl_init: Too many file names given in --ide invocation")
end
| uu____9707 -> begin
()
end)
end)
end)))


let rec go : repl_state  ->  Prims.int = (fun st -> (

let query = (read_interactive_query st.repl_stdin)
in (

let uu____9716 = (validate_and_run_query st query)
in (match (uu____9716) with
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

let uu____9760 = (

let uu____9763 = (FStar_ST.op_Bang issues)
in (e)::uu____9763)
in (FStar_ST.op_Colon_Equals issues uu____9760)))
in (

let count_errors = (fun uu____9977 -> (

let uu____9978 = (

let uu____9981 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____9981))
in (FStar_List.length uu____9978)))
in (

let report = (fun uu____10096 -> (

let uu____10097 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____10097)))
in (

let clear1 = (fun uu____10208 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : (FStar_Util.json  ->  unit)  ->  FStar_Util.printer = (fun printer -> {FStar_Util.printer_prinfo = (fun s -> (forward_message printer "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (forward_message printer "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (forward_message printer "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label get_string get_json -> (

let uu____10344 = (get_json ())
in (forward_message printer label uu____10344)))})


let install_ide_mode_hooks : (FStar_Util.json  ->  unit)  ->  unit = (fun printer -> ((FStar_Util.set_printer (interactive_printer printer));
(FStar_Errors.set_handler interactive_error_handler);
))


let initial_range : FStar_Range.range = (

let uu____10356 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____10357 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____10356 uu____10357)))


let build_initial_repl_state : Prims.string  ->  repl_state = (fun filename -> (

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env initial_range)
in (

let uu____10365 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_deps_stack = []; repl_curmod = FStar_Pervasives_Native.None; repl_env = env1; repl_stdin = uu____10365; repl_names = FStar_Interactive_CompletionTable.empty}))))


let interactive_mode' : 'Auu____10374 . repl_state  ->  'Auu____10374 = (fun init_st -> ((write_hello ());
(

let exit_code = (

let uu____10382 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____10382) with
| true -> begin
(

let uu____10383 = (

let uu____10384 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10384))
in (FStar_SMTEncoding_Solver.with_hints_db uu____10383 (fun uu____10388 -> (go init_st))))
end
| uu____10389 -> begin
(go init_st)
end))
in (FStar_All.exit exit_code));
))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((install_ide_mode_hooks write_json);
(

let uu____10397 = (

let uu____10398 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____10398))
in (match (uu____10397) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("--ide: ignoring --codegen")))
end
| uu____10401 -> begin
()
end));
(

let init1 = (build_initial_repl_state filename)
in (

let uu____10403 = (FStar_Options.trace_error ())
in (match (uu____10403) with
| true -> begin
(interactive_mode' init1)
end
| uu____10404 -> begin
(FStar_All.try_with (fun uu___117_10406 -> (match (()) with
| () -> begin
(interactive_mode' init1)
end)) (fun uu___116_10410 -> (match (uu___116_10410) with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise e);
)
end)))
end)));
))




