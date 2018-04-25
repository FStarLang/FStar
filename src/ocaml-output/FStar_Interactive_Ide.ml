
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


let with_captured_errors' : 'Auu____62 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____62 FStar_Pervasives_Native.option)  ->  'Auu____62 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (FStar_All.try_with (fun uu___93_92 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler sigint_handler (fun uu____98 -> (f env)))
end)) (fun uu___92_103 -> (match (uu___92_103) with
| FStar_All.Failure (msg) -> begin
(

let msg1 = (Prims.strcat "ASSERTION FAILURE: " (Prims.strcat msg (Prims.strcat "\n" (Prims.strcat "F* may be in an inconsistent state.\n" (Prims.strcat "Please file a bug report, ideally with a " "minimized version of the program that triggered the error.")))))
in ((

let uu____109 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.log_issue uu____109 ((FStar_Errors.Error_IDEAssertionFailure), (msg1))));
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

let uu____130 = (

let uu____139 = (

let uu____146 = (FStar_TypeChecker_Env.get_range env)
in ((e), (msg), (uu____146)))
in (uu____139)::[])
in (FStar_TypeChecker_Err.add_errors env uu____130));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Stop -> begin
FStar_Pervasives_Native.None
end))))


let with_captured_errors : 'Auu____167 . FStar_TypeChecker_Env.env  ->  FStar_Util.sigint_handler  ->  (FStar_TypeChecker_Env.env  ->  'Auu____167 FStar_Pervasives_Native.option)  ->  'Auu____167 FStar_Pervasives_Native.option = (fun env sigint_handler f -> (

let uu____194 = (FStar_Options.trace_error ())
in (match (uu____194) with
| true -> begin
(f env)
end
| uu____197 -> begin
(with_captured_errors' env sigint_handler f)
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

let uu____227 = (FStar_Parser_ParseIt.get_file_last_modification_time fname)
in {tf_fname = fname; tf_modtime = uu____227}))


let dummy_tf_of_fname : Prims.string  ->  timed_fname = (fun fname -> {tf_fname = fname; tf_modtime = t0})


let string_of_timed_fname : timed_fname  ->  Prims.string = (fun uu____237 -> (match (uu____237) with
| {tf_fname = fname; tf_modtime = modtime} -> begin
(match ((Prims.op_Equality modtime t0)) with
| true -> begin
(FStar_Util.format1 "{ %s }" fname)
end
| uu____240 -> begin
(

let uu____241 = (FStar_Util.string_of_time modtime)
in (FStar_Util.format2 "{ %s; %s }" fname uu____241))
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
| uu____353 -> begin
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
| uu____379 -> begin
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
| uu____393 -> begin
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
| uu____407 -> begin
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

let uu____734 = (FStar_ST.op_Bang repl_stack)
in (match (uu____734) with
| [] -> begin
(failwith "Too many pops")
end
| ((uu____786, st'))::stack -> begin
((pop st.repl_env "REPL pop_repl");
(FStar_ST.op_Colon_Equals repl_stack stack);
st';
)
end)))


let push_repl : push_kind  ->  repl_task  ->  repl_state  ->  FStar_TypeChecker_Env.env = (fun push_kind task st -> ((

let uu____858 = (

let uu____865 = (FStar_ST.op_Bang repl_stack)
in (((task), (st)))::uu____865)
in (FStar_ST.op_Colon_Equals repl_stack uu____858));
(

let uu____958 = (set_check_kind st.repl_env push_kind)
in (push uu____958 "REPL push_repl"));
))


let nothing_left_to_pop : repl_state  ->  Prims.bool = (fun st -> (

let uu____964 = (

let uu____965 = (FStar_ST.op_Bang repl_stack)
in (FStar_List.length uu____965))
in (Prims.op_Equality uu____964 (FStar_List.length st.repl_deps_stack))))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of FStar_TypeChecker_Env.binding


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____1071 -> begin
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
| uu____1107 -> begin
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
| uu____1137 -> begin
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
| uu____1163 -> begin
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

let uu____1209 = (FStar_Ident.text_of_id id1)
in (

let uu____1210 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table uu____1209 [] uu____1210)))
end
| uu____1211 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1219 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_Syntax_DsEnv.Open_module) [] uu____1219))
end
| uu____1220 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____1223 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____1224 -> begin
(query_of_lid host)
end)
in (

let uu____1225 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____1223 uu____1225)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_TypeChecker_Env.Binding_lid (lid, uu____1233) -> begin
(lid)::[]
end
| FStar_TypeChecker_Env.Binding_sig (lids, uu____1235) -> begin
lids
end
| FStar_TypeChecker_Env.Binding_sig_inst (lids, uu____1241, uu____1242) -> begin
lids
end
| uu____1247 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____1259 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (

let uu____1260 = (FStar_Ident.text_of_id lid.FStar_Ident.ident)
in (FStar_Interactive_CompletionTable.insert tbl ns_query uu____1260 lid)))) table lids))
end)))


let commit_name_tracking' : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____1286 = (FStar_Syntax_Syntax.mod_name md)
in uu____1286.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let commit_name_tracking : repl_state  ->  name_tracking_event Prims.list  ->  repl_state = (fun st name_events -> (

let names1 = (commit_name_tracking' st.repl_curmod st.repl_names name_events)
in (

let uu___94_1311 = st
in {repl_line = uu___94_1311.repl_line; repl_column = uu___94_1311.repl_column; repl_fname = uu___94_1311.repl_fname; repl_deps_stack = uu___94_1311.repl_deps_stack; repl_curmod = uu___94_1311.repl_curmod; repl_env = uu___94_1311.repl_env; repl_stdin = uu___94_1311.repl_stdin; repl_names = names1})))


let fresh_name_tracking_hooks : unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____1326 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____1340 = (

let uu____1343 = (FStar_ST.op_Bang events)
in (evt)::uu____1343)
in (FStar_ST.op_Colon_Equals events uu____1340)))
in ((events), ({FStar_Syntax_DsEnv.ds_push_open_hook = (fun dsenv1 op -> (

let uu____1634 = (

let uu____1635 = (

let uu____1640 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1640), (op)))
in NTOpen (uu____1635))
in (push_event uu____1634))); FStar_Syntax_DsEnv.ds_push_include_hook = (fun dsenv1 ns -> (

let uu____1646 = (

let uu____1647 = (

let uu____1652 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1652), (ns)))
in NTInclude (uu____1647))
in (push_event uu____1646))); FStar_Syntax_DsEnv.ds_push_module_abbrev_hook = (fun dsenv1 x l -> (

let uu____1660 = (

let uu____1661 = (

let uu____1668 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1668), (x), (l)))
in NTAlias (uu____1661))
in (push_event uu____1660)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____1673 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : env_t  ->  (env_t * (env_t  ->  (env_t * name_tracking_event Prims.list))) = (fun env -> (

let set_hooks = (fun dshooks tchooks env1 -> (

let uu____1722 = (FStar_Universal.with_tcenv env1 (fun dsenv1 -> (

let uu____1730 = (FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks)
in ((()), (uu____1730)))))
in (match (uu____1722) with
| ((), tcenv') -> begin
(FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks)
end)))
in (

let uu____1732 = (

let uu____1737 = (FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv)
in (

let uu____1738 = (FStar_TypeChecker_Env.tc_hooks env)
in ((uu____1737), (uu____1738))))
in (match (uu____1732) with
| (old_dshooks, old_tchooks) -> begin
(

let uu____1754 = (fresh_name_tracking_hooks ())
in (match (uu____1754) with
| (events, new_dshooks, new_tchooks) -> begin
(

let uu____1789 = (set_hooks new_dshooks new_tchooks env)
in ((uu____1789), ((fun env1 -> (

let uu____1803 = (set_hooks old_dshooks old_tchooks env1)
in (

let uu____1804 = (

let uu____1807 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____1807))
in ((uu____1803), (uu____1804))))))))
end))
end))))


let string_of_repl_task : repl_task  ->  Prims.string = (fun uu___76_1919 -> (match (uu___76_1919) with
| LDInterleaved (intf, impl) -> begin
(

let uu____1922 = (string_of_timed_fname intf)
in (

let uu____1923 = (string_of_timed_fname impl)
in (FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1922 uu____1923)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____1925 = (string_of_timed_fname intf_or_impl)
in (FStar_Util.format1 "LDSingle %s" uu____1925))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1927 = (string_of_timed_fname intf)
in (FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1927))
end
| PushFragment (frag) -> begin
(FStar_Util.format1 "PushFragment { code = %s }" frag.FStar_Parser_ParseIt.frag_text)
end))


let tc_one : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env intf_opt modf -> (

let uu____1948 = (FStar_Universal.tc_one_file env FStar_Pervasives_Native.None intf_opt modf)
in (match (uu____1948) with
| (uu____1962, env1, delta1) -> begin
(

let env2 = (FStar_Universal.apply_delta_env env1 delta1)
in env2)
end)))


let run_repl_task : optmod_t  ->  env_t  ->  repl_task  ->  (optmod_t * env_t) = (fun curmod env task -> (match (task) with
| LDInterleaved (intf, impl) -> begin
(

let uu____2001 = (tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname)) impl.tf_fname)
in ((curmod), (uu____2001)))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____2003 = (tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname)
in ((curmod), (uu____2003)))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____2005 = (FStar_Universal.load_interface_decls env intf.tf_fname)
in ((curmod), (uu____2005)))
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

let uu____2060 = (aux deps' final_tasks1)
in (LDInterleaved ((((wrap intf)), ((wrap impl)))))::uu____2060)
end
| (intf_or_impl)::deps' -> begin
(

let uu____2067 = (aux deps' final_tasks1)
in (LDSingle ((wrap intf_or_impl)))::uu____2067)
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

let uu____2108 = (get_mod_name f)
in (Prims.op_Equality uu____2108 our_mod_name)))
in (

let uu____2109 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]))
in (match (uu____2109) with
| (deps, dep_graph1) -> begin
(

let uu____2132 = (FStar_List.partition has_our_mod_name deps)
in (match (uu____2132) with
| (same_name, real_deps) -> begin
(

let intf_tasks = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____2169 = (

let uu____2170 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____2170)))
in (match (uu____2169) with
| true -> begin
(

let uu____2171 = (

let uu____2176 = (FStar_Util.format1 "Expecting an interface, got %s" intf)
in ((FStar_Errors.Fatal_MissingInterface), (uu____2176)))
in (FStar_Errors.raise_err uu____2171))
end
| uu____2177 -> begin
()
end));
(

let uu____2179 = (

let uu____2180 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____2180)))
in (match (uu____2179) with
| true -> begin
(

let uu____2181 = (

let uu____2186 = (FStar_Util.format1 "Expecting an implementation, got %s" impl)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2186)))
in (FStar_Errors.raise_err uu____2181))
end
| uu____2187 -> begin
()
end));
(LDInterfaceOfCurrentFile ((dummy_tf_of_fname intf)))::[];
)
end
| (impl)::[] -> begin
[]
end
| uu____2189 -> begin
(

let mods_str = (FStar_String.concat " " same_name)
in (

let message = "Too many or too few files matching %s: %s"
in ((

let uu____2195 = (

let uu____2200 = (FStar_Util.format message ((our_mod_name)::(mods_str)::[]))
in ((FStar_Errors.Fatal_TooManyOrTooFewFileMatch), (uu____2200)))
in (FStar_Errors.raise_err uu____2195));
[];
)))
end)
in (

let tasks = (repl_ld_tasks_of_deps real_deps intf_tasks)
in ((real_deps), (tasks), (dep_graph1))))
end))
end))))))


let update_task_timestamps : repl_task  ->  repl_task = (fun uu___77_2212 -> (match (uu___77_2212) with
| LDInterleaved (intf, impl) -> begin
(

let uu____2215 = (

let uu____2220 = (tf_of_fname intf.tf_fname)
in (

let uu____2221 = (tf_of_fname impl.tf_fname)
in ((uu____2220), (uu____2221))))
in LDInterleaved (uu____2215))
end
| LDSingle (intf_or_impl) -> begin
(

let uu____2223 = (tf_of_fname intf_or_impl.tf_fname)
in LDSingle (uu____2223))
end
| LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____2225 = (tf_of_fname intf.tf_fname)
in LDInterfaceOfCurrentFile (uu____2225))
end
| PushFragment (frag) -> begin
PushFragment (frag)
end))


let run_repl_transaction : repl_state  ->  push_kind  ->  Prims.bool  ->  repl_task  ->  (Prims.bool * repl_state) = (fun st push_kind must_rollback task -> (

let env = (push_repl push_kind task st)
in (

let uu____2252 = (track_name_changes env)
in (match (uu____2252) with
| (env1, finish_name_tracking) -> begin
(

let check_success = (fun uu____2295 -> ((

let uu____2298 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2298 (Prims.parse_int "0"))) && (not (must_rollback))))
in (

let sigint_handler = (match (task) with
| PushFragment (uu____2300) -> begin
FStar_Util.sigint_raise
end
| uu____2301 -> begin
FStar_Util.sigint_ignore
end)
in (

let uu____2302 = (

let uu____2309 = (with_captured_errors env1 sigint_handler (fun env2 -> (

let uu____2323 = (run_repl_task st.repl_curmod env2 task)
in (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) uu____2323))))
in (match (uu____2309) with
| FStar_Pervasives_Native.Some (curmod, env2) when (check_success ()) -> begin
((curmod), (env2), (true))
end
| uu____2354 -> begin
((st.repl_curmod), (env1), (false))
end))
in (match (uu____2302) with
| (curmod, env2, success) -> begin
(

let uu____2368 = (finish_name_tracking env2)
in (match (uu____2368) with
| (env', name_events) -> begin
(

let st1 = (

let uu___95_2386 = st
in {repl_line = uu___95_2386.repl_line; repl_column = uu___95_2386.repl_column; repl_fname = uu___95_2386.repl_fname; repl_deps_stack = uu___95_2386.repl_deps_stack; repl_curmod = curmod; repl_env = env2; repl_stdin = uu___95_2386.repl_stdin; repl_names = uu___95_2386.repl_names})
in (

let st2 = (match (success) with
| true -> begin
(commit_name_tracking st1 name_events)
end
| uu____2388 -> begin
(pop_repl st1)
end)
in ((success), (st2))))
end))
end))))
end))))


let run_repl_ld_transactions : repl_state  ->  repl_task Prims.list  ->  (repl_task  ->  unit)  ->  (repl_state, repl_state) FStar_Util.either = (fun st tasks progress_callback -> (

let debug1 = (fun verb task -> (

let uu____2428 = (FStar_Options.debug_any ())
in (match (uu____2428) with
| true -> begin
(

let uu____2429 = (string_of_repl_task task)
in (FStar_Util.print2 "%s %s" verb uu____2429))
end
| uu____2430 -> begin
()
end)))
in (

let rec revert_many = (fun st1 uu___78_2447 -> (match (uu___78_2447) with
| [] -> begin
st1
end
| ((task, _st'))::entries -> begin
((debug1 "Reverting" task);
(

let uu____2474 = (pop_repl st1)
in (revert_many uu____2474 entries));
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

let uu____2526 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____2526 (fun a240 -> ())));
(

let timestamped_task = (update_task_timestamps task)
in (

let push_kind = (

let uu____2529 = (FStar_Options.lax ())
in (match (uu____2529) with
| true -> begin
LaxCheck
end
| uu____2530 -> begin
FullCheck
end))
in (

let uu____2531 = (run_repl_transaction st1 push_kind false timestamped_task)
in (match (uu____2531) with
| (success, st2) -> begin
(match (success) with
| true -> begin
(

let uu____2546 = (

let uu___96_2547 = st2
in (

let uu____2548 = (FStar_ST.op_Bang repl_stack)
in {repl_line = uu___96_2547.repl_line; repl_column = uu___96_2547.repl_column; repl_fname = uu___96_2547.repl_fname; repl_deps_stack = uu____2548; repl_curmod = uu___96_2547.repl_curmod; repl_env = uu___96_2547.repl_env; repl_stdin = uu___96_2547.repl_stdin; repl_names = uu___96_2547.repl_names}))
in (aux uu____2546 tasks2 []))
end
| uu____2596 -> begin
FStar_Util.Inr (st2)
end)
end))));
)
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____2609 = (update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst prev) uu____2609)) -> begin
((debug1 "Skipping" task);
(aux st1 tasks2 previous1);
)
end
| (tasks2, previous1) -> begin
(

let uu____2621 = (revert_many st1 previous1)
in (aux uu____2621 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.repl_deps_stack))))))


let json_debug : FStar_Util.json  ->  Prims.string = (fun uu___79_2630 -> (match (uu___79_2630) with
| FStar_Util.JsonNull -> begin
"null"
end
| FStar_Util.JsonBool (b) -> begin
(FStar_Util.format1 "bool (%s)" (match (b) with
| true -> begin
"true"
end
| uu____2632 -> begin
"false"
end))
end
| FStar_Util.JsonInt (i) -> begin
(

let uu____2634 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 "int (%s)" uu____2634))
end
| FStar_Util.JsonStr (s) -> begin
(FStar_Util.format1 "string (%s)" s)
end
| FStar_Util.JsonList (uu____2636) -> begin
"list (...)"
end
| FStar_Util.JsonAssoc (uu____2639) -> begin
"dictionary (...)"
end))

exception UnexpectedJsonType of ((Prims.string * FStar_Util.json))


let uu___is_UnexpectedJsonType : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2659) -> begin
true
end
| uu____2664 -> begin
false
end))


let __proj__UnexpectedJsonType__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Util.json) = (fun projectee -> (match (projectee) with
| UnexpectedJsonType (uu____2679) -> begin
uu____2679
end))


let js_fail : 'Auu____2690 . Prims.string  ->  FStar_Util.json  ->  'Auu____2690 = (fun expected got -> (FStar_Exn.raise (UnexpectedJsonType (((expected), (got))))))


let js_int : FStar_Util.json  ->  Prims.int = (fun uu___80_2705 -> (match (uu___80_2705) with
| FStar_Util.JsonInt (i) -> begin
i
end
| other -> begin
(js_fail "int" other)
end))


let js_str : FStar_Util.json  ->  Prims.string = (fun uu___81_2712 -> (match (uu___81_2712) with
| FStar_Util.JsonStr (s) -> begin
s
end
| other -> begin
(js_fail "string" other)
end))


let js_list : 'Auu____2721 . (FStar_Util.json  ->  'Auu____2721)  ->  FStar_Util.json  ->  'Auu____2721 Prims.list = (fun k uu___82_2736 -> (match (uu___82_2736) with
| FStar_Util.JsonList (l) -> begin
(FStar_List.map k l)
end
| other -> begin
(js_fail "list" other)
end))


let js_assoc : FStar_Util.json  ->  (Prims.string * FStar_Util.json) Prims.list = (fun uu___83_2755 -> (match (uu___83_2755) with
| FStar_Util.JsonAssoc (a) -> begin
a
end
| other -> begin
(js_fail "dictionary" other)
end))


let js_pushkind : FStar_Util.json  ->  push_kind = (fun s -> (

let uu____2781 = (js_str s)
in (match (uu____2781) with
| "syntax" -> begin
SyntaxCheck
end
| "lax" -> begin
LaxCheck
end
| "full" -> begin
FullCheck
end
| uu____2782 -> begin
(js_fail "push_kind" s)
end)))


let js_reductionrule : FStar_Util.json  ->  FStar_TypeChecker_Normalize.step = (fun s -> (

let uu____2788 = (js_str s)
in (match (uu____2788) with
| "beta" -> begin
FStar_TypeChecker_Normalize.Beta
end
| "delta" -> begin
FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant)
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
| uu____2789 -> begin
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
| uu____2809 -> begin
false
end))


let uu___is_CKOption : completion_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CKOption (_0) -> begin
true
end
| uu____2816 -> begin
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
| uu____2834 -> begin
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

let uu____2864 = (js_str k1)
in (match (uu____2864) with
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
| uu____2865 -> begin
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
| uu____2871 -> begin
false
end))


let uu___is_LKModule : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKModule -> begin
true
end
| uu____2877 -> begin
false
end))


let uu___is_LKOption : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKOption -> begin
true
end
| uu____2883 -> begin
false
end))


let uu___is_LKCode : lookup_context  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LKCode -> begin
true
end
| uu____2889 -> begin
false
end))


let js_optional_lookup_context : FStar_Util.json FStar_Pervasives_Native.option  ->  lookup_context = (fun k -> (match (k) with
| FStar_Pervasives_Native.None -> begin
LKSymbolOnly
end
| FStar_Pervasives_Native.Some (k1) -> begin
(

let uu____2900 = (js_str k1)
in (match (uu____2900) with
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
| uu____2901 -> begin
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
| uu____2998 -> begin
false
end))


let uu___is_DescribeProtocol : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeProtocol -> begin
true
end
| uu____3004 -> begin
false
end))


let uu___is_DescribeRepl : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DescribeRepl -> begin
true
end
| uu____3010 -> begin
false
end))


let uu___is_Segment : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Segment (_0) -> begin
true
end
| uu____3017 -> begin
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
| uu____3030 -> begin
false
end))


let uu___is_Push : query'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____3037 -> begin
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
| uu____3057 -> begin
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
| uu____3093 -> begin
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
| uu____3131 -> begin
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
| uu____3189 -> begin
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
| uu____3227 -> begin
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
| uu____3241 -> begin
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
| uu____3255 -> begin
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


let query_needs_current_module : query'  ->  Prims.bool = (fun uu___84_3281 -> (match (uu___84_3281) with
| Exit -> begin
false
end
| DescribeProtocol -> begin
false
end
| DescribeRepl -> begin
false
end
| Segment (uu____3282) -> begin
false
end
| Pop -> begin
false
end
| Push ({push_kind = uu____3283; push_code = uu____3284; push_line = uu____3285; push_column = uu____3286; push_peek_only = false}) -> begin
false
end
| VfsAdd (uu____3287) -> begin
false
end
| GenericError (uu____3294) -> begin
false
end
| ProtocolViolation (uu____3295) -> begin
false
end
| Push (uu____3296) -> begin
true
end
| AutoComplete (uu____3297) -> begin
true
end
| Lookup (uu____3302) -> begin
true
end
| Compute (uu____3315) -> begin
true
end
| Search (uu____3324) -> begin
true
end))


let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2")


let interactive_protocol_features : Prims.string Prims.list = ("autocomplete")::("autocomplete/context")::("compute")::("compute/reify")::("compute/pure-subterms")::("describe-protocol")::("describe-repl")::("exit")::("lookup")::("lookup/context")::("lookup/documentation")::("lookup/definition")::("peek")::("pop")::("push")::("search")::("segment")::("vfs-add")::("tactic-ranges")::("interrupt")::("progress")::[]

exception InvalidQuery of (Prims.string)


let uu___is_InvalidQuery : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3336) -> begin
true
end
| uu____3337 -> begin
false
end))


let __proj__InvalidQuery__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidQuery (uu____3344) -> begin
uu____3344
end))

type query_status =
| QueryOK
| QueryNOK
| QueryViolatesProtocol


let uu___is_QueryOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryOK -> begin
true
end
| uu____3350 -> begin
false
end))


let uu___is_QueryNOK : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryNOK -> begin
true
end
| uu____3356 -> begin
false
end))


let uu___is_QueryViolatesProtocol : query_status  ->  Prims.bool = (fun projectee -> (match (projectee) with
| QueryViolatesProtocol -> begin
true
end
| uu____3362 -> begin
false
end))


let try_assoc : 'Auu____3371 'Auu____3372 . 'Auu____3371  ->  ('Auu____3371 * 'Auu____3372) Prims.list  ->  'Auu____3372 FStar_Pervasives_Native.option = (fun key a -> (

let uu____3397 = (FStar_Util.try_find (fun uu____3411 -> (match (uu____3411) with
| (k, uu____3417) -> begin
(Prims.op_Equality k key)
end)) a)
in (FStar_Util.map_option FStar_Pervasives_Native.snd uu____3397)))


let wrap_js_failure : Prims.string  ->  Prims.string  ->  FStar_Util.json  ->  query = (fun qid expected got -> (

let uu____3437 = (

let uu____3438 = (

let uu____3439 = (json_debug got)
in (FStar_Util.format2 "JSON decoding failed: expected %s, got %s" expected uu____3439))
in ProtocolViolation (uu____3438))
in {qq = uu____3437; qid = qid}))


let unpack_interactive_query : FStar_Util.json  ->  query = (fun json -> (

let assoc1 = (fun errloc key a -> (

let uu____3473 = (try_assoc key a)
in (match (uu____3473) with
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3477 = (

let uu____3478 = (FStar_Util.format2 "Missing key [%s] in %s." key errloc)
in InvalidQuery (uu____3478))
in (FStar_Exn.raise uu____3477))
end)))
in (

let request = (FStar_All.pipe_right json js_assoc)
in (

let qid = (

let uu____3493 = (assoc1 "query" "query-id" request)
in (FStar_All.pipe_right uu____3493 js_str))
in (FStar_All.try_with (fun uu___98_3500 -> (match (()) with
| () -> begin
(

let query = (

let uu____3502 = (assoc1 "query" "query" request)
in (FStar_All.pipe_right uu____3502 js_str))
in (

let args = (

let uu____3510 = (assoc1 "query" "args" request)
in (FStar_All.pipe_right uu____3510 js_assoc))
in (

let arg = (fun k -> (assoc1 "[args]" k args))
in (

let try_arg = (fun k -> (

let uu____3531 = (try_assoc k args)
in (match (uu____3531) with
| FStar_Pervasives_Native.Some (FStar_Util.JsonNull) -> begin
FStar_Pervasives_Native.None
end
| other -> begin
other
end)))
in (

let uu____3539 = (match (query) with
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

let uu____3540 = (

let uu____3541 = (arg "code")
in (FStar_All.pipe_right uu____3541 js_str))
in Segment (uu____3540))
end
| "peek" -> begin
(

let uu____3542 = (

let uu____3543 = (

let uu____3544 = (arg "kind")
in (FStar_All.pipe_right uu____3544 js_pushkind))
in (

let uu____3545 = (

let uu____3546 = (arg "code")
in (FStar_All.pipe_right uu____3546 js_str))
in (

let uu____3547 = (

let uu____3548 = (arg "line")
in (FStar_All.pipe_right uu____3548 js_int))
in (

let uu____3549 = (

let uu____3550 = (arg "column")
in (FStar_All.pipe_right uu____3550 js_int))
in {push_kind = uu____3543; push_code = uu____3545; push_line = uu____3547; push_column = uu____3549; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3542))
end
| "push" -> begin
(

let uu____3551 = (

let uu____3552 = (

let uu____3553 = (arg "kind")
in (FStar_All.pipe_right uu____3553 js_pushkind))
in (

let uu____3554 = (

let uu____3555 = (arg "code")
in (FStar_All.pipe_right uu____3555 js_str))
in (

let uu____3556 = (

let uu____3557 = (arg "line")
in (FStar_All.pipe_right uu____3557 js_int))
in (

let uu____3558 = (

let uu____3559 = (arg "column")
in (FStar_All.pipe_right uu____3559 js_int))
in {push_kind = uu____3552; push_code = uu____3554; push_line = uu____3556; push_column = uu____3558; push_peek_only = (Prims.op_Equality query "peek")}))))
in Push (uu____3551))
end
| "autocomplete" -> begin
(

let uu____3560 = (

let uu____3565 = (

let uu____3566 = (arg "partial-symbol")
in (FStar_All.pipe_right uu____3566 js_str))
in (

let uu____3567 = (

let uu____3568 = (try_arg "context")
in (FStar_All.pipe_right uu____3568 js_optional_completion_context))
in ((uu____3565), (uu____3567))))
in AutoComplete (uu____3560))
end
| "lookup" -> begin
(

let uu____3573 = (

let uu____3586 = (

let uu____3587 = (arg "symbol")
in (FStar_All.pipe_right uu____3587 js_str))
in (

let uu____3588 = (

let uu____3589 = (try_arg "context")
in (FStar_All.pipe_right uu____3589 js_optional_lookup_context))
in (

let uu____3594 = (

let uu____3603 = (

let uu____3612 = (try_arg "location")
in (FStar_All.pipe_right uu____3612 (FStar_Util.map_option js_assoc)))
in (FStar_All.pipe_right uu____3603 (FStar_Util.map_option (fun loc -> (

let uu____3670 = (

let uu____3671 = (assoc1 "[location]" "filename" loc)
in (FStar_All.pipe_right uu____3671 js_str))
in (

let uu____3672 = (

let uu____3673 = (assoc1 "[location]" "line" loc)
in (FStar_All.pipe_right uu____3673 js_int))
in (

let uu____3674 = (

let uu____3675 = (assoc1 "[location]" "column" loc)
in (FStar_All.pipe_right uu____3675 js_int))
in ((uu____3670), (uu____3672), (uu____3674)))))))))
in (

let uu____3676 = (

let uu____3679 = (arg "requested-info")
in (FStar_All.pipe_right uu____3679 (js_list js_str)))
in ((uu____3586), (uu____3588), (uu____3594), (uu____3676))))))
in Lookup (uu____3573))
end
| "compute" -> begin
(

let uu____3692 = (

let uu____3701 = (

let uu____3702 = (arg "term")
in (FStar_All.pipe_right uu____3702 js_str))
in (

let uu____3703 = (

let uu____3708 = (try_arg "rules")
in (FStar_All.pipe_right uu____3708 (FStar_Util.map_option (js_list js_reductionrule))))
in ((uu____3701), (uu____3703))))
in Compute (uu____3692))
end
| "search" -> begin
(

let uu____3723 = (

let uu____3724 = (arg "terms")
in (FStar_All.pipe_right uu____3724 js_str))
in Search (uu____3723))
end
| "vfs-add" -> begin
(

let uu____3725 = (

let uu____3732 = (

let uu____3735 = (try_arg "filename")
in (FStar_All.pipe_right uu____3735 (FStar_Util.map_option js_str)))
in (

let uu____3742 = (

let uu____3743 = (arg "contents")
in (FStar_All.pipe_right uu____3743 js_str))
in ((uu____3732), (uu____3742))))
in VfsAdd (uu____3725))
end
| uu____3746 -> begin
(

let uu____3747 = (FStar_Util.format1 "Unknown query \'%s\'" query)
in ProtocolViolation (uu____3747))
end)
in {qq = uu____3539; qid = qid})))))
end)) (fun uu___97_3750 -> (match (uu___97_3750) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = qid}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure qid expected got)
end)))))))


let deserialize_interactive_query : FStar_Util.json  ->  query = (fun js_query -> (FStar_All.try_with (fun uu___100_3760 -> (match (()) with
| () -> begin
(unpack_interactive_query js_query)
end)) (fun uu___99_3763 -> (match (uu___99_3763) with
| InvalidQuery (msg) -> begin
{qq = ProtocolViolation (msg); qid = "?"}
end
| UnexpectedJsonType (expected, got) -> begin
(wrap_js_failure "?" expected got)
end))))


let parse_interactive_query : Prims.string  ->  query = (fun query_str -> (

let uu____3772 = (FStar_Util.json_of_string query_str)
in (match (uu____3772) with
| FStar_Pervasives_Native.None -> begin
{qq = ProtocolViolation ("Json parsing failed."); qid = "?"}
end
| FStar_Pervasives_Native.Some (request) -> begin
(deserialize_interactive_query request)
end)))


let read_interactive_query : FStar_Util.stream_reader  ->  query = (fun stream -> (

let uu____3781 = (FStar_Util.read_line stream)
in (match (uu____3781) with
| FStar_Pervasives_Native.None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| FStar_Pervasives_Native.Some (line) -> begin
(parse_interactive_query line)
end)))


let json_of_opt : 'Auu____3791 . ('Auu____3791  ->  FStar_Util.json)  ->  'Auu____3791 FStar_Pervasives_Native.option  ->  FStar_Util.json = (fun json_of_a opt_a -> (

let uu____3811 = (FStar_Util.map_option json_of_a opt_a)
in (FStar_Util.dflt FStar_Util.JsonNull uu____3811)))


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

let uu____3824 = (

let uu____3831 = (

let uu____3838 = (

let uu____3845 = (

let uu____3850 = (

let uu____3851 = (

let uu____3854 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3860 = (FStar_Range.json_of_use_range r)
in (uu____3860)::[])
end)
in (

let uu____3861 = (match (issue.FStar_Errors.issue_range) with
| FStar_Pervasives_Native.Some (r) when (

let uu____3867 = (FStar_Range.def_range r)
in (

let uu____3868 = (FStar_Range.use_range r)
in (Prims.op_disEquality uu____3867 uu____3868))) -> begin
(

let uu____3869 = (FStar_Range.json_of_def_range r)
in (uu____3869)::[])
end
| uu____3870 -> begin
[]
end)
in (FStar_List.append uu____3854 uu____3861)))
in FStar_Util.JsonList (uu____3851))
in (("ranges"), (uu____3850)))
in (uu____3845)::[])
in ((("message"), (FStar_Util.JsonStr (issue.FStar_Errors.issue_message))))::uu____3838)
in ((("level"), ((json_of_issue_level issue.FStar_Errors.issue_level))))::uu____3831)
in FStar_Util.JsonAssoc (uu____3824)))

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

let uu____4039 = (

let uu____4046 = (

let uu____4051 = (json_of_opt FStar_Range.json_of_def_range lr.slr_def_range)
in (("defined-at"), (uu____4051)))
in (

let uu____4052 = (

let uu____4059 = (

let uu____4064 = (json_of_opt (fun _0_18 -> FStar_Util.JsonStr (_0_18)) lr.slr_typ)
in (("type"), (uu____4064)))
in (

let uu____4065 = (

let uu____4072 = (

let uu____4077 = (json_of_opt (fun _0_19 -> FStar_Util.JsonStr (_0_19)) lr.slr_doc)
in (("documentation"), (uu____4077)))
in (

let uu____4078 = (

let uu____4085 = (

let uu____4090 = (json_of_opt (fun _0_20 -> FStar_Util.JsonStr (_0_20)) lr.slr_def)
in (("definition"), (uu____4090)))
in (uu____4085)::[])
in (uu____4072)::uu____4078))
in (uu____4059)::uu____4065))
in (uu____4046)::uu____4052))
in ((("name"), (FStar_Util.JsonStr (lr.slr_name))))::uu____4039))


let alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4123 = (FStar_List.map (fun _0_21 -> FStar_Util.JsonStr (_0_21)) interactive_protocol_features)
in (FStar_All.pipe_left (fun _0_22 -> FStar_Util.JsonList (_0_22)) uu____4123))
in ((("version"), (js_version)))::((("features"), (js_features)))::[]))

type fstar_option_permission_level =
| OptSet
| OptReset
| OptReadOnly


let uu___is_OptSet : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptSet -> begin
true
end
| uu____4145 -> begin
false
end))


let uu___is_OptReset : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReset -> begin
true
end
| uu____4151 -> begin
false
end))


let uu___is_OptReadOnly : fstar_option_permission_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| OptReadOnly -> begin
true
end
| uu____4157 -> begin
false
end))


let string_of_option_permission_level : fstar_option_permission_level  ->  Prims.string = (fun uu___85_4162 -> (match (uu___85_4162) with
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


let rec kind_of_fstar_option_type : FStar_Options.opt_type  ->  Prims.string = (fun uu___86_4355 -> (match (uu___86_4355) with
| FStar_Options.Const (uu____4356) -> begin
"flag"
end
| FStar_Options.IntStr (uu____4357) -> begin
"int"
end
| FStar_Options.BoolStr -> begin
"bool"
end
| FStar_Options.PathStr (uu____4358) -> begin
"path"
end
| FStar_Options.SimpleStr (uu____4359) -> begin
"string"
end
| FStar_Options.EnumStr (uu____4360) -> begin
"enum"
end
| FStar_Options.OpenEnumStr (uu____4363) -> begin
"open enum"
end
| FStar_Options.PostProcessed (uu____4370, typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.Accumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.ReverseAccumulated (typ) -> begin
(kind_of_fstar_option_type typ)
end
| FStar_Options.WithSideEffect (uu____4380, typ) -> begin
(kind_of_fstar_option_type typ)
end))


let rec snippets_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string Prims.list = (fun name typ -> (

let mk_field = (fun field_name -> (Prims.strcat "${" (Prims.strcat field_name "}")))
in (

let mk_snippet = (fun name1 argstring -> (Prims.strcat "--" (Prims.strcat name1 (match ((Prims.op_disEquality argstring "")) with
| true -> begin
(Prims.strcat " " argstring)
end
| uu____4417 -> begin
""
end))))
in (

let rec arg_snippets_of_type = (fun typ1 -> (match (typ1) with
| FStar_Options.Const (uu____4428) -> begin
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
| FStar_Options.PostProcessed (uu____4441, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.Accumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.ReverseAccumulated (elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end
| FStar_Options.WithSideEffect (uu____4451, elem_spec) -> begin
(arg_snippets_of_type elem_spec)
end))
in (

let uu____4459 = (arg_snippets_of_type typ)
in (FStar_List.map (mk_snippet name) uu____4459))))))


let rec json_of_fstar_option_value : FStar_Options.option_val  ->  FStar_Util.json = (fun uu___87_4466 -> (match (uu___87_4466) with
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

let uu____4474 = (FStar_List.map json_of_fstar_option_value vs)
in FStar_Util.JsonList (uu____4474))
end
| FStar_Options.Unset -> begin
FStar_Util.JsonNull
end))


let alist_of_fstar_option : fstar_option  ->  (Prims.string * FStar_Util.json) Prims.list = (fun opt -> (

let uu____4488 = (

let uu____4495 = (

let uu____4502 = (

let uu____4507 = (json_of_fstar_option_value opt.opt_value)
in (("value"), (uu____4507)))
in (

let uu____4508 = (

let uu____4515 = (

let uu____4520 = (json_of_fstar_option_value opt.opt_default)
in (("default"), (uu____4520)))
in (

let uu____4521 = (

let uu____4528 = (

let uu____4533 = (json_of_opt (fun _0_23 -> FStar_Util.JsonStr (_0_23)) opt.opt_documentation)
in (("documentation"), (uu____4533)))
in (

let uu____4534 = (

let uu____4541 = (

let uu____4546 = (

let uu____4547 = (kind_of_fstar_option_type opt.opt_type)
in FStar_Util.JsonStr (uu____4547))
in (("type"), (uu____4546)))
in (uu____4541)::((("permission-level"), (FStar_Util.JsonStr ((string_of_option_permission_level opt.opt_permission_level)))))::[])
in (uu____4528)::uu____4534))
in (uu____4515)::uu____4521))
in (uu____4502)::uu____4508))
in ((("signature"), (FStar_Util.JsonStr (opt.opt_sig))))::uu____4495)
in ((("name"), (FStar_Util.JsonStr (opt.opt_name))))::uu____4488))


let json_of_fstar_option : fstar_option  ->  FStar_Util.json = (fun opt -> (

let uu____4585 = (alist_of_fstar_option opt)
in FStar_Util.JsonAssoc (uu____4585)))


let write_json : FStar_Util.json  ->  unit = (fun json -> ((

let uu____4598 = (FStar_Util.string_of_json json)
in (FStar_Util.print_raw uu____4598));
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

let uu____4661 = (

let uu____4668 = (

let uu____4675 = (

let uu____4680 = (

let uu____4681 = (FStar_ST.op_Bang repl_current_qid)
in (json_of_opt (fun _0_24 -> FStar_Util.JsonStr (_0_24)) uu____4681))
in (("query-id"), (uu____4680)))
in (uu____4675)::((("level"), (FStar_Util.JsonStr (level))))::((("contents"), (js_contents)))::[])
in ((("kind"), (FStar_Util.JsonStr ("message"))))::uu____4668)
in FStar_Util.JsonAssoc (uu____4661)))


let forward_message : 'Auu____4745 . (FStar_Util.json  ->  'Auu____4745)  ->  Prims.string  ->  FStar_Util.json  ->  'Auu____4745 = (fun callback level contents -> (

let uu____4766 = (json_of_message level contents)
in (callback uu____4766)))


let json_of_hello : FStar_Util.json = (

let js_version = FStar_Util.JsonInt (interactive_protocol_vernum)
in (

let js_features = (

let uu____4769 = (FStar_List.map (fun _0_25 -> FStar_Util.JsonStr (_0_25)) interactive_protocol_features)
in FStar_Util.JsonList (uu____4769))
in FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr ("protocol-info"))))::alist_of_protocol_info)))


let write_hello : unit  ->  unit = (fun uu____4780 -> (write_json json_of_hello))


let sig_of_fstar_option : Prims.string  ->  FStar_Options.opt_type  ->  Prims.string = (fun name typ -> (

let flag = (Prims.strcat "--" name)
in (

let uu____4792 = (FStar_Options.desc_of_opt_type typ)
in (match (uu____4792) with
| FStar_Pervasives_Native.None -> begin
flag
end
| FStar_Pervasives_Native.Some (arg_sig) -> begin
(Prims.strcat flag (Prims.strcat " " arg_sig))
end))))


let fstar_options_list_cache : fstar_option Prims.list = (

let defaults1 = (FStar_Util.smap_of_list FStar_Options.defaults)
in (

let uu____4801 = (FStar_All.pipe_right FStar_Options.all_specs_with_types (FStar_List.filter_map (fun uu____4830 -> (match (uu____4830) with
| (_shortname, name, typ, doc1) -> begin
(

let uu____4845 = (FStar_Util.smap_try_find defaults1 name)
in (FStar_All.pipe_right uu____4845 (FStar_Util.map_option (fun default_value -> (

let uu____4857 = (sig_of_fstar_option name typ)
in (

let uu____4858 = (snippets_of_fstar_option name typ)
in (

let uu____4861 = (

let uu____4862 = (FStar_Options.settable name)
in (match (uu____4862) with
| true -> begin
OptSet
end
| uu____4863 -> begin
(

let uu____4864 = (FStar_Options.resettable name)
in (match (uu____4864) with
| true -> begin
OptReset
end
| uu____4865 -> begin
OptReadOnly
end))
end))
in {opt_name = name; opt_sig = uu____4857; opt_value = FStar_Options.Unset; opt_default = default_value; opt_type = typ; opt_snippets = uu____4858; opt_documentation = (match ((Prims.op_Equality doc1 "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4868 -> begin
FStar_Pervasives_Native.Some (doc1)
end); opt_permission_level = uu____4861})))))))
end))))
in (FStar_All.pipe_right uu____4801 (FStar_List.sortWith (fun o1 o2 -> (FStar_String.compare (FStar_String.lowercase o1.opt_name) (FStar_String.lowercase o2.opt_name)))))))


let fstar_options_map_cache : fstar_option FStar_Util.smap = (

let cache = (FStar_Util.smap_create (Prims.parse_int "50"))
in ((FStar_List.iter (fun opt -> (FStar_Util.smap_add cache opt.opt_name opt)) fstar_options_list_cache);
cache;
))


let update_option : fstar_option  ->  fstar_option = (fun opt -> (

let uu___101_4890 = opt
in (

let uu____4891 = (FStar_Options.get_option opt.opt_name)
in {opt_name = uu___101_4890.opt_name; opt_sig = uu___101_4890.opt_sig; opt_value = uu____4891; opt_default = uu___101_4890.opt_default; opt_type = uu___101_4890.opt_type; opt_snippets = uu___101_4890.opt_snippets; opt_documentation = uu___101_4890.opt_documentation; opt_permission_level = uu___101_4890.opt_permission_level})))


let current_fstar_options : (fstar_option  ->  Prims.bool)  ->  fstar_option Prims.list = (fun filter1 -> (

let uu____4904 = (FStar_List.filter filter1 fstar_options_list_cache)
in (FStar_List.map update_option uu____4904)))


let trim_option_name : Prims.string  ->  (Prims.string * Prims.string) = (fun opt_name -> (

let opt_prefix = "--"
in (match ((FStar_Util.starts_with opt_name opt_prefix)) with
| true -> begin
(

let uu____4921 = (FStar_Util.substring_from opt_name (FStar_String.length opt_prefix))
in ((opt_prefix), (uu____4921)))
end
| uu____4922 -> begin
((""), (opt_name))
end)))


let json_of_repl_state : repl_state  ->  FStar_Util.json = (fun st -> (

let filenames = (fun uu____4939 -> (match (uu____4939) with
| (task, uu____4947) -> begin
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
| PushFragment (uu____4954) -> begin
[]
end)
end))
in (

let uu____4955 = (

let uu____4962 = (

let uu____4967 = (

let uu____4968 = (

let uu____4971 = (FStar_List.concatMap filenames st.repl_deps_stack)
in (FStar_List.map (fun _0_26 -> FStar_Util.JsonStr (_0_26)) uu____4971))
in FStar_Util.JsonList (uu____4968))
in (("loaded-dependencies"), (uu____4967)))
in (

let uu____4978 = (

let uu____4985 = (

let uu____4990 = (

let uu____4991 = (

let uu____4994 = (current_fstar_options (fun uu____4999 -> true))
in (FStar_List.map json_of_fstar_option uu____4994))
in FStar_Util.JsonList (uu____4991))
in (("options"), (uu____4990)))
in (uu____4985)::[])
in (uu____4962)::uu____4978))
in FStar_Util.JsonAssoc (uu____4955))))


let with_printed_effect_args : 'Auu____5016 . (unit  ->  'Auu____5016)  ->  'Auu____5016 = (fun k -> (FStar_Options.with_saved_options (fun uu____5029 -> ((FStar_Options.set_option "print_effect_args" (FStar_Options.Bool (true)));
(k ());
))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun tcenv t -> (with_printed_effect_args (fun uu____5042 -> (FStar_TypeChecker_Normalize.term_to_string tcenv t))))


let sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun se -> (with_printed_effect_args (fun uu____5049 -> (FStar_Syntax_Print.sigelt_to_string se))))


let run_exit : 'Auu____5056 'Auu____5057 . 'Auu____5056  ->  ((query_status * FStar_Util.json) * ('Auu____5057, Prims.int) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inr ((Prims.parse_int "0")))))


let run_describe_protocol : 'Auu____5089 'Auu____5090 . 'Auu____5089  ->  ((query_status * FStar_Util.json) * ('Auu____5089, 'Auu____5090) FStar_Util.either) = (fun st -> ((((QueryOK), (FStar_Util.JsonAssoc (alist_of_protocol_info)))), (FStar_Util.Inl (st))))


let run_describe_repl : 'Auu____5120 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5120) FStar_Util.either) = (fun st -> (

let uu____5138 = (

let uu____5143 = (json_of_repl_state st)
in ((QueryOK), (uu____5143)))
in ((uu____5138), (FStar_Util.Inl (st)))))


let run_protocol_violation : 'Auu____5160 'Auu____5161 . 'Auu____5160  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____5160, 'Auu____5161) FStar_Util.either) = (fun st message -> ((((QueryViolatesProtocol), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let run_generic_error : 'Auu____5200 'Auu____5201 . 'Auu____5200  ->  Prims.string  ->  ((query_status * FStar_Util.json) * ('Auu____5200, 'Auu____5201) FStar_Util.either) = (fun st message -> ((((QueryNOK), (FStar_Util.JsonStr (message)))), (FStar_Util.Inl (st))))


let collect_errors : unit  ->  FStar_Errors.issue Prims.list = (fun uu____5238 -> (

let errors = (FStar_Errors.report_all ())
in ((FStar_Errors.clear ());
errors;
)))


let run_segment : 'Auu____5249 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5249) FStar_Util.either) = (fun st code -> (

let frag = {FStar_Parser_ParseIt.frag_text = code; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let collect_decls = (fun uu____5280 -> (

let uu____5281 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____5281) with
| FStar_Parser_Driver.Empty -> begin
[]
end
| FStar_Parser_Driver.Decls (decls) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Module (uu____5287, decls)) -> begin
decls
end
| FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface (uu____5293, decls, uu____5295)) -> begin
decls
end)))
in (

let uu____5300 = (with_captured_errors st.repl_env FStar_Util.sigint_ignore (fun uu____5309 -> (

let uu____5310 = (collect_decls ())
in (FStar_All.pipe_left (fun _0_27 -> FStar_Pervasives_Native.Some (_0_27)) uu____5310))))
in (match (uu____5300) with
| FStar_Pervasives_Native.None -> begin
(

let errors = (

let uu____5338 = (collect_errors ())
in (FStar_All.pipe_right uu____5338 (FStar_List.map json_of_issue)))
in ((((QueryNOK), (FStar_Util.JsonList (errors)))), (FStar_Util.Inl (st))))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let json_of_decl = (fun decl -> (

let uu____5364 = (

let uu____5371 = (

let uu____5376 = (FStar_Range.json_of_def_range (FStar_Parser_AST.decl_drange decl))
in (("def_range"), (uu____5376)))
in (uu____5371)::[])
in FStar_Util.JsonAssoc (uu____5364)))
in (

let js_decls = (

let uu____5386 = (FStar_List.map json_of_decl decls)
in (FStar_All.pipe_left (fun _0_28 -> FStar_Util.JsonList (_0_28)) uu____5386))
in ((((QueryOK), (FStar_Util.JsonAssoc (((("decls"), (js_decls)))::[])))), (FStar_Util.Inl (st)))))
end)))))


let run_vfs_add : 'Auu____5415 . repl_state  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5415) FStar_Util.either) = (fun st opt_fname contents -> (

let fname = (FStar_Util.dflt st.repl_fname opt_fname)
in ((FStar_Parser_ParseIt.add_vfs_entry fname contents);
((((QueryOK), (FStar_Util.JsonNull))), (FStar_Util.Inl (st)));
)))


let run_pop : 'Auu____5461 . repl_state  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5461) FStar_Util.either) = (fun st -> (

let uu____5479 = (nothing_left_to_pop st)
in (match (uu____5479) with
| true -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Too many pops")))), (FStar_Util.Inl (st)))
end
| uu____5500 -> begin
(

let st' = (pop_repl st)
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

let uu____5549 = (json_of_message "progress" (FStar_Util.JsonAssoc (js_contents)))
in (write_json uu____5549)))))


let write_repl_ld_task_progress : repl_task  ->  unit = (fun task -> (match (task) with
| LDInterleaved (uu____5555, tf) -> begin
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
| PushFragment (frag) -> begin
()
end))


let load_deps : repl_state  ->  ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either = (fun st -> (

let uu____5602 = (with_captured_errors st.repl_env FStar_Util.sigint_ignore (fun _env -> (

let uu____5628 = (deps_and_repl_ld_tasks_of_our_file st.repl_fname)
in (FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) uu____5628))))
in (match (uu____5602) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (st)
end
| FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___102_5719 = st
in (

let uu____5720 = (FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1)
in {repl_line = uu___102_5719.repl_line; repl_column = uu___102_5719.repl_column; repl_fname = uu___102_5719.repl_fname; repl_deps_stack = uu___102_5719.repl_deps_stack; repl_curmod = uu___102_5719.repl_curmod; repl_env = uu____5720; repl_stdin = uu___102_5719.repl_stdin; repl_names = uu___102_5719.repl_names}))
in (

let uu____5721 = (run_repl_ld_transactions st1 tasks write_repl_ld_task_progress)
in (match (uu____5721) with
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

let uu___103_5767 = issue
in (

let uu____5768 = (FStar_Util.format1 "Error while computing or loading dependencies:\n%s" issue.FStar_Errors.issue_message)
in {FStar_Errors.issue_message = uu____5768; FStar_Errors.issue_level = uu___103_5767.FStar_Errors.issue_level; FStar_Errors.issue_range = uu___103_5767.FStar_Errors.issue_range; FStar_Errors.issue_number = uu___103_5767.FStar_Errors.issue_number})))


let run_push_without_deps : 'Auu____5775 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5775) FStar_Util.either) = (fun st query -> (

let set_nosynth_flag = (fun st1 flag -> (

let uu___104_5809 = st1
in {repl_line = uu___104_5809.repl_line; repl_column = uu___104_5809.repl_column; repl_fname = uu___104_5809.repl_fname; repl_deps_stack = uu___104_5809.repl_deps_stack; repl_curmod = uu___104_5809.repl_curmod; repl_env = (

let uu___105_5811 = st1.repl_env
in {FStar_TypeChecker_Env.solver = uu___105_5811.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_5811.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_5811.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_5811.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_5811.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_5811.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_5811.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_5811.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_5811.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_5811.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_5811.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_5811.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_5811.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___105_5811.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_5811.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___105_5811.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___105_5811.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_5811.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_5811.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_5811.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___105_5811.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = flag; FStar_TypeChecker_Env.tc_term = uu___105_5811.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___105_5811.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_5811.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___105_5811.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_5811.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___105_5811.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___105_5811.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___105_5811.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___105_5811.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___105_5811.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___105_5811.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___105_5811.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___105_5811.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___105_5811.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___105_5811.FStar_TypeChecker_Env.dep_graph}); repl_stdin = uu___104_5809.repl_stdin; repl_names = uu___104_5809.repl_names}))
in (

let uu____5812 = query
in (match (uu____5812) with
| {push_kind = push_kind; push_code = text; push_line = line; push_column = column; push_peek_only = peek_only} -> begin
(

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = line; FStar_Parser_ParseIt.frag_col = column}
in ((FStar_TypeChecker_Env.toggle_id_info st.repl_env true);
(

let st1 = (set_nosynth_flag st peek_only)
in (

let uu____5833 = (run_repl_transaction st1 push_kind peek_only (PushFragment (frag)))
in (match (uu____5833) with
| (success, st2) -> begin
(

let st3 = (set_nosynth_flag st2 false)
in (

let status = (match ((success || peek_only)) with
| true -> begin
QueryOK
end
| uu____5854 -> begin
QueryNOK
end)
in (

let json_errors = (

let uu____5856 = (

let uu____5859 = (collect_errors ())
in (FStar_All.pipe_right uu____5859 (FStar_List.map json_of_issue)))
in FStar_Util.JsonList (uu____5856))
in (

let st4 = (match (success) with
| true -> begin
(

let uu___106_5867 = st3
in {repl_line = line; repl_column = column; repl_fname = uu___106_5867.repl_fname; repl_deps_stack = uu___106_5867.repl_deps_stack; repl_curmod = uu___106_5867.repl_curmod; repl_env = uu___106_5867.repl_env; repl_stdin = uu___106_5867.repl_stdin; repl_names = uu___106_5867.repl_names})
end
| uu____5868 -> begin
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
| uu____5882 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____5884 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat (FStar_String.uppercase first) uu____5884)))
end))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____5914 = (FStar_Util.psmap_empty ())
in (

let uu____5917 = (

let uu____5920 = (FStar_Options.prims ())
in (uu____5920)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____5930 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____5930 true))) uu____5914 uu____5917)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____5948 -> (match (uu____5948) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____5956 -> begin
(

let ns_query = (

let uu____5960 = (capitalize modname)
in (FStar_Util.split uu____5960 "."))
in (

let uu____5961 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____5961 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods)))))))


let run_push_with_deps : 'Auu____5972 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____5972) FStar_Util.either) = (fun st query -> ((

let uu____5996 = (FStar_Options.debug_any ())
in (match (uu____5996) with
| true -> begin
(FStar_Util.print_string "Reloading dependencies")
end
| uu____5997 -> begin
()
end));
(FStar_TypeChecker_Env.toggle_id_info st.repl_env false);
(

let uu____5999 = (load_deps st)
in (match (uu____5999) with
| FStar_Util.Inr (st1) -> begin
(

let errors = (

let uu____6032 = (collect_errors ())
in (FStar_List.map rephrase_dependency_error uu____6032))
in (

let js_errors = (FStar_All.pipe_right errors (FStar_List.map json_of_issue))
in ((((QueryNOK), (FStar_Util.JsonList (js_errors)))), (FStar_Util.Inl (st1)))))
end
| FStar_Util.Inl (st1, deps) -> begin
((

let uu____6063 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____6063 (fun a241 -> ())));
(

let names1 = (add_module_completions st1.repl_fname deps st1.repl_names)
in (run_push_without_deps (

let uu___107_6066 = st1
in {repl_line = uu___107_6066.repl_line; repl_column = uu___107_6066.repl_column; repl_fname = uu___107_6066.repl_fname; repl_deps_stack = uu___107_6066.repl_deps_stack; repl_curmod = uu___107_6066.repl_curmod; repl_env = uu___107_6066.repl_env; repl_stdin = uu___107_6066.repl_stdin; repl_names = names1}) query));
)
end));
))


let run_push : 'Auu____6073 . repl_state  ->  push_query  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____6073) FStar_Util.either) = (fun st query -> (

let uu____6096 = (nothing_left_to_pop st)
in (match (uu____6096) with
| true -> begin
(run_push_with_deps st query)
end
| uu____6109 -> begin
(run_push_without_deps st query)
end)))


let run_symbol_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let tcenv = st.repl_env
in (

let info_of_lid_str = (fun lid_str -> (

let lid = (

let uu____6184 = (FStar_List.map FStar_Ident.id_of_text (FStar_Util.split lid_str "."))
in (FStar_Ident.lid_of_ids uu____6184))
in (

let lid1 = (

let uu____6188 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_left (FStar_Util.dflt lid) uu____6188))
in (

let uu____6193 = (FStar_TypeChecker_Env.try_lookup_lid tcenv lid1)
in (FStar_All.pipe_right uu____6193 (FStar_Util.map_option (fun uu____6248 -> (match (uu____6248) with
| ((uu____6267, typ), r) -> begin
((FStar_Util.Inr (lid1)), (typ), (r))
end))))))))
in (

let docs_of_lid = (fun lid -> (

let uu____6286 = (FStar_Syntax_DsEnv.try_lookup_doc tcenv.FStar_TypeChecker_Env.dsenv lid)
in (FStar_All.pipe_right uu____6286 (FStar_Util.map_option FStar_Pervasives_Native.fst))))
in (

let def_of_lid = (fun lid -> (

let uu____6317 = (FStar_TypeChecker_Env.lookup_qname tcenv lid)
in (FStar_Util.bind_opt uu____6317 (fun uu___88_6361 -> (match (uu___88_6361) with
| (FStar_Util.Inr (se, uu____6383), uu____6384) -> begin
(

let uu____6413 = (sigelt_to_string se)
in FStar_Pervasives_Native.Some (uu____6413))
end
| uu____6414 -> begin
FStar_Pervasives_Native.None
end)))))
in (

let info_at_pos_opt = (FStar_Util.bind_opt pos_opt (fun uu____6466 -> (match (uu____6466) with
| (file, row, col) -> begin
(FStar_TypeChecker_Err.info_at_pos tcenv file row col)
end)))
in (

let info_opt = (match (info_at_pos_opt) with
| FStar_Pervasives_Native.Some (uu____6513) -> begin
info_at_pos_opt
end
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality symbol "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6566 -> begin
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

let uu____6641 = (term_to_string tcenv typ)
in FStar_Pervasives_Native.Some (uu____6641))
end
| uu____6642 -> begin
FStar_Pervasives_Native.None
end)
in (

let doc_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "documentation" requested_info) -> begin
(docs_of_lid lid)
end
| uu____6649 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_str = (match (name_or_lid) with
| FStar_Util.Inr (lid) when (FStar_List.mem "definition" requested_info) -> begin
(def_of_lid lid)
end
| uu____6660 -> begin
FStar_Pervasives_Native.None
end)
in (

let def_range1 = (match ((FStar_List.mem "defined-at" requested_info)) with
| true -> begin
FStar_Pervasives_Native.Some (rng)
end
| uu____6670 -> begin
FStar_Pervasives_Native.None
end)
in (

let result = {slr_name = name; slr_def_range = def_range1; slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str}
in (

let uu____6672 = (

let uu____6683 = (alist_of_symbol_lookup_result result)
in (("symbol"), (uu____6683)))
in FStar_Pervasives_Native.Some (uu____6672))))))))
end)
in (match (response) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Symbol not found")
end
| FStar_Pervasives_Native.Some (info) -> begin
FStar_Util.Inr (info)
end)))))))))


let run_option_lookup : Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun opt_name -> (

let uu____6790 = (trim_option_name opt_name)
in (match (uu____6790) with
| (uu____6809, trimmed_name) -> begin
(

let uu____6811 = (FStar_Util.smap_try_find fstar_options_map_cache trimmed_name)
in (match (uu____6811) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ((Prims.strcat "Unknown option:" opt_name))
end
| FStar_Pervasives_Native.Some (opt) -> begin
(

let uu____6839 = (

let uu____6850 = (

let uu____6857 = (update_option opt)
in (alist_of_fstar_option uu____6857))
in (("option"), (uu____6850)))
in FStar_Util.Inr (uu____6839))
end))
end)))


let run_module_lookup : repl_state  ->  Prims.string  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol -> (

let query = (FStar_Util.split symbol ".")
in (

let uu____6901 = (FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names query)
in (match (uu____6901) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("No such module or namespace")
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Module (mod_info)) -> begin
(

let uu____6929 = (

let uu____6940 = (FStar_Interactive_CompletionTable.alist_of_mod_info mod_info)
in (("module"), (uu____6940)))
in FStar_Util.Inr (uu____6929))
end
| FStar_Pervasives_Native.Some (FStar_Interactive_CompletionTable.Namespace (ns_info)) -> begin
(

let uu____6964 = (

let uu____6975 = (FStar_Interactive_CompletionTable.alist_of_ns_info ns_info)
in (("namespace"), (uu____6975)))
in FStar_Util.Inr (uu____6964))
end))))


let run_code_lookup : repl_state  ->  Prims.string  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  (Prims.string, (Prims.string * (Prims.string * FStar_Util.json) Prims.list)) FStar_Util.either = (fun st symbol pos_opt requested_info -> (

let uu____7052 = (run_symbol_lookup st symbol pos_opt requested_info)
in (match (uu____7052) with
| FStar_Util.Inr (alist) -> begin
FStar_Util.Inr (alist)
end
| FStar_Util.Inl (uu____7112) -> begin
(

let uu____7123 = (run_module_lookup st symbol)
in (match (uu____7123) with
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


let run_lookup : 'Auu____7289 . repl_state  ->  Prims.string  ->  lookup_context  ->  (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option  ->  Prims.string Prims.list  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7289) FStar_Util.either) = (fun st symbol context pos_opt requested_info -> (

let uu____7347 = (run_lookup' st symbol context pos_opt requested_info)
in (match (uu____7347) with
| FStar_Util.Inl (err_msg) -> begin
((((QueryNOK), (FStar_Util.JsonStr (err_msg)))), (FStar_Util.Inl (st)))
end
| FStar_Util.Inr (kind, info) -> begin
((((QueryOK), (FStar_Util.JsonAssoc (((("kind"), (FStar_Util.JsonStr (kind))))::info)))), (FStar_Util.Inl (st)))
end)))


let code_autocomplete_mod_filter : 'Auu____7433 . ('Auu____7433 * FStar_Interactive_CompletionTable.mod_symbol)  ->  ('Auu____7433 * FStar_Interactive_CompletionTable.mod_symbol) FStar_Pervasives_Native.option = (fun uu___89_7448 -> (match (uu___89_7448) with
| (uu____7453, FStar_Interactive_CompletionTable.Namespace (uu____7454)) -> begin
FStar_Pervasives_Native.None
end
| (uu____7459, FStar_Interactive_CompletionTable.Module ({FStar_Interactive_CompletionTable.mod_name = uu____7460; FStar_Interactive_CompletionTable.mod_path = uu____7461; FStar_Interactive_CompletionTable.mod_loaded = true})) -> begin
FStar_Pervasives_Native.None
end
| (pth, FStar_Interactive_CompletionTable.Module (md)) -> begin
(

let uu____7468 = (

let uu____7473 = (

let uu____7474 = (

let uu___108_7475 = md
in (

let uu____7476 = (

let uu____7477 = (FStar_Interactive_CompletionTable.mod_name md)
in (Prims.strcat uu____7477 "."))
in {FStar_Interactive_CompletionTable.mod_name = uu____7476; FStar_Interactive_CompletionTable.mod_path = uu___108_7475.FStar_Interactive_CompletionTable.mod_path; FStar_Interactive_CompletionTable.mod_loaded = uu___108_7475.FStar_Interactive_CompletionTable.mod_loaded}))
in FStar_Interactive_CompletionTable.Module (uu____7474))
in ((pth), (uu____7473)))
in FStar_Pervasives_Native.Some (uu____7468))
end))


let run_code_autocomplete : 'Auu____7488 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7488) FStar_Util.either) = (fun st search_term -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle code_autocomplete_mod_filter)
in (

let lids = (FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names needle)
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result (FStar_List.append lids mods_and_nss))
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st))))))))


let run_module_autocomplete : 'Auu____7545 'Auu____7546 'Auu____7547 . repl_state  ->  Prims.string  ->  'Auu____7545  ->  'Auu____7546  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7547) FStar_Util.either) = (fun st search_term modules1 namespaces -> (

let needle = (FStar_Util.split search_term ".")
in (

let mods_and_nss = (FStar_Interactive_CompletionTable.autocomplete_mod_or_ns st.repl_names needle (fun _0_30 -> FStar_Pervasives_Native.Some (_0_30)))
in (

let json = (FStar_List.map FStar_Interactive_CompletionTable.json_of_completion_result mods_and_nss)
in ((((QueryOK), (FStar_Util.JsonList (json)))), (FStar_Util.Inl (st)))))))


let candidates_of_fstar_option : Prims.int  ->  Prims.bool  ->  fstar_option  ->  FStar_Interactive_CompletionTable.completion_result Prims.list = (fun match_len is_reset opt -> (

let uu____7618 = (match (opt.opt_permission_level) with
| OptSet -> begin
((true), (""))
end
| OptReset -> begin
((is_reset), ("#reset-only"))
end
| OptReadOnly -> begin
((false), ("read-only"))
end)
in (match (uu____7618) with
| (may_set, explanation) -> begin
(

let opt_type = (kind_of_fstar_option_type opt.opt_type)
in (

let annot = (match (may_set) with
| true -> begin
opt_type
end
| uu____7633 -> begin
(Prims.strcat "(" (Prims.strcat explanation (Prims.strcat " " (Prims.strcat opt_type ")"))))
end)
in (FStar_All.pipe_right opt.opt_snippets (FStar_List.map (fun snippet -> {FStar_Interactive_CompletionTable.completion_match_length = match_len; FStar_Interactive_CompletionTable.completion_candidate = snippet; FStar_Interactive_CompletionTable.completion_annotation = annot})))))
end)))


let run_option_autocomplete : 'Auu____7650 'Auu____7651 . 'Auu____7650  ->  Prims.string  ->  Prims.bool  ->  ((query_status * FStar_Util.json) * ('Auu____7650, 'Auu____7651) FStar_Util.either) = (fun st search_term is_reset -> (

let uu____7679 = (trim_option_name search_term)
in (match (uu____7679) with
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
| (uu____7734, uu____7735) -> begin
((((QueryNOK), (FStar_Util.JsonStr ("Options should start with \'--\'")))), (FStar_Util.Inl (st)))
end)))


let run_autocomplete : 'Auu____7752 . repl_state  ->  Prims.string  ->  completion_context  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7752) FStar_Util.either) = (fun st search_term context -> (match (context) with
| CKCode -> begin
(run_code_autocomplete st search_term)
end
| CKOption (is_reset) -> begin
(run_option_autocomplete st search_term is_reset)
end
| CKModuleOrNamespace (modules1, namespaces) -> begin
(run_module_autocomplete st search_term modules1 namespaces)
end))


let run_and_rewind : 'Auu____7793 'Auu____7794 . repl_state  ->  'Auu____7793  ->  (repl_state  ->  'Auu____7793)  ->  ('Auu____7793 * (repl_state, 'Auu____7794) FStar_Util.either) = (fun st sigint_default task -> (

let env' = (push st.repl_env "REPL run_and_rewind")
in (

let results = (FStar_All.try_with (fun uu___110_7834 -> (match (()) with
| () -> begin
(FStar_Util.with_sigint_handler FStar_Util.sigint_raise (fun uu____7845 -> (

let uu____7846 = (task st)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Util.Inl (_0_31)) uu____7846))))
end)) (fun uu___109_7852 -> (match (uu___109_7852) with
| FStar_Util.SigInt -> begin
FStar_Util.Inl (sigint_default)
end
| e -> begin
FStar_Util.Inr (e)
end)))
in ((pop env' "REPL run_and_rewind");
(match (results) with
| FStar_Util.Inl (results1) -> begin
((results1), (FStar_Util.Inl ((

let uu___111_7873 = st
in {repl_line = uu___111_7873.repl_line; repl_column = uu___111_7873.repl_column; repl_fname = uu___111_7873.repl_fname; repl_deps_stack = uu___111_7873.repl_deps_stack; repl_curmod = uu___111_7873.repl_curmod; repl_env = env'; repl_stdin = uu___111_7873.repl_stdin; repl_names = uu___111_7873.repl_names}))))
end
| FStar_Util.Inr (e) -> begin
(FStar_Exn.raise e)
end);
))))


let run_with_parsed_and_tc_term : 'Auu____7899 'Auu____7900 'Auu____7901 . repl_state  ->  Prims.string  ->  'Auu____7899  ->  'Auu____7900  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (query_status * FStar_Util.json))  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____7901) FStar_Util.either) = (fun st term line column continuation -> (

let dummy_let_fragment = (fun term1 -> (

let dummy_decl = (FStar_Util.format1 "let __compute_dummy__ = (%s)" term1)
in {FStar_Parser_ParseIt.frag_text = dummy_decl; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}))
in (

let find_let_body = (fun ses -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((uu____7994, ({FStar_Syntax_Syntax.lbname = uu____7995; FStar_Syntax_Syntax.lbunivs = univs1; FStar_Syntax_Syntax.lbtyp = uu____7997; FStar_Syntax_Syntax.lbeff = uu____7998; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu____8000; FStar_Syntax_Syntax.lbpos = uu____8001})::[]), uu____8002); FStar_Syntax_Syntax.sigrng = uu____8003; FStar_Syntax_Syntax.sigquals = uu____8004; FStar_Syntax_Syntax.sigmeta = uu____8005; FStar_Syntax_Syntax.sigattrs = uu____8006})::[] -> begin
FStar_Pervasives_Native.Some (((univs1), (def)))
end
| uu____8049 -> begin
FStar_Pervasives_Native.None
end))
in (

let parse1 = (fun frag -> (

let uu____8070 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel (frag)))
in (match (uu____8070) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (decls), uu____8076) -> begin
FStar_Pervasives_Native.Some (decls)
end
| uu____8101 -> begin
FStar_Pervasives_Native.None
end)))
in (

let desugar = (fun env decls -> (

let uu____8119 = (

let uu____8124 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts decls)
in (uu____8124 env.FStar_TypeChecker_Env.dsenv))
in (FStar_Pervasives_Native.fst uu____8119)))
in (

let typecheck = (fun tcenv decls -> (

let uu____8148 = (FStar_TypeChecker_Tc.tc_decls tcenv decls)
in (match (uu____8148) with
| (ses, uu____8162, uu____8163) -> begin
ses
end)))
in (run_and_rewind st ((QueryNOK), (FStar_Util.JsonStr ("Computation interrupted"))) (fun st1 -> (

let tcenv = st1.repl_env
in (

let frag = (dummy_let_fragment term)
in (match (st1.repl_curmod) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Current module unset")))
end
| uu____8186 -> begin
(

let uu____8187 = (parse1 frag)
in (match (uu____8187) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Could not parse this term")))
end
| FStar_Pervasives_Native.Some (decls) -> begin
(

let aux = (fun uu____8212 -> (

let decls1 = (desugar tcenv decls)
in (

let ses = (typecheck tcenv decls1)
in (match ((find_let_body ses)) with
| FStar_Pervasives_Native.None -> begin
((QueryNOK), (FStar_Util.JsonStr ("Typechecking yielded an unexpected term")))
end
| FStar_Pervasives_Native.Some (univs1, def) -> begin
(

let uu____8247 = (FStar_Syntax_Subst.open_univ_vars univs1 def)
in (match (uu____8247) with
| (univs2, def1) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.push_univ_vars tcenv univs2)
in (continuation tcenv1 def1))
end))
end))))
in (

let uu____8259 = (FStar_Options.trace_error ())
in (match (uu____8259) with
| true -> begin
(aux ())
end
| uu____8264 -> begin
(FStar_All.try_with (fun uu___113_8270 -> (match (()) with
| () -> begin
(aux ())
end)) (fun uu___112_8280 -> (match (uu___112_8280) with
| e -> begin
(

let uu____8286 = (FStar_Errors.issue_of_exn e)
in (match (uu____8286) with
| FStar_Pervasives_Native.Some (issue) -> begin
(

let uu____8294 = (

let uu____8295 = (FStar_Errors.format_issue issue)
in FStar_Util.JsonStr (uu____8295))
in ((QueryNOK), (uu____8294)))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise e)
end))
end)))
end)))
end))
end)))))))))))


let run_compute : 'Auu____8308 . repl_state  ->  Prims.string  ->  FStar_TypeChecker_Normalize.step Prims.list FStar_Pervasives_Native.option  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____8308) FStar_Util.either) = (fun st term rules -> (

let rules1 = (FStar_List.append (match (rules) with
| FStar_Pervasives_Native.Some (rules1) -> begin
rules1
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]
end) ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Primops)::[]))
in (

let normalize_term1 = (fun tcenv rules2 t -> (FStar_TypeChecker_Normalize.normalize rules2 tcenv t))
in (run_with_parsed_and_tc_term st term (Prims.parse_int "0") (Prims.parse_int "0") (fun tcenv def -> (

let normalized = (normalize_term1 tcenv rules1 def)
in (

let uu____8380 = (

let uu____8381 = (term_to_string tcenv normalized)
in FStar_Util.JsonStr (uu____8381))
in ((QueryOK), (uu____8380)))))))))

type search_term' =
| NameContainsStr of Prims.string
| TypeContainsLid of FStar_Ident.lid 
 and search_term =
{st_negate : Prims.bool; st_term : search_term'}


let uu___is_NameContainsStr : search_term'  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NameContainsStr (_0) -> begin
true
end
| uu____8408 -> begin
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
| uu____8422 -> begin
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


let st_cost : search_term'  ->  Prims.int = (fun uu___90_8448 -> (match (uu___90_8448) with
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

let uu____8903 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let uu____8910 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in {sc_lid = lid; sc_typ = uu____8903; sc_fvars = uu____8910})))


let sc_typ : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Syntax_Syntax.typ = (fun tcenv sc -> (

let uu____9073 = (FStar_ST.op_Bang sc.sc_typ)
in (match (uu____9073) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let typ = (

let uu____9113 = (FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid)
in (match (uu____9113) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Pervasives_Native.Some ((uu____9134, typ), uu____9136) -> begin
typ
end))
in ((FStar_ST.op_Colon_Equals sc.sc_typ (FStar_Pervasives_Native.Some (typ)));
typ;
))
end)))


let sc_fvars : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Ident.lid FStar_Util.set = (fun tcenv sc -> (

let uu____9197 = (FStar_ST.op_Bang sc.sc_fvars)
in (match (uu____9197) with
| FStar_Pervasives_Native.Some (fv) -> begin
fv
end
| FStar_Pervasives_Native.None -> begin
(

let fv = (

let uu____9251 = (sc_typ tcenv sc)
in (FStar_Syntax_Free.fvars uu____9251))
in ((FStar_ST.op_Colon_Equals sc.sc_fvars (FStar_Pervasives_Native.Some (fv)));
fv;
))
end)))


let json_of_search_result : FStar_TypeChecker_Env.env  ->  search_candidate  ->  FStar_Util.json = (fun tcenv sc -> (

let typ_str = (

let uu____9303 = (sc_typ tcenv sc)
in (term_to_string tcenv uu____9303))
in (

let uu____9304 = (

let uu____9311 = (

let uu____9316 = (

let uu____9317 = (

let uu____9318 = (FStar_Syntax_DsEnv.shorten_lid tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid)
in uu____9318.FStar_Ident.str)
in FStar_Util.JsonStr (uu____9317))
in (("lid"), (uu____9316)))
in (uu____9311)::((("type"), (FStar_Util.JsonStr (typ_str))))::[])
in FStar_Util.JsonAssoc (uu____9304))))

exception InvalidSearch of (Prims.string)


let uu___is_InvalidSearch : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____9340) -> begin
true
end
| uu____9341 -> begin
false
end))


let __proj__InvalidSearch__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| InvalidSearch (uu____9348) -> begin
uu____9348
end))


let run_search : 'Auu____9355 . repl_state  ->  Prims.string  ->  ((query_status * FStar_Util.json) * (repl_state, 'Auu____9355) FStar_Util.either) = (fun st search_str -> (

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

let uu____9396 = (sc_fvars tcenv candidate)
in (FStar_Util.set_mem lid uu____9396))
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
| uu____9415 -> begin
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
| uu____9424 -> begin
(FStar_Util.substring str (Prims.parse_int "1") ((FStar_String.length term1) - (Prims.parse_int "2")))
end))
in (

let parsed = (match ((Prims.op_disEquality beg_quote end_quote)) with
| true -> begin
(

let uu____9426 = (

let uu____9427 = (FStar_Util.format1 "Improperly quoted search term: %s" term1)
in InvalidSearch (uu____9427))
in (FStar_Exn.raise uu____9426))
end
| uu____9428 -> begin
(match (beg_quote) with
| true -> begin
(

let uu____9429 = (strip_quotes term1)
in NameContainsStr (uu____9429))
end
| uu____9430 -> begin
(

let lid = (FStar_Ident.lid_of_str term1)
in (

let uu____9432 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name tcenv.FStar_TypeChecker_Env.dsenv lid)
in (match (uu____9432) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9435 = (

let uu____9436 = (FStar_Util.format1 "Unknown identifier: %s" term1)
in InvalidSearch (uu____9436))
in (FStar_Exn.raise uu____9435))
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

let uu____9458 = (match (term.st_term) with
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
| uu____9461 -> begin
""
end) uu____9458)))
in (

let results = (FStar_All.try_with (fun uu___115_9482 -> (match (()) with
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

let uu____9527 = (FStar_List.map pprint_one terms)
in (FStar_Util.concat_l " " uu____9527))
in (

let uu____9530 = (

let uu____9531 = (FStar_Util.format1 "No results found for query [%s]" kwds)
in InvalidSearch (uu____9531))
in (FStar_Exn.raise uu____9530)))
end
| uu____9536 -> begin
((QueryOK), (FStar_Util.JsonList (js)))
end)))))))))
end)) (fun uu___114_9541 -> (match (uu___114_9541) with
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
| Push ({push_kind = SyntaxCheck; push_code = uu____9634; push_line = uu____9635; push_column = uu____9636; push_peek_only = false}) -> begin
{qq = ProtocolViolation ("Cannot use \'kind\': \'syntax\' with \'query\': \'push\'"); qid = q.qid}
end
| uu____9637 -> begin
(match (st.repl_curmod) with
| FStar_Pervasives_Native.None when (query_needs_current_module q.qq) -> begin
{qq = GenericError ("Current module unset"); qid = q.qid}
end
| uu____9638 -> begin
q
end)
end))


let validate_and_run_query : repl_state  ->  query  ->  ((query_status * FStar_Util.json) * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let query1 = (validate_query st query)
in ((FStar_ST.op_Colon_Equals repl_current_qid (FStar_Pervasives_Native.Some (query1.qid)));
(run_query st query1.qq);
)))


let js_repl_eval : repl_state  ->  query  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query -> (

let uu____9714 = (validate_and_run_query st query)
in (match (uu____9714) with
| ((status, response), st_opt) -> begin
(

let js_response = (json_of_response query.qid status response)
in ((js_response), (st_opt)))
end)))


let js_repl_eval_js : repl_state  ->  FStar_Util.json  ->  (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either) = (fun st query_js -> (

let uu____9773 = (deserialize_interactive_query query_js)
in (js_repl_eval st uu____9773)))


let js_repl_eval_str : repl_state  ->  Prims.string  ->  (Prims.string * (repl_state, Prims.int) FStar_Util.either) = (fun st query_str -> (

let uu____9792 = (

let uu____9801 = (parse_interactive_query query_str)
in (js_repl_eval st uu____9801))
in (match (uu____9792) with
| (js_response, st_opt) -> begin
(

let uu____9820 = (FStar_Util.string_of_json js_response)
in ((uu____9820), (st_opt)))
end)))


let js_repl_init_opts : unit  ->  unit = (fun uu____9829 -> (

let uu____9830 = (FStar_Options.parse_cmd_line ())
in (match (uu____9830) with
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
| (h)::(uu____9845)::uu____9846 -> begin
(failwith "repl_init: Too many file names given in --ide invocation")
end
| uu____9849 -> begin
()
end)
end)
end)))


let rec go : repl_state  ->  Prims.int = (fun st -> (

let query = (read_interactive_query st.repl_stdin)
in (

let uu____9858 = (validate_and_run_query st query)
in (match (uu____9858) with
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

let uu____9902 = (

let uu____9905 = (FStar_ST.op_Bang issues)
in (e)::uu____9905)
in (FStar_ST.op_Colon_Equals issues uu____9902)))
in (

let count_errors = (fun uu____10119 -> (

let uu____10120 = (

let uu____10123 = (FStar_ST.op_Bang issues)
in (FStar_List.filter (fun e -> (Prims.op_Equality e.FStar_Errors.issue_level FStar_Errors.EError)) uu____10123))
in (FStar_List.length uu____10120)))
in (

let report = (fun uu____10238 -> (

let uu____10239 = (FStar_ST.op_Bang issues)
in (FStar_List.sortWith FStar_Errors.compare_issues uu____10239)))
in (

let clear1 = (fun uu____10350 -> (FStar_ST.op_Colon_Equals issues []))
in {FStar_Errors.eh_add_one = add_one1; FStar_Errors.eh_count_errors = count_errors; FStar_Errors.eh_report = report; FStar_Errors.eh_clear = clear1})))))


let interactive_printer : (FStar_Util.json  ->  unit)  ->  FStar_Util.printer = (fun printer -> {FStar_Util.printer_prinfo = (fun s -> (forward_message printer "info" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prwarning = (fun s -> (forward_message printer "warning" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prerror = (fun s -> (forward_message printer "error" (FStar_Util.JsonStr (s)))); FStar_Util.printer_prgeneric = (fun label get_string get_json -> (

let uu____10486 = (get_json ())
in (forward_message printer label uu____10486)))})


let install_ide_mode_hooks : (FStar_Util.json  ->  unit)  ->  unit = (fun printer -> ((FStar_Util.set_printer (interactive_printer printer));
(FStar_Errors.set_handler interactive_error_handler);
))


let initial_range : FStar_Range.range = (

let uu____10498 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (

let uu____10499 = (FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0"))
in (FStar_Range.mk_range "<input>" uu____10498 uu____10499)))


let build_initial_repl_state : Prims.string  ->  repl_state = (fun filename -> (

let env = (FStar_Universal.init_env FStar_Parser_Dep.empty_deps)
in (

let env1 = (FStar_TypeChecker_Env.set_range env initial_range)
in (

let uu____10507 = (FStar_Util.open_stdin ())
in {repl_line = (Prims.parse_int "1"); repl_column = (Prims.parse_int "0"); repl_fname = filename; repl_deps_stack = []; repl_curmod = FStar_Pervasives_Native.None; repl_env = env1; repl_stdin = uu____10507; repl_names = FStar_Interactive_CompletionTable.empty}))))


let interactive_mode' : 'Auu____10516 . repl_state  ->  'Auu____10516 = (fun init_st -> ((write_hello ());
(

let exit_code = (

let uu____10524 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____10524) with
| true -> begin
(

let uu____10525 = (

let uu____10526 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10526))
in (FStar_SMTEncoding_Solver.with_hints_db uu____10525 (fun uu____10530 -> (go init_st))))
end
| uu____10531 -> begin
(go init_st)
end))
in (FStar_All.exit exit_code));
))


let interactive_mode : Prims.string  ->  unit = (fun filename -> ((install_ide_mode_hooks write_json);
(FStar_Util.set_sigint_handler FStar_Util.sigint_ignore);
(

let uu____10540 = (

let uu____10541 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____10541))
in (match (uu____10540) with
| true -> begin
(FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Warning_IDEIgnoreCodeGen), ("--ide: ignoring --codegen")))
end
| uu____10544 -> begin
()
end));
(

let init1 = (build_initial_repl_state filename)
in (

let uu____10546 = (FStar_Options.trace_error ())
in (match (uu____10546) with
| true -> begin
(interactive_mode' init1)
end
| uu____10547 -> begin
(FStar_All.try_with (fun uu___117_10549 -> (match (()) with
| () -> begin
(interactive_mode' init1)
end)) (fun uu___116_10553 -> (match (uu___116_10553) with
| e -> begin
((FStar_Errors.set_handler FStar_Errors.default_handler);
(FStar_Exn.raise e);
)
end)))
end)));
))




