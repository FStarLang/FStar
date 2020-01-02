
open Prims
open FStar_Pervasives
type push_kind =
| SyntaxCheck
| LaxCheck
| FullCheck


let uu___is_SyntaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SyntaxCheck -> begin
true
end
| uu____8 -> begin
false
end))


let uu___is_LaxCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LaxCheck -> begin
true
end
| uu____19 -> begin
false
end))


let uu___is_FullCheck : push_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FullCheck -> begin
true
end
| uu____30 -> begin
false
end))


type ctx_depth_t =
(Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int)


type deps_t =
FStar_Parser_Dep.deps


type either_replst =
(FStar_Interactive_JsonHelper.repl_state, FStar_Interactive_JsonHelper.repl_state) FStar_Util.either


let repl_stack : FStar_Interactive_JsonHelper.repl_stack_t FStar_ST.ref = (FStar_Util.mk_ref [])


let set_check_kind : FStar_TypeChecker_Env.env_t  ->  push_kind  ->  FStar_TypeChecker_Env.env_t = (fun env check_kind -> (

let uu___4_71 = env
in (

let uu____72 = (FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv (Prims.op_Equality check_kind SyntaxCheck))
in {FStar_TypeChecker_Env.solver = uu___4_71.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___4_71.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___4_71.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___4_71.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___4_71.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___4_71.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___4_71.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___4_71.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___4_71.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___4_71.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___4_71.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___4_71.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___4_71.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___4_71.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___4_71.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___4_71.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___4_71.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___4_71.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___4_71.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = (Prims.op_Equality check_kind LaxCheck); FStar_TypeChecker_Env.lax_universes = uu___4_71.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___4_71.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___4_71.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___4_71.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___4_71.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___4_71.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___4_71.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___4_71.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___4_71.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___4_71.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___4_71.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___4_71.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___4_71.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___4_71.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___4_71.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___4_71.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___4_71.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___4_71.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___4_71.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___4_71.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___4_71.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu____72; FStar_TypeChecker_Env.nbe = uu___4_71.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___4_71.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___4_71.FStar_TypeChecker_Env.erasable_types_tab})))


let repl_ld_tasks_of_deps : Prims.string Prims.list  ->  FStar_Interactive_JsonHelper.repl_task Prims.list  ->  FStar_Interactive_JsonHelper.repl_task Prims.list = (fun deps final_tasks -> (

let wrap = (fun fname -> (

let uu____104 = (FStar_Util.now ())
in {FStar_Interactive_JsonHelper.tf_fname = fname; FStar_Interactive_JsonHelper.tf_modtime = uu____104}))
in (

let rec aux = (fun deps1 final_tasks1 -> (match (deps1) with
| (intf)::(impl)::deps' when (FStar_Universal.needs_interleaving intf impl) -> begin
(

let uu____140 = (

let uu____141 = (

let uu____146 = (wrap intf)
in (

let uu____147 = (wrap impl)
in ((uu____146), (uu____147))))
in FStar_Interactive_JsonHelper.LDInterleaved (uu____141))
in (

let uu____148 = (aux deps' final_tasks1)
in (uu____140)::uu____148))
end
| (intf_or_impl)::deps' -> begin
(

let uu____158 = (

let uu____159 = (wrap intf_or_impl)
in FStar_Interactive_JsonHelper.LDSingle (uu____159))
in (

let uu____160 = (aux deps' final_tasks1)
in (uu____158)::uu____160))
end
| [] -> begin
final_tasks1
end))
in (aux deps final_tasks))))


let deps_and_repl_ld_tasks_of_our_file : Prims.string  ->  (Prims.string Prims.list * FStar_Interactive_JsonHelper.repl_task Prims.list * deps_t) = (fun filename -> (

let get_mod_name = (fun fname -> (FStar_Parser_Dep.lowercase_module_name fname))
in (

let our_mod_name = (get_mod_name filename)
in (

let has_our_mod_name = (fun f -> (

let uu____214 = (get_mod_name f)
in (Prims.op_Equality uu____214 our_mod_name)))
in (

let parse_data_cache = FStar_CheckedFiles.load_parsing_data_from_cache
in (

let uu____225 = (FStar_Dependencies.find_deps_if_needed ((filename)::[]) parse_data_cache)
in (match (uu____225) with
| (deps, dep_graph1) -> begin
(

let uu____254 = (FStar_List.partition has_our_mod_name deps)
in (match (uu____254) with
| (same_name, real_deps) -> begin
(

let intf_tasks = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____304 = (

let uu____306 = (FStar_Parser_Dep.is_interface intf)
in (not (uu____306)))
in (match (uu____304) with
| true -> begin
(

let uu____309 = (

let uu____315 = (FStar_Util.format1 "Expecting an interface, got %s" intf)
in ((FStar_Errors.Fatal_MissingInterface), (uu____315)))
in (FStar_Errors.raise_err uu____309))
end
| uu____319 -> begin
()
end));
(

let uu____322 = (

let uu____324 = (FStar_Parser_Dep.is_implementation impl)
in (not (uu____324)))
in (match (uu____322) with
| true -> begin
(

let uu____327 = (

let uu____333 = (FStar_Util.format1 "Expecting an implementation, got %s" impl)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____333)))
in (FStar_Errors.raise_err uu____327))
end
| uu____337 -> begin
()
end));
(

let uu____339 = (

let uu____340 = (

let uu____341 = (FStar_Util.now ())
in {FStar_Interactive_JsonHelper.tf_fname = intf; FStar_Interactive_JsonHelper.tf_modtime = uu____341})
in FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (uu____340))
in (uu____339)::[]);
)
end
| (impl)::[] -> begin
[]
end
| uu____346 -> begin
(

let mods_str = (FStar_String.concat " " same_name)
in (

let message = "Too many or too few files matching %s: %s"
in ((

let uu____357 = (

let uu____363 = (FStar_Util.format message ((our_mod_name)::(mods_str)::[]))
in ((FStar_Errors.Fatal_TooManyOrTooFewFileMatch), (uu____363)))
in (FStar_Errors.raise_err uu____357));
[];
)))
end)
in (

let tasks = (repl_ld_tasks_of_deps real_deps intf_tasks)
in ((real_deps), (tasks), (dep_graph1))))
end))
end)))))))


let snapshot_env : FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Interactive_JsonHelper.repl_depth_t * FStar_TypeChecker_Env.env_t) = (fun env msg -> (

let uu____398 = (FStar_TypeChecker_Tc.snapshot_context env msg)
in (match (uu____398) with
| (ctx_depth, env1) -> begin
(

let uu____442 = (FStar_Options.snapshot ())
in (match (uu____442) with
| (opt_depth, ()) -> begin
((((ctx_depth), (opt_depth))), (env1))
end))
end)))


let push_repl : Prims.string  ->  push_kind  ->  FStar_Interactive_JsonHelper.repl_task  ->  FStar_Interactive_JsonHelper.repl_state  ->  FStar_Interactive_JsonHelper.repl_state = (fun msg push_kind task st -> (

let uu____479 = (snapshot_env st.FStar_Interactive_JsonHelper.repl_env msg)
in (match (uu____479) with
| (depth, env) -> begin
((

let uu____487 = (

let uu____488 = (FStar_ST.op_Bang repl_stack)
in (((depth), (((task), (st)))))::uu____488)
in (FStar_ST.op_Colon_Equals repl_stack uu____487));
(

let uu___66_549 = st
in (

let uu____550 = (set_check_kind env push_kind)
in {FStar_Interactive_JsonHelper.repl_line = uu___66_549.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___66_549.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___66_549.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___66_549.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___66_549.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu____550; FStar_Interactive_JsonHelper.repl_stdin = uu___66_549.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___66_549.FStar_Interactive_JsonHelper.repl_names}));
)
end)))


let rollback_env : FStar_TypeChecker_Env.solver_t  ->  Prims.string  ->  ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) * Prims.int)  ->  FStar_TypeChecker_Env.env = (fun solver1 msg uu____583 -> (match (uu____583) with
| (ctx_depth, opt_depth) -> begin
(

let env = (FStar_TypeChecker_Tc.rollback_context solver1 msg (FStar_Pervasives_Native.Some (ctx_depth)))
in ((FStar_Options.rollback (FStar_Pervasives_Native.Some (opt_depth)));
env;
))
end))


let pop_repl : Prims.string  ->  FStar_Interactive_JsonHelper.repl_state  ->  FStar_Interactive_JsonHelper.repl_state = (fun msg st -> (

let uu____654 = (FStar_ST.op_Bang repl_stack)
in (match (uu____654) with
| [] -> begin
(failwith "Too many pops")
end
| ((depth, (uu____684, st')))::stack_tl -> begin
(

let env = (rollback_env st.FStar_Interactive_JsonHelper.repl_env.FStar_TypeChecker_Env.solver msg depth)
in ((FStar_ST.op_Colon_Equals repl_stack stack_tl);
(

let uu____731 = (FStar_Util.physical_equality env st'.FStar_Interactive_JsonHelper.repl_env)
in (FStar_Common.runtime_assert uu____731 "Inconsistent stack state"));
st';
))
end)))


let tc_one : FStar_TypeChecker_Env.env_t  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_TypeChecker_Env.env_t = (fun env intf_opt modf -> (

let parse_data = (

let uu____759 = (

let uu____765 = (FStar_TypeChecker_Env.dep_graph env)
in (FStar_Parser_Dep.parsing_data_of uu____765))
in (FStar_All.pipe_right modf uu____759))
in (

let uu____767 = (FStar_Universal.tc_one_file_for_ide env intf_opt modf parse_data)
in (match (uu____767) with
| (uu____772, env1) -> begin
env1
end))))


let run_repl_task : FStar_Interactive_JsonHelper.optmod_t  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Interactive_JsonHelper.repl_task  ->  (FStar_Interactive_JsonHelper.optmod_t * FStar_TypeChecker_Env.env_t) = (fun curmod env task -> (match (task) with
| FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) -> begin
(

let uu____800 = (tc_one env (FStar_Pervasives_Native.Some (intf.FStar_Interactive_JsonHelper.tf_fname)) impl.FStar_Interactive_JsonHelper.tf_fname)
in ((curmod), (uu____800)))
end
| FStar_Interactive_JsonHelper.LDSingle (intf_or_impl) -> begin
(

let uu____803 = (tc_one env FStar_Pervasives_Native.None intf_or_impl.FStar_Interactive_JsonHelper.tf_fname)
in ((curmod), (uu____803)))
end
| FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____806 = (FStar_Universal.load_interface_decls env intf.FStar_Interactive_JsonHelper.tf_fname)
in ((curmod), (uu____806)))
end
| FStar_Interactive_JsonHelper.PushFragment (frag) -> begin
(FStar_Universal.tc_one_fragment curmod env frag)
end
| FStar_Interactive_JsonHelper.Noop -> begin
((curmod), (env))
end))

type name_tracking_event =
| NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid)
| NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
| NTInclude of (FStar_Ident.lid * FStar_Ident.lid)
| NTBinding of (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding) FStar_Util.either


let uu___is_NTAlias : name_tracking_event  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NTAlias (_0) -> begin
true
end
| uu____862 -> begin
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
| uu____903 -> begin
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
| uu____938 -> begin
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
| uu____973 -> begin
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

let uu____1041 = (FStar_Ident.text_of_id id1)
in (

let uu____1043 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_alias table uu____1041 [] uu____1043)))
end
| uu____1045 -> begin
table
end)
end
| NTOpen (host, (included, kind)) -> begin
(match ((is_cur_mod host)) with
| true -> begin
(

let uu____1051 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_open table (Prims.op_Equality kind FStar_Syntax_DsEnv.Open_module) [] uu____1051))
end
| uu____1053 -> begin
table
end)
end
| NTInclude (host, included) -> begin
(

let uu____1057 = (match ((is_cur_mod host)) with
| true -> begin
[]
end
| uu____1060 -> begin
(query_of_lid host)
end)
in (

let uu____1062 = (query_of_lid included)
in (FStar_Interactive_CompletionTable.register_include table uu____1057 uu____1062)))
end
| NTBinding (binding) -> begin
(

let lids = (match (binding) with
| FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid (lid, uu____1074)) -> begin
(lid)::[]
end
| FStar_Util.Inr (lids, uu____1092) -> begin
lids
end
| uu____1097 -> begin
[]
end)
in (FStar_List.fold_left (fun tbl lid -> (

let ns_query = (match ((Prims.op_Equality lid.FStar_Ident.nsstr cur_mod_str)) with
| true -> begin
[]
end
| uu____1112 -> begin
(query_of_ids lid.FStar_Ident.ns)
end)
in (

let uu____1114 = (FStar_Ident.text_of_id lid.FStar_Ident.ident)
in (FStar_Interactive_CompletionTable.insert tbl ns_query uu____1114 lid)))) table lids))
end)))


let commit_name_tracking' : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Interactive_CompletionTable.table  ->  name_tracking_event Prims.list  ->  FStar_Interactive_CompletionTable.table = (fun cur_mod names1 name_events -> (

let cur_mod_str = (match (cur_mod) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (md) -> begin
(

let uu____1145 = (FStar_Syntax_Syntax.mod_name md)
in uu____1145.FStar_Ident.str)
end)
in (

let updater = (update_names_from_event cur_mod_str)
in (FStar_List.fold_left updater names1 name_events))))


let commit_name_tracking : FStar_Interactive_JsonHelper.repl_state  ->  name_tracking_event Prims.list  ->  FStar_Interactive_JsonHelper.repl_state = (fun st name_events -> (

let names1 = (commit_name_tracking' st.FStar_Interactive_JsonHelper.repl_curmod st.FStar_Interactive_JsonHelper.repl_names name_events)
in (

let uu___166_1171 = st
in {FStar_Interactive_JsonHelper.repl_line = uu___166_1171.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___166_1171.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___166_1171.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___166_1171.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___166_1171.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu___166_1171.FStar_Interactive_JsonHelper.repl_env; FStar_Interactive_JsonHelper.repl_stdin = uu___166_1171.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = names1})))


let fresh_name_tracking_hooks : unit  ->  (name_tracking_event Prims.list FStar_ST.ref * FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks) = (fun uu____1187 -> (

let events = (FStar_Util.mk_ref [])
in (

let push_event = (fun evt -> (

let uu____1201 = (

let uu____1204 = (FStar_ST.op_Bang events)
in (evt)::uu____1204)
in (FStar_ST.op_Colon_Equals events uu____1201)))
in ((events), ({FStar_Syntax_DsEnv.ds_push_open_hook = (fun dsenv1 op -> (

let uu____1265 = (

let uu____1266 = (

let uu____1271 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1271), (op)))
in NTOpen (uu____1266))
in (push_event uu____1265))); FStar_Syntax_DsEnv.ds_push_include_hook = (fun dsenv1 ns -> (

let uu____1277 = (

let uu____1278 = (

let uu____1283 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1283), (ns)))
in NTInclude (uu____1278))
in (push_event uu____1277))); FStar_Syntax_DsEnv.ds_push_module_abbrev_hook = (fun dsenv1 x l -> (

let uu____1291 = (

let uu____1292 = (

let uu____1299 = (FStar_Syntax_DsEnv.current_module dsenv1)
in ((uu____1299), (x), (l)))
in NTAlias (uu____1292))
in (push_event uu____1291)))}), ({FStar_TypeChecker_Env.tc_push_in_gamma_hook = (fun uu____1304 s -> (push_event (NTBinding (s))))})))))


let track_name_changes : FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t * (FStar_TypeChecker_Env.env_t  ->  (FStar_TypeChecker_Env.env_t * name_tracking_event Prims.list))) = (fun env -> (

let set_hooks = (fun dshooks tchooks env1 -> (

let uu____1358 = (FStar_Universal.with_dsenv_of_tcenv env1 (fun dsenv1 -> (

let uu____1366 = (FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks)
in ((()), (uu____1366)))))
in (match (uu____1358) with
| ((), tcenv') -> begin
(FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks)
end)))
in (

let uu____1368 = (

let uu____1373 = (FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv)
in (

let uu____1374 = (FStar_TypeChecker_Env.tc_hooks env)
in ((uu____1373), (uu____1374))))
in (match (uu____1368) with
| (old_dshooks, old_tchooks) -> begin
(

let uu____1390 = (fresh_name_tracking_hooks ())
in (match (uu____1390) with
| (events, new_dshooks, new_tchooks) -> begin
(

let uu____1425 = (set_hooks new_dshooks new_tchooks env)
in ((uu____1425), ((fun env1 -> (

let uu____1439 = (set_hooks old_dshooks old_tchooks env1)
in (

let uu____1440 = (

let uu____1443 = (FStar_ST.op_Bang events)
in (FStar_List.rev uu____1443))
in ((uu____1439), (uu____1440))))))))
end))
end))))


let repl_tx : FStar_Interactive_JsonHelper.repl_state  ->  push_kind  ->  FStar_Interactive_JsonHelper.repl_task  ->  (FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option * FStar_Interactive_JsonHelper.repl_state) = (fun st push_kind task -> (FStar_All.try_with (fun uu___202_1512 -> (match (()) with
| () -> begin
(

let st1 = (push_repl "repl_tx" push_kind task st)
in (

let uu____1521 = (track_name_changes st1.FStar_Interactive_JsonHelper.repl_env)
in (match (uu____1521) with
| (env, finish_name_tracking) -> begin
(

let uu____1561 = (run_repl_task st1.FStar_Interactive_JsonHelper.repl_curmod env task)
in (match (uu____1561) with
| (curmod, env1) -> begin
(

let st2 = (

let uu___228_1575 = st1
in {FStar_Interactive_JsonHelper.repl_line = uu___228_1575.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___228_1575.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___228_1575.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___228_1575.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = curmod; FStar_Interactive_JsonHelper.repl_env = env1; FStar_Interactive_JsonHelper.repl_stdin = uu___228_1575.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___228_1575.FStar_Interactive_JsonHelper.repl_names})
in (

let uu____1576 = (finish_name_tracking env1)
in (match (uu____1576) with
| (env2, name_events) -> begin
(

let uu____1595 = (commit_name_tracking st2 name_events)
in ((FStar_Pervasives_Native.None), (uu____1595)))
end)))
end))
end)))
end)) (fun uu___201_1601 -> (match (uu___201_1601) with
| FStar_All.Failure (msg) -> begin
(

let uu____1610 = (

let uu____1613 = (FStar_Interactive_JsonHelper.js_diag st.FStar_Interactive_JsonHelper.repl_fname msg FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____1613))
in ((uu____1610), (st)))
end
| FStar_Util.SigInt -> begin
((FStar_Util.print_error "[E] Interrupt");
((FStar_Pervasives_Native.None), (st));
)
end
| FStar_Errors.Error (e, msg, r) -> begin
(

let uu____1625 = (

let uu____1628 = (FStar_Interactive_JsonHelper.js_diag st.FStar_Interactive_JsonHelper.repl_fname msg (FStar_Pervasives_Native.Some (r)))
in FStar_Pervasives_Native.Some (uu____1628))
in ((uu____1625), (st)))
end
| FStar_Errors.Err (e, msg) -> begin
(

let uu____1635 = (

let uu____1638 = (FStar_Interactive_JsonHelper.js_diag st.FStar_Interactive_JsonHelper.repl_fname msg FStar_Pervasives_Native.None)
in FStar_Pervasives_Native.Some (uu____1638))
in ((uu____1635), (st)))
end
| FStar_Errors.Stop -> begin
((FStar_Util.print_error "[E] Stop");
((FStar_Pervasives_Native.None), (st));
)
end))))


let tf_of_fname : Prims.string  ->  FStar_Interactive_JsonHelper.timed_fname = (fun fname -> (

let uu____1653 = (FStar_Parser_ParseIt.get_file_last_modification_time fname)
in {FStar_Interactive_JsonHelper.tf_fname = fname; FStar_Interactive_JsonHelper.tf_modtime = uu____1653}))


let update_task_timestamps : FStar_Interactive_JsonHelper.repl_task  ->  FStar_Interactive_JsonHelper.repl_task = (fun uu___0_1659 -> (match (uu___0_1659) with
| FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) -> begin
(

let uu____1662 = (

let uu____1667 = (tf_of_fname intf.FStar_Interactive_JsonHelper.tf_fname)
in (

let uu____1668 = (tf_of_fname impl.FStar_Interactive_JsonHelper.tf_fname)
in ((uu____1667), (uu____1668))))
in FStar_Interactive_JsonHelper.LDInterleaved (uu____1662))
end
| FStar_Interactive_JsonHelper.LDSingle (intf_or_impl) -> begin
(

let uu____1670 = (tf_of_fname intf_or_impl.FStar_Interactive_JsonHelper.tf_fname)
in FStar_Interactive_JsonHelper.LDSingle (uu____1670))
end
| FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (intf) -> begin
(

let uu____1672 = (tf_of_fname intf.FStar_Interactive_JsonHelper.tf_fname)
in FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile (uu____1672))
end
| other -> begin
other
end))


let repl_ldtx : FStar_Interactive_JsonHelper.repl_state  ->  FStar_Interactive_JsonHelper.repl_task Prims.list  ->  either_replst = (fun st tasks -> (

let rec revert_many = (fun st1 uu___1_1709 -> (match (uu___1_1709) with
| [] -> begin
st1
end
| ((_id, (task, _st')))::entries -> begin
(

let st' = (pop_repl "repl_ldtx" st1)
in (

let dep_graph1 = (FStar_TypeChecker_Env.dep_graph st1.FStar_Interactive_JsonHelper.repl_env)
in (

let st'1 = (

let uu___260_1758 = st'
in (

let uu____1759 = (FStar_TypeChecker_Env.set_dep_graph st'.FStar_Interactive_JsonHelper.repl_env dep_graph1)
in {FStar_Interactive_JsonHelper.repl_line = uu___260_1758.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___260_1758.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___260_1758.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___260_1758.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___260_1758.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu____1759; FStar_Interactive_JsonHelper.repl_stdin = uu___260_1758.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___260_1758.FStar_Interactive_JsonHelper.repl_names}))
in (revert_many st'1 entries))))
end))
in (

let rec aux = (fun st1 tasks1 previous -> (match (((tasks1), (previous))) with
| ([], []) -> begin
FStar_Util.Inl (st1)
end
| ((task)::tasks2, []) -> begin
(

let timestamped_task = (update_task_timestamps task)
in (

let uu____1809 = (repl_tx st1 LaxCheck timestamped_task)
in (match (uu____1809) with
| (diag1, st2) -> begin
(match ((not ((FStar_Util.is_some diag1)))) with
| true -> begin
(

let uu____1831 = (

let uu___280_1832 = st2
in (

let uu____1833 = (FStar_ST.op_Bang repl_stack)
in {FStar_Interactive_JsonHelper.repl_line = uu___280_1832.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___280_1832.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___280_1832.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu____1833; FStar_Interactive_JsonHelper.repl_curmod = uu___280_1832.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu___280_1832.FStar_Interactive_JsonHelper.repl_env; FStar_Interactive_JsonHelper.repl_stdin = uu___280_1832.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___280_1832.FStar_Interactive_JsonHelper.repl_names}))
in (aux uu____1831 tasks2 []))
end
| uu____1863 -> begin
FStar_Util.Inr (st2)
end)
end)))
end
| ((task)::tasks2, (prev)::previous1) when (

let uu____1877 = (update_task_timestamps task)
in (Prims.op_Equality (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev)) uu____1877)) -> begin
(aux st1 tasks2 previous1)
end
| (tasks2, previous1) -> begin
(

let uu____1892 = (revert_many st1 previous1)
in (aux uu____1892 tasks2 []))
end))
in (aux st tasks (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)))))


let ld_deps : FStar_Interactive_JsonHelper.repl_state  ->  ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list), FStar_Interactive_JsonHelper.repl_state) FStar_Util.either = (fun st -> (FStar_All.try_with (fun uu___294_1937 -> (match (()) with
| () -> begin
(

let uu____1949 = (deps_and_repl_ld_tasks_of_our_file st.FStar_Interactive_JsonHelper.repl_fname)
in (match (uu____1949) with
| (deps, tasks, dep_graph1) -> begin
(

let st1 = (

let uu___304_1986 = st
in (

let uu____1987 = (FStar_TypeChecker_Env.set_dep_graph st.FStar_Interactive_JsonHelper.repl_env dep_graph1)
in {FStar_Interactive_JsonHelper.repl_line = uu___304_1986.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___304_1986.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___304_1986.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___304_1986.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___304_1986.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu____1987; FStar_Interactive_JsonHelper.repl_stdin = uu___304_1986.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = uu___304_1986.FStar_Interactive_JsonHelper.repl_names}))
in (

let uu____1988 = (repl_ldtx st1 tasks)
in (match (uu____1988) with
| FStar_Util.Inr (st2) -> begin
FStar_Util.Inr (st2)
end
| FStar_Util.Inl (st2) -> begin
FStar_Util.Inl (((st2), (deps)))
end)))
end))
end)) (fun uu___293_2021 -> ((FStar_Util.print_error "[E] Failed to load deps");
FStar_Util.Inr (st);
))))


let add_module_completions : Prims.string  ->  Prims.string Prims.list  ->  FStar_Interactive_CompletionTable.table  ->  FStar_Interactive_CompletionTable.table = (fun this_fname deps table -> (

let capitalize = (fun str -> (match ((Prims.op_Equality str "")) with
| true -> begin
str
end
| uu____2079 -> begin
(

let first = (FStar_String.substring str (Prims.parse_int "0") (Prims.parse_int "1"))
in (

let uu____2085 = (FStar_String.substring str (Prims.parse_int "1") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.op_Hat (FStar_String.uppercase first) uu____2085)))
end))
in (

let mods = (FStar_Parser_Dep.build_inclusion_candidates_list ())
in (

let loaded_mods_set = (

let uu____2102 = (FStar_Util.psmap_empty ())
in (

let uu____2107 = (

let uu____2111 = (FStar_Options.prims ())
in (uu____2111)::deps)
in (FStar_List.fold_left (fun acc dep1 -> (

let uu____2127 = (FStar_Parser_Dep.lowercase_module_name dep1)
in (FStar_Util.psmap_add acc uu____2127 true))) uu____2102 uu____2107)))
in (

let loaded = (fun modname -> (FStar_Util.psmap_find_default loaded_mods_set modname false))
in (

let this_mod_key = (FStar_Parser_Dep.lowercase_module_name this_fname)
in (FStar_List.fold_left (fun table1 uu____2156 -> (match (uu____2156) with
| (modname, mod_path) -> begin
(

let mod_key = (FStar_String.lowercase modname)
in (match ((Prims.op_Equality this_mod_key mod_key)) with
| true -> begin
table1
end
| uu____2173 -> begin
(

let ns_query = (

let uu____2179 = (capitalize modname)
in (FStar_Util.split uu____2179 "."))
in (

let uu____2182 = (loaded mod_key)
in (FStar_Interactive_CompletionTable.register_module_path table1 uu____2182 mod_path ns_query)))
end))
end)) table (FStar_List.rev mods))))))))


let full_lax : Prims.string  ->  FStar_Interactive_JsonHelper.repl_state  ->  (FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option * FStar_Interactive_JsonHelper.repl_state) = (fun text st -> ((FStar_TypeChecker_Env.toggle_id_info st.FStar_Interactive_JsonHelper.repl_env true);
(

let frag = {FStar_Parser_ParseIt.frag_fname = st.FStar_Interactive_JsonHelper.repl_fname; FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")}
in (

let uu____2214 = (ld_deps st)
in (match (uu____2214) with
| FStar_Util.Inl (st1, deps) -> begin
(

let names1 = (add_module_completions st1.FStar_Interactive_JsonHelper.repl_fname deps st1.FStar_Interactive_JsonHelper.repl_names)
in (repl_tx (

let uu___341_2250 = st1
in {FStar_Interactive_JsonHelper.repl_line = uu___341_2250.FStar_Interactive_JsonHelper.repl_line; FStar_Interactive_JsonHelper.repl_column = uu___341_2250.FStar_Interactive_JsonHelper.repl_column; FStar_Interactive_JsonHelper.repl_fname = uu___341_2250.FStar_Interactive_JsonHelper.repl_fname; FStar_Interactive_JsonHelper.repl_deps_stack = uu___341_2250.FStar_Interactive_JsonHelper.repl_deps_stack; FStar_Interactive_JsonHelper.repl_curmod = uu___341_2250.FStar_Interactive_JsonHelper.repl_curmod; FStar_Interactive_JsonHelper.repl_env = uu___341_2250.FStar_Interactive_JsonHelper.repl_env; FStar_Interactive_JsonHelper.repl_stdin = uu___341_2250.FStar_Interactive_JsonHelper.repl_stdin; FStar_Interactive_JsonHelper.repl_names = names1}) LaxCheck (FStar_Interactive_JsonHelper.PushFragment (frag))))
end
| FStar_Util.Inr (st1) -> begin
((FStar_Pervasives_Native.None), (st1))
end)));
))




