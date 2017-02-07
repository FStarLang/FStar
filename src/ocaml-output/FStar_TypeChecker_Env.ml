
open Prims
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____29 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_lid : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
true
end
| uu____43 -> begin
false
end))


let __proj__Binding_lid__item___0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
_0
end))


let uu___is_Binding_sig : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
true
end
| uu____64 -> begin
false
end))


let __proj__Binding_sig__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
_0
end))


let uu___is_Binding_univ : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
true
end
| uu____85 -> begin
false
end))


let __proj__Binding_univ__item___0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
_0
end))


let uu___is_Binding_sig_inst : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
true
end
| uu____101 -> begin
false
end))


let __proj__Binding_sig_inst__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
_0
end))

type delta_level =
| NoDelta
| Inlining
| Eager_unfolding_only
| Unfold of FStar_Syntax_Syntax.delta_depth


let uu___is_NoDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDelta -> begin
true
end
| uu____127 -> begin
false
end))


let uu___is_Inlining : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____131 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____135 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____140 -> begin
false
end))


let __proj__Unfold__item___0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
_0
end))


type mlift =
FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ}

type effects =
{decls : FStar_Syntax_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


type cached_elt =
((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ Prims.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) Prims.option} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; solve : (Prims.unit  ->  Prims.string) Prims.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list}


type implicits =
(Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| ((NoDelta, _)) | ((Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) | ((Unfold (_), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)) | ((Unfold (_), FStar_Syntax_Syntax.Visible_default)) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____773 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun uu____783 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache = (fun uu____791 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____830 = (new_gamma_cache ())
in (

let uu____832 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____830; modules = []; expected_typ = None; sigtab = uu____832; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____872 -> (

let uu____873 = (FStar_ST.read query_indices)
in (match (uu____873) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____887 -> begin
(

let uu____892 = (

let uu____897 = (

let uu____901 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____901))
in (

let uu____915 = (FStar_ST.read query_indices)
in (uu____897)::uu____915))
in (FStar_ST.write query_indices uu____892))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____937 -> (

let uu____938 = (FStar_ST.read query_indices)
in (match (uu____938) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.write query_indices tl)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____974 -> (match (uu____974) with
| (l, n) -> begin
(

let uu____979 = (FStar_ST.read query_indices)
in (match (uu____979) with
| (hd)::tl -> begin
(FStar_ST.write query_indices (((((l), (n)))::hd)::tl))
end
| uu____1013 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____1023 -> (

let uu____1024 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____1024)))


let commit_query_index_mark : Prims.unit  ->  Prims.unit = (fun uu____1040 -> (

let uu____1041 = (FStar_ST.read query_indices)
in (match (uu____1041) with
| (hd)::(uu____1053)::tl -> begin
(FStar_ST.write query_indices ((hd)::tl))
end
| uu____1080 -> begin
(failwith "Unmarked query index stack")
end)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____1094 = (

let uu____1096 = (FStar_ST.read stack)
in (env)::uu____1096)
in (FStar_ST.write stack uu____1094));
(

let uu___106_1104 = env
in (

let uu____1105 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____1107 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___106_1104.solver; range = uu___106_1104.range; curmodule = uu___106_1104.curmodule; gamma = uu___106_1104.gamma; gamma_cache = uu____1105; modules = uu___106_1104.modules; expected_typ = uu___106_1104.expected_typ; sigtab = uu____1107; is_pattern = uu___106_1104.is_pattern; instantiate_imp = uu___106_1104.instantiate_imp; effects = uu___106_1104.effects; generalize = uu___106_1104.generalize; letrecs = uu___106_1104.letrecs; top_level = uu___106_1104.top_level; check_uvars = uu___106_1104.check_uvars; use_eq = uu___106_1104.use_eq; is_iface = uu___106_1104.is_iface; admit = uu___106_1104.admit; lax = uu___106_1104.lax; lax_universes = uu___106_1104.lax_universes; type_of = uu___106_1104.type_of; universe_of = uu___106_1104.universe_of; use_bv_sorts = uu___106_1104.use_bv_sorts; qname_and_index = uu___106_1104.qname_and_index})));
))


let pop_stack : Prims.unit  ->  env = (fun uu____1111 -> (

let uu____1112 = (FStar_ST.read stack)
in (match (uu____1112) with
| (env)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____1124 -> begin
(failwith "Impossible: Too many pops")
end)))


let cleanup_interactive : env  ->  Prims.unit = (fun env -> (env.solver.pop ""))


let push : env  ->  Prims.string  ->  env = (fun env msg -> ((push_query_indices ());
(env.solver.push msg);
(push_stack env);
))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> ((env.solver.pop msg);
(pop_query_indices ());
(pop_stack ());
))


let mark : env  ->  env = (fun env -> ((env.solver.mark "USER MARK");
(push_query_indices ());
(push_stack env);
))


let commit_mark : env  ->  env = (fun env -> ((commit_query_index_mark ());
(env.solver.commit_mark "USER MARK");
(

let uu____1156 = (pop_stack ())
in ());
env;
))


let reset_mark : env  ->  env = (fun env -> ((env.solver.reset_mark "USER MARK");
(pop_query_indices ());
(pop_stack ());
))


let incr_query_index : env  ->  env = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| None -> begin
env
end
| Some (l, n) -> begin
(

let uu____1175 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1187 -> (match (uu____1187) with
| (m, uu____1191) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1175) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___107_1196 = env
in {solver = uu___107_1196.solver; range = uu___107_1196.range; curmodule = uu___107_1196.curmodule; gamma = uu___107_1196.gamma; gamma_cache = uu___107_1196.gamma_cache; modules = uu___107_1196.modules; expected_typ = uu___107_1196.expected_typ; sigtab = uu___107_1196.sigtab; is_pattern = uu___107_1196.is_pattern; instantiate_imp = uu___107_1196.instantiate_imp; effects = uu___107_1196.effects; generalize = uu___107_1196.generalize; letrecs = uu___107_1196.letrecs; top_level = uu___107_1196.top_level; check_uvars = uu___107_1196.check_uvars; use_eq = uu___107_1196.use_eq; is_iface = uu___107_1196.is_iface; admit = uu___107_1196.admit; lax = uu___107_1196.lax; lax_universes = uu___107_1196.lax_universes; type_of = uu___107_1196.type_of; universe_of = uu___107_1196.universe_of; use_bv_sorts = uu___107_1196.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1199, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___108_1205 = env
in {solver = uu___108_1205.solver; range = uu___108_1205.range; curmodule = uu___108_1205.curmodule; gamma = uu___108_1205.gamma; gamma_cache = uu___108_1205.gamma_cache; modules = uu___108_1205.modules; expected_typ = uu___108_1205.expected_typ; sigtab = uu___108_1205.sigtab; is_pattern = uu___108_1205.is_pattern; instantiate_imp = uu___108_1205.instantiate_imp; effects = uu___108_1205.effects; generalize = uu___108_1205.generalize; letrecs = uu___108_1205.letrecs; top_level = uu___108_1205.top_level; check_uvars = uu___108_1205.check_uvars; use_eq = uu___108_1205.use_eq; is_iface = uu___108_1205.is_iface; admit = uu___108_1205.admit; lax = uu___108_1205.lax; lax_universes = uu___108_1205.lax_universes; type_of = uu___108_1205.type_of; universe_of = uu___108_1205.universe_of; use_bv_sorts = uu___108_1205.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____1220 -> begin
(

let uu___109_1221 = e
in {solver = uu___109_1221.solver; range = r; curmodule = uu___109_1221.curmodule; gamma = uu___109_1221.gamma; gamma_cache = uu___109_1221.gamma_cache; modules = uu___109_1221.modules; expected_typ = uu___109_1221.expected_typ; sigtab = uu___109_1221.sigtab; is_pattern = uu___109_1221.is_pattern; instantiate_imp = uu___109_1221.instantiate_imp; effects = uu___109_1221.effects; generalize = uu___109_1221.generalize; letrecs = uu___109_1221.letrecs; top_level = uu___109_1221.top_level; check_uvars = uu___109_1221.check_uvars; use_eq = uu___109_1221.use_eq; is_iface = uu___109_1221.is_iface; admit = uu___109_1221.admit; lax = uu___109_1221.lax; lax_universes = uu___109_1221.lax_universes; type_of = uu___109_1221.type_of; universe_of = uu___109_1221.universe_of; use_bv_sorts = uu___109_1221.use_bv_sorts; qname_and_index = uu___109_1221.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___110_1238 = env
in {solver = uu___110_1238.solver; range = uu___110_1238.range; curmodule = lid; gamma = uu___110_1238.gamma; gamma_cache = uu___110_1238.gamma_cache; modules = uu___110_1238.modules; expected_typ = uu___110_1238.expected_typ; sigtab = uu___110_1238.sigtab; is_pattern = uu___110_1238.is_pattern; instantiate_imp = uu___110_1238.instantiate_imp; effects = uu___110_1238.effects; generalize = uu___110_1238.generalize; letrecs = uu___110_1238.letrecs; top_level = uu___110_1238.top_level; check_uvars = uu___110_1238.check_uvars; use_eq = uu___110_1238.use_eq; is_iface = uu___110_1238.is_iface; admit = uu___110_1238.admit; lax = uu___110_1238.lax; lax_universes = uu___110_1238.lax_universes; type_of = uu___110_1238.type_of; universe_of = uu___110_1238.universe_of; use_bv_sorts = uu___110_1238.use_bv_sorts; qname_and_index = uu___110_1238.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (

let uu____1260 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____1260)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1263 -> (

let uu____1264 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1264)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1287) -> begin
(

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (

let uu____1303 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____1303)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___93_1308 -> (match (uu___93_1308) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1322 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1332 = (inst_tscheme t)
in (match (uu____1332) with
| (us, t) -> begin
(

let uu____1339 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (uu____1339)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1351 -> (match (uu____1351) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs))) with
| true -> begin
(

let uu____1365 = (

let uu____1366 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (

let uu____1369 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____1372 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1373 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____1366 uu____1369 uu____1372 uu____1373)))))
in (failwith uu____1365))
end
| uu____1374 -> begin
()
end);
(

let uu____1375 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd uu____1375));
))
end
| uu____1379 -> begin
(

let uu____1380 = (

let uu____1381 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____1381))
in (failwith uu____1380))
end)
end))

type tri =
| Yes
| No
| Maybe


let uu___is_Yes : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Yes -> begin
true
end
| uu____1385 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1389 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1393 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1401 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], uu____1419) -> begin
Maybe
end
| (uu____1423, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| uu____1435 -> begin
No
end))
in (aux cur lns))))
end
| uu____1440 -> begin
No
end)
end)))


let lookup_qname : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes Prims.option)) FStar_Util.either Prims.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> ((FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t);
Some (t);
))
in (

let found = (match ((cur_mod <> No)) with
| true -> begin
(

let uu____1487 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1487) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___94_1504 -> (match (uu___94_1504) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____1523 = (

let uu____1531 = (inst_tscheme t)
in FStar_Util.Inl (uu____1531))
in Some (uu____1523))
end
| uu____1546 -> begin
None
end)
end
| Binding_sig (uu____1554, FStar_Syntax_Syntax.Sig_bundle (ses, uu____1556, uu____1557, uu____1558)) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1568 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1568) with
| true -> begin
(cache (FStar_Util.Inr (((se), (None)))))
end
| uu____1577 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1588) -> begin
Some (t)
end
| uu____1595 -> begin
(cache t)
end))
in (

let uu____1596 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1596) with
| true -> begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end
| uu____1612 -> begin
None
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1625 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1625) with
| true -> begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end
| uu____1648 -> begin
None
end))
end
| uu____1656 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1666 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1689 -> begin
(

let uu____1690 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1690) with
| true -> begin
(

let uu____1699 = (find_in_sigtab env lid)
in (match (uu____1699) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end))
end
| uu____1730 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1750, uu____1751, uu____1752) -> begin
(add_sigelts env ses)
end
| uu____1759 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1765) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1769 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___95_1785 -> (match (uu___95_1785) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| uu____1792 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____1807, (lb)::[]), uu____1809, uu____1810, uu____1811, uu____1812) -> begin
(

let uu____1823 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1823))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1831, lbs), uu____1833, uu____1834, uu____1835, uu____1836) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1854) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____1859 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1859) with
| true -> begin
(

let uu____1863 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1863))
end
| uu____1871 -> begin
None
end))
end)))
end
| uu____1874 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1887) -> begin
(

let uu____1888 = (

let uu____1891 = (

let uu____1892 = (

let uu____1895 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____1895))
in ((ne.FStar_Syntax_Syntax.univs), (uu____1892)))
in (inst_tscheme uu____1891))
in Some (uu____1888))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____1905, uu____1906, uu____1907, uu____1908) -> begin
(

let uu____1913 = (

let uu____1916 = (

let uu____1917 = (

let uu____1920 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____1920))
in ((us), (uu____1917)))
in (inst_tscheme uu____1916))
in Some (uu____1913))
end
| uu____1927 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun uu___96_1954 -> (match (uu___96_1954) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____1975, uvs, t, uu____1978, uu____1979, uu____1980, uu____1981, uu____1982), None) -> begin
(

let uu____1993 = (inst_tscheme ((uvs), (t)))
in Some (uu____1993))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, uu____2002), None) -> begin
(

let uu____2011 = (

let uu____2012 = (in_cur_mod env l)
in (uu____2012 = Yes))
in (match (uu____2011) with
| true -> begin
(

let uu____2016 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____2016) with
| true -> begin
(

let uu____2021 = (inst_tscheme ((uvs), (t)))
in Some (uu____2021))
end
| uu____2026 -> begin
None
end))
end
| uu____2029 -> begin
(

let uu____2030 = (inst_tscheme ((uvs), (t)))
in Some (uu____2030))
end))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2039, uu____2040, uu____2041, uu____2042), None) -> begin
(match (tps) with
| [] -> begin
(

let uu____2060 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) uu____2060))
end
| uu____2070 -> begin
(

let uu____2071 = (

let uu____2074 = (

let uu____2075 = (

let uu____2078 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2078))
in ((uvs), (uu____2075)))
in (inst_tscheme uu____2074))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____2071))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2094, uu____2095, uu____2096, uu____2097), Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____2116 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____2116))
end
| uu____2126 -> begin
(

let uu____2127 = (

let uu____2130 = (

let uu____2131 = (

let uu____2134 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2134))
in ((uvs), (uu____2131)))
in (inst_tscheme_with uu____2130 us))
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____2127))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (uu____2158), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2169 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (

let uu____2174 = (

let uu____2178 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____2178 mapper))
in (match (uu____2174) with
| Some (us, t) -> begin
Some (((us), ((

let uu___111_2211 = t
in {FStar_Syntax_Syntax.n = uu___111_2211.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___111_2211.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___111_2211.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2228 = (lookup_qname env l)
in (match (uu____2228) with
| None -> begin
false
end
| Some (uu____2244) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (

let uu____2265 = (try_lookup_bv env bv)
in (match (uu____2265) with
| None -> begin
(

let uu____2271 = (

let uu____2272 = (

let uu____2275 = (variable_not_found bv)
in (

let uu____2276 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____2275), (uu____2276))))
in FStar_Errors.Error (uu____2272))
in (Prims.raise uu____2271))
end
| Some (t) -> begin
(

let uu____2282 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range uu____2282 t))
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (

let uu____2292 = (try_lookup_lid_aux env l)
in (match (uu____2292) with
| None -> begin
None
end
| Some (us, t) -> begin
(

let uu____2317 = (

let uu____2320 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (uu____2320)))
in Some (uu____2317))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (

let uu____2331 = (try_lookup_lid env l)
in (match (uu____2331) with
| None -> begin
(

let uu____2339 = (

let uu____2340 = (

let uu____2343 = (name_not_found l)
in ((uu____2343), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____2340))
in (Prims.raise uu____2339))
end
| Some (us, t) -> begin
((us), (t))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___97_2357 -> (match (uu___97_2357) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2359 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2370 = (lookup_qname env lid)
in (match (uu____2370) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2383, uvs, t, q, uu____2387), None)) -> begin
(

let uu____2403 = (

let uu____2409 = (

let uu____2412 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____2412)))
in ((uu____2409), (q)))
in Some (uu____2403))
end
| uu____2421 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2441 = (lookup_qname env lid)
in (match (uu____2441) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2452, uvs, t, uu____2455, uu____2456), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2472 -> begin
(

let uu____2481 = (

let uu____2482 = (

let uu____2485 = (name_not_found lid)
in ((uu____2485), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2482))
in (Prims.raise uu____2481))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2496 = (lookup_qname env lid)
in (match (uu____2496) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2507, uvs, t, uu____2510, uu____2511, uu____2512, uu____2513, uu____2514), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2532 -> begin
(

let uu____2541 = (

let uu____2542 = (

let uu____2545 = (name_not_found lid)
in ((uu____2545), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2542))
in (Prims.raise uu____2541))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____2557 = (lookup_qname env lid)
in (match (uu____2557) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2569, uu____2570, uu____2571, uu____2572, uu____2573, dcs, uu____2575, uu____2576), uu____2577)) -> begin
((true), (dcs))
end
| uu____2599 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____2615 = (lookup_qname env lid)
in (match (uu____2615) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2624, uu____2625, uu____2626, l, uu____2628, uu____2629, uu____2630, uu____2631), uu____2632)) -> begin
l
end
| uu____2651 -> begin
(

let uu____2660 = (

let uu____2661 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____2661))
in (failwith uu____2660))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____2685 = (lookup_qname env lid)
in (match (uu____2685) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____2714, lbs), uu____2716, uu____2717, quals, uu____2719) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2736 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2736) with
| true -> begin
(

let uu____2741 = (

let uu____2745 = (

let uu____2746 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) uu____2746))
in ((lb.FStar_Syntax_Syntax.lbunivs), (uu____2745)))
in Some (uu____2741))
end
| uu____2751 -> begin
None
end)))))
end
| uu____2755 -> begin
None
end)
end
| uu____2758 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____2777 = (lookup_qname env ftv)
in (match (uu____2777) with
| Some (FStar_Util.Inr (se, None)) -> begin
(

let uu____2801 = (effect_signature se)
in (match (uu____2801) with
| None -> begin
None
end
| Some (uu____2808, t) -> begin
(

let uu____2812 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (uu____2812))
end))
end
| uu____2813 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____2828 = (try_lookup_effect_lid env ftv)
in (match (uu____2828) with
| None -> begin
(

let uu____2830 = (

let uu____2831 = (

let uu____2834 = (name_not_found ftv)
in ((uu____2834), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____2831))
in (Prims.raise uu____2830))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____2848 = (lookup_qname env lid0)
in (match (uu____2848) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, uu____2865, uu____2866), None)) -> begin
(

let lid = (

let uu____2885 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____2885))
in (

let uu____2886 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_2888 -> (match (uu___98_2888) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____2889 -> begin
false
end))))
in (match (uu____2886) with
| true -> begin
None
end
| uu____2895 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs))) with
| true -> begin
univ_insts
end
| uu____2901 -> begin
(match (((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____2904 -> begin
(

let uu____2905 = (

let uu____2906 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____2907 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" uu____2906 uu____2907)))
in (failwith uu____2905))
end)
end)
in (match (((binders), (univs))) with
| ([], uu____2913) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____2922, (uu____2923)::(uu____2924)::uu____2925) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(

let uu____2928 = (

let uu____2929 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____2930 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____2929 uu____2930)))
in (failwith uu____2928))
end
| uu____2936 -> begin
(

let uu____2939 = (

let uu____2942 = (

let uu____2943 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (uu____2943)))
in (inst_tscheme_with uu____2942 insts))
in (match (uu____2939) with
| (uu____2951, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (

let uu____2954 = (

let uu____2955 = (FStar_Syntax_Subst.compress t)
in uu____2955.FStar_Syntax_Syntax.n)
in (match (uu____2954) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| uu____2985 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____2989 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (

let uu____3013 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)
in (match (uu____3013) with
| None -> begin
None
end
| Some (uu____3020, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____3025 = (find l)
in (match (uu____3025) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____3030 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____3030) with
| Some (l) -> begin
l
end
| None -> begin
(

let uu____3033 = (find l)
in (match (uu____3033) with
| None -> begin
l
end
| Some (m) -> begin
((FStar_Util.smap_add cache l.FStar_Ident.str m);
m;
)
end))
end))
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l = (norm_eff_name env l)
in (

let uu____3045 = (lookup_qname env l)
in (match (uu____3045) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3056), uu____3057)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____3072 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____3093 -> (

let uu____3094 = (

let uu____3095 = (FStar_Util.string_of_int i)
in (

let uu____3096 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____3095 uu____3096)))
in (failwith uu____3094)))
in (

let uu____3097 = (lookup_datacon env lid)
in (match (uu____3097) with
| (uu____3100, t) -> begin
(

let uu____3102 = (

let uu____3103 = (FStar_Syntax_Subst.compress t)
in uu____3103.FStar_Syntax_Syntax.n)
in (match (uu____3102) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3107) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____3122 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____3128 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right uu____3128 Prims.fst)))
end)
end
| uu____3133 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____3140 = (lookup_qname env l)
in (match (uu____3140) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____3149, uu____3150, uu____3151, quals, uu____3153), uu____3154)) -> begin
(FStar_Util.for_some (fun uu___99_3171 -> (match (uu___99_3171) with
| FStar_Syntax_Syntax.Projector (uu____3172) -> begin
true
end
| uu____3175 -> begin
false
end)) quals)
end
| uu____3176 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3191 = (lookup_qname env lid)
in (match (uu____3191) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____3200, uu____3201, uu____3202, uu____3203, uu____3204, uu____3205, uu____3206, uu____3207), uu____3208)) -> begin
true
end
| uu____3227 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3242 = (lookup_qname env lid)
in (match (uu____3242) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3251, uu____3252, uu____3253, uu____3254, uu____3255, uu____3256, tags, uu____3258), uu____3259)) -> begin
(FStar_Util.for_some (fun uu___100_3280 -> (match (uu___100_3280) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3283 -> begin
false
end)) tags)
end
| uu____3284 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3299 = (lookup_qname env lid)
in (match (uu____3299) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (uu____3308, uu____3309, uu____3310, tags, uu____3312), uu____3313)) -> begin
(FStar_Util.for_some (fun uu___101_3334 -> (match (uu___101_3334) with
| FStar_Syntax_Syntax.Action (uu____3335) -> begin
true
end
| uu____3336 -> begin
false
end)) tags)
end
| uu____3337 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (

let uu____3354 = (

let uu____3355 = (FStar_Syntax_Util.un_uinst head)
in uu____3355.FStar_Syntax_Syntax.n)
in (match (uu____3354) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3359 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun uu___102_3377 -> (match (uu___102_3377) with
| FStar_Util.Inl (uu____3386) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____3395) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3404, uu____3405, uu____3406, qs, uu____3408) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3411) -> begin
Some (true)
end
| uu____3423 -> begin
Some (false)
end)
end))
in (

let uu____3424 = (

let uu____3426 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____3426 mapper))
in (match (uu____3424) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____3449 = (lookup_qname env lid)
in (match (uu____3449) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3458, uu____3459, tps, uu____3461, uu____3462, uu____3463, uu____3464, uu____3465), uu____3466)) -> begin
(FStar_List.length tps)
end
| uu____3490 -> begin
(

let uu____3499 = (

let uu____3500 = (

let uu____3503 = (name_not_found lid)
in ((uu____3503), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____3500))
in (Prims.raise uu____3499))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____3520 = (effect_decl_opt env l)
in (match (uu____3520) with
| None -> begin
(

let uu____3522 = (

let uu____3523 = (

let uu____3526 = (name_not_found l)
in ((uu____3526), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3523))
in (Prims.raise uu____3522))
end
| Some (md) -> begin
md
end)))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3574 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3598 -> begin
(

let uu____3599 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____3623 -> (match (uu____3623) with
| (m1, m2, uu____3631, uu____3632, uu____3633) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____3599) with
| None -> begin
(

let uu____3650 = (

let uu____3651 = (

let uu____3654 = (

let uu____3655 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____3656 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____3655 uu____3656)))
in ((uu____3654), (env.range)))
in FStar_Errors.Error (uu____3651))
in (Prims.raise uu____3650))
end
| Some (uu____3668, uu____3669, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end
| uu____3700 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____3716 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____3716) with
| None -> begin
(

let uu____3725 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____3725))
end
| Some (md) -> begin
(

let uu____3731 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____3731) with
| (uu____3738, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____3746))::((wp, uu____3748))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____3770 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (Some (res_u)))
end
| uu____3797 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (Some (res_u)))
end
| uu____3798 -> begin
(

let eff_name = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____3805 = (get_range env)
in (

let uu____3806 = (

let uu____3809 = (

let uu____3810 = (

let uu____3820 = (

let uu____3822 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____3822)::[])
in ((null_wp), (uu____3820)))
in FStar_Syntax_Syntax.Tm_app (uu____3810))
in (FStar_Syntax_Syntax.mk uu____3809))
in (uu____3806 None uu____3805)))
in (

let uu____3832 = (

let uu____3833 = (

let uu____3839 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____3839)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____3833; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____3832))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3847) -> begin
(

let effects = (

let uu___112_3849 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___112_3849.order; joins = uu___112_3849.joins})
in (

let uu___113_3850 = env
in {solver = uu___113_3850.solver; range = uu___113_3850.range; curmodule = uu___113_3850.curmodule; gamma = uu___113_3850.gamma; gamma_cache = uu___113_3850.gamma_cache; modules = uu___113_3850.modules; expected_typ = uu___113_3850.expected_typ; sigtab = uu___113_3850.sigtab; is_pattern = uu___113_3850.is_pattern; instantiate_imp = uu___113_3850.instantiate_imp; effects = effects; generalize = uu___113_3850.generalize; letrecs = uu___113_3850.letrecs; top_level = uu___113_3850.top_level; check_uvars = uu___113_3850.check_uvars; use_eq = uu___113_3850.use_eq; is_iface = uu___113_3850.is_iface; admit = uu___113_3850.admit; lax = uu___113_3850.lax; lax_universes = uu___113_3850.lax_universes; type_of = uu___113_3850.type_of; universe_of = uu___113_3850.universe_of; use_bv_sorts = uu___113_3850.use_bv_sorts; qname_and_index = uu___113_3850.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, uu____3852) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (

let uu____3862 = (e1.mlift r wp1)
in (e2.mlift r uu____3862)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let uu____3875 = (inst_tscheme lift_t)
in (match (uu____3875) with
| (uu____3880, lift_t) -> begin
(

let uu____3882 = (

let uu____3885 = (

let uu____3886 = (

let uu____3896 = (

let uu____3898 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____3899 = (

let uu____3901 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3901)::[])
in (uu____3898)::uu____3899))
in ((lift_t), (uu____3896)))
in FStar_Syntax_Syntax.Tm_app (uu____3886))
in (FStar_Syntax_Syntax.mk uu____3885))
in (uu____3882 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_lift_wp = (match (sub.FStar_Syntax_Syntax.lift_wp) with
| Some (sub_lift_wp) -> begin
sub_lift_wp
end
| None -> begin
(failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (mk_lift sub_lift_wp)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (

let uu____3935 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____3935 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (

let uu____3937 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____3937 FStar_Syntax_Syntax.Delta_constant None))
in (

let uu____3938 = (l arg wp)
in (FStar_Syntax_Print.term_to_string uu____3938)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order uu____3956 -> (match (uu____3956) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_32 -> Some (_0_32)))
end
| uu____3965 -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (

let uu____3977 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____3983 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____3988 -> begin
(

let uu____3989 = (

let uu____3994 = (find_edge order ((i), (k)))
in (

let uu____3996 = (find_edge order ((k), (j)))
in ((uu____3994), (uu____3996))))
in (match (uu____3989) with
| (Some (e1), Some (e2)) -> begin
(

let uu____4005 = (compose_edges e1 e2)
in (uu____4005)::[])
end
| uu____4006 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order uu____3977))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in ((FStar_All.pipe_right order (FStar_List.iter (fun edge -> (

let uu____4018 = ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (

let uu____4019 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right uu____4019 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____4018) with
| true -> begin
(

let uu____4022 = (

let uu____4023 = (

let uu____4026 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (

let uu____4027 = (get_range env)
in ((uu____4026), (uu____4027))))
in FStar_Errors.Error (uu____4023))
in (Prims.raise uu____4022))
end
| uu____4028 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____4122 = (

let uu____4127 = (find_edge order ((i), (k)))
in (

let uu____4129 = (find_edge order ((j), (k)))
in ((uu____4127), (uu____4129))))
in (match (uu____4122) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____4152, uu____4153) -> begin
(

let uu____4157 = ((

let uu____4158 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some uu____4158)) && (

let uu____4160 = (

let uu____4161 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some uu____4161))
in (not (uu____4160))))
in (match (uu____4157) with
| true -> begin
Some (((k), (ik), (jk)))
end
| uu____4170 -> begin
bopt
end))
end)
end
| uu____4171 -> begin
bopt
end))) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___114_4250 = env.effects
in {decls = uu___114_4250.decls; order = order; joins = joins})
in (

let uu___115_4251 = env
in {solver = uu___115_4251.solver; range = uu___115_4251.range; curmodule = uu___115_4251.curmodule; gamma = uu___115_4251.gamma; gamma_cache = uu___115_4251.gamma_cache; modules = uu___115_4251.modules; expected_typ = uu___115_4251.expected_typ; sigtab = uu___115_4251.sigtab; is_pattern = uu___115_4251.is_pattern; instantiate_imp = uu___115_4251.instantiate_imp; effects = effects; generalize = uu___115_4251.generalize; letrecs = uu___115_4251.letrecs; top_level = uu___115_4251.top_level; check_uvars = uu___115_4251.check_uvars; use_eq = uu___115_4251.use_eq; is_iface = uu___115_4251.is_iface; admit = uu___115_4251.admit; lax = uu___115_4251.lax; lax_universes = uu___115_4251.lax_universes; type_of = uu___115_4251.type_of; universe_of = uu___115_4251.universe_of; use_bv_sorts = uu___115_4251.use_bv_sorts; qname_and_index = uu___115_4251.qname_and_index})));
))))))))))))
end
| uu____4252 -> begin
env
end))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push = (fun x rest -> (match (rest) with
| ((Binding_sig (_))::_) | ((Binding_sig_inst (_))::_) -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest -> begin
(

let uu____4277 = (push x rest)
in (local)::uu____4277)
end))
in (

let uu___116_4279 = env
in (

let uu____4280 = (push s env.gamma)
in {solver = uu___116_4279.solver; range = uu___116_4279.range; curmodule = uu___116_4279.curmodule; gamma = uu____4280; gamma_cache = uu___116_4279.gamma_cache; modules = uu___116_4279.modules; expected_typ = uu___116_4279.expected_typ; sigtab = uu___116_4279.sigtab; is_pattern = uu___116_4279.is_pattern; instantiate_imp = uu___116_4279.instantiate_imp; effects = uu___116_4279.effects; generalize = uu___116_4279.generalize; letrecs = uu___116_4279.letrecs; top_level = uu___116_4279.top_level; check_uvars = uu___116_4279.check_uvars; use_eq = uu___116_4279.use_eq; is_iface = uu___116_4279.is_iface; admit = uu___116_4279.admit; lax = uu___116_4279.lax; lax_universes = uu___116_4279.lax_universes; type_of = uu___116_4279.type_of; universe_of = uu___116_4279.universe_of; use_bv_sorts = uu___116_4279.use_bv_sorts; qname_and_index = uu___116_4279.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___117_4307 = env
in {solver = uu___117_4307.solver; range = uu___117_4307.range; curmodule = uu___117_4307.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___117_4307.gamma_cache; modules = uu___117_4307.modules; expected_typ = uu___117_4307.expected_typ; sigtab = uu___117_4307.sigtab; is_pattern = uu___117_4307.is_pattern; instantiate_imp = uu___117_4307.instantiate_imp; effects = uu___117_4307.effects; generalize = uu___117_4307.generalize; letrecs = uu___117_4307.letrecs; top_level = uu___117_4307.top_level; check_uvars = uu___117_4307.check_uvars; use_eq = uu___117_4307.use_eq; is_iface = uu___117_4307.is_iface; admit = uu___117_4307.admit; lax = uu___117_4307.lax; lax_universes = uu___117_4307.lax_universes; type_of = uu___117_4307.type_of; universe_of = uu___117_4307.universe_of; use_bv_sorts = uu___117_4307.use_bv_sorts; qname_and_index = uu___117_4307.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env uu____4323 -> (match (uu____4323) with
| (x, uu____4327) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let x = (

let uu___118_4347 = x
in {FStar_Syntax_Syntax.ppname = uu___118_4347.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_4347.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___119_4377 = env
in {solver = uu___119_4377.solver; range = uu___119_4377.range; curmodule = uu___119_4377.curmodule; gamma = []; gamma_cache = uu___119_4377.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___119_4377.sigtab; is_pattern = uu___119_4377.is_pattern; instantiate_imp = uu___119_4377.instantiate_imp; effects = uu___119_4377.effects; generalize = uu___119_4377.generalize; letrecs = uu___119_4377.letrecs; top_level = uu___119_4377.top_level; check_uvars = uu___119_4377.check_uvars; use_eq = uu___119_4377.use_eq; is_iface = uu___119_4377.is_iface; admit = uu___119_4377.admit; lax = uu___119_4377.lax; lax_universes = uu___119_4377.lax_universes; type_of = uu___119_4377.type_of; universe_of = uu___119_4377.universe_of; use_bv_sorts = uu___119_4377.use_bv_sorts; qname_and_index = uu___119_4377.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___120_4392 = env
in {solver = uu___120_4392.solver; range = uu___120_4392.range; curmodule = uu___120_4392.curmodule; gamma = uu___120_4392.gamma; gamma_cache = uu___120_4392.gamma_cache; modules = uu___120_4392.modules; expected_typ = Some (t); sigtab = uu___120_4392.sigtab; is_pattern = uu___120_4392.is_pattern; instantiate_imp = uu___120_4392.instantiate_imp; effects = uu___120_4392.effects; generalize = uu___120_4392.generalize; letrecs = uu___120_4392.letrecs; top_level = uu___120_4392.top_level; check_uvars = uu___120_4392.check_uvars; use_eq = false; is_iface = uu___120_4392.is_iface; admit = uu___120_4392.admit; lax = uu___120_4392.lax; lax_universes = uu___120_4392.lax_universes; type_of = uu___120_4392.type_of; universe_of = uu___120_4392.universe_of; use_bv_sorts = uu___120_4392.use_bv_sorts; qname_and_index = uu___120_4392.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env_ -> (

let uu____4408 = (expected_typ env_)
in (((

let uu___121_4411 = env_
in {solver = uu___121_4411.solver; range = uu___121_4411.range; curmodule = uu___121_4411.curmodule; gamma = uu___121_4411.gamma; gamma_cache = uu___121_4411.gamma_cache; modules = uu___121_4411.modules; expected_typ = None; sigtab = uu___121_4411.sigtab; is_pattern = uu___121_4411.is_pattern; instantiate_imp = uu___121_4411.instantiate_imp; effects = uu___121_4411.effects; generalize = uu___121_4411.generalize; letrecs = uu___121_4411.letrecs; top_level = uu___121_4411.top_level; check_uvars = uu___121_4411.check_uvars; use_eq = false; is_iface = uu___121_4411.is_iface; admit = uu___121_4411.admit; lax = uu___121_4411.lax; lax_universes = uu___121_4411.lax_universes; type_of = uu___121_4411.type_of; universe_of = uu___121_4411.universe_of; use_bv_sorts = uu___121_4411.use_bv_sorts; qname_and_index = uu___121_4411.qname_and_index})), (uu____4408))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(

let uu____4422 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___103_4426 -> (match (uu___103_4426) with
| Binding_sig (uu____4428, se) -> begin
(se)::[]
end
| uu____4432 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4422 FStar_List.rev))
end
| uu____4435 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___122_4437 = env
in {solver = uu___122_4437.solver; range = uu___122_4437.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___122_4437.gamma_cache; modules = (m)::env.modules; expected_typ = uu___122_4437.expected_typ; sigtab = uu___122_4437.sigtab; is_pattern = uu___122_4437.is_pattern; instantiate_imp = uu___122_4437.instantiate_imp; effects = uu___122_4437.effects; generalize = uu___122_4437.generalize; letrecs = uu___122_4437.letrecs; top_level = uu___122_4437.top_level; check_uvars = uu___122_4437.check_uvars; use_eq = uu___122_4437.use_eq; is_iface = uu___122_4437.is_iface; admit = uu___122_4437.admit; lax = uu___122_4437.lax; lax_universes = uu___122_4437.lax_universes; type_of = uu___122_4437.type_of; universe_of = uu___122_4437.universe_of; use_bv_sorts = uu___122_4437.use_bv_sorts; qname_and_index = uu___122_4437.qname_and_index});
))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Syntax.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (uu____4487))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4502 = (

let uu____4506 = (FStar_Syntax_Free.uvars t)
in (ext out uu____4506))
in (aux uu____4502 tl))
end
| ((Binding_sig (_))::_) | ((Binding_sig_inst (_))::_) -> begin
out
end))
in (aux no_uvs env.gamma)))))


let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (

let no_univs = FStar_Syntax_Syntax.no_universe_uvars
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| ((Binding_sig_inst (_))::tl) | ((Binding_univ (_))::tl) -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4562 = (

let uu____4564 = (FStar_Syntax_Free.univs t)
in (ext out uu____4564))
in (aux uu____4562 tl))
end
| (Binding_sig (uu____4566))::uu____4567 -> begin
out
end))
in (aux no_univs env.gamma)))))


let univnames : env  ->  FStar_Syntax_Syntax.univ_name FStar_Util.set = (fun env -> (

let no_univ_names = FStar_Syntax_Syntax.no_universe_names
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____4604))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(

let uu____4614 = (FStar_Util.set_add uname out)
in (aux uu____4614 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4628 = (

let uu____4630 = (FStar_Syntax_Free.univnames t)
in (ext out uu____4630))
in (aux uu____4628 tl))
end
| (Binding_sig (uu____4632))::uu____4633 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___104_4649 -> (match (uu___104_4649) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____4661 = (

let uu____4663 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____4663 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____4661 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___105_4714 -> (match (uu___105_4714) with
| Binding_sig (lids, uu____4718) -> begin
(FStar_List.append lids keys)
end
| uu____4721 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____4723 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun uu____4727 -> ()); push = (fun uu____4728 -> ()); pop = (fun uu____4729 -> ()); mark = (fun uu____4730 -> ()); reset_mark = (fun uu____4731 -> ()); commit_mark = (fun uu____4732 -> ()); encode_modul = (fun uu____4733 uu____4734 -> ()); encode_sig = (fun uu____4735 uu____4736 -> ()); solve = (fun uu____4737 uu____4738 uu____4739 -> ()); is_trivial = (fun uu____4743 uu____4744 -> false); finish = (fun uu____4745 -> ()); refresh = (fun uu____4746 -> ())}




