
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
{mlift_wp : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ; mlift_term : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) Prims.option}

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}

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
| uu____807 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab = (fun uu____817 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache = (fun uu____825 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (

let uu____864 = (new_gamma_cache ())
in (

let uu____866 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____864; modules = []; expected_typ = None; sigtab = uu____866; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____906 -> (

let uu____907 = (FStar_ST.read query_indices)
in (match (uu____907) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____921 -> begin
(

let uu____926 = (

let uu____931 = (

let uu____935 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____935))
in (

let uu____949 = (FStar_ST.read query_indices)
in (uu____931)::uu____949))
in (FStar_ST.write query_indices uu____926))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____971 -> (

let uu____972 = (FStar_ST.read query_indices)
in (match (uu____972) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.write query_indices tl)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____1008 -> (match (uu____1008) with
| (l, n) -> begin
(

let uu____1013 = (FStar_ST.read query_indices)
in (match (uu____1013) with
| (hd)::tl -> begin
(FStar_ST.write query_indices (((((l), (n)))::hd)::tl))
end
| uu____1047 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____1057 -> (

let uu____1058 = (FStar_ST.read query_indices)
in (FStar_List.hd uu____1058)))


let commit_query_index_mark : Prims.unit  ->  Prims.unit = (fun uu____1074 -> (

let uu____1075 = (FStar_ST.read query_indices)
in (match (uu____1075) with
| (hd)::(uu____1087)::tl -> begin
(FStar_ST.write query_indices ((hd)::tl))
end
| uu____1114 -> begin
(failwith "Unmarked query index stack")
end)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____1128 = (

let uu____1130 = (FStar_ST.read stack)
in (env)::uu____1130)
in (FStar_ST.write stack uu____1128));
(

let uu___106_1138 = env
in (

let uu____1139 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____1141 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___106_1138.solver; range = uu___106_1138.range; curmodule = uu___106_1138.curmodule; gamma = uu___106_1138.gamma; gamma_cache = uu____1139; modules = uu___106_1138.modules; expected_typ = uu___106_1138.expected_typ; sigtab = uu____1141; is_pattern = uu___106_1138.is_pattern; instantiate_imp = uu___106_1138.instantiate_imp; effects = uu___106_1138.effects; generalize = uu___106_1138.generalize; letrecs = uu___106_1138.letrecs; top_level = uu___106_1138.top_level; check_uvars = uu___106_1138.check_uvars; use_eq = uu___106_1138.use_eq; is_iface = uu___106_1138.is_iface; admit = uu___106_1138.admit; lax = uu___106_1138.lax; lax_universes = uu___106_1138.lax_universes; type_of = uu___106_1138.type_of; universe_of = uu___106_1138.universe_of; use_bv_sorts = uu___106_1138.use_bv_sorts; qname_and_index = uu___106_1138.qname_and_index})));
))


let pop_stack : Prims.unit  ->  env = (fun uu____1145 -> (

let uu____1146 = (FStar_ST.read stack)
in (match (uu____1146) with
| (env)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____1158 -> begin
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

let uu____1190 = (pop_stack ())
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

let uu____1209 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1221 -> (match (uu____1221) with
| (m, uu____1225) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1209) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___107_1230 = env
in {solver = uu___107_1230.solver; range = uu___107_1230.range; curmodule = uu___107_1230.curmodule; gamma = uu___107_1230.gamma; gamma_cache = uu___107_1230.gamma_cache; modules = uu___107_1230.modules; expected_typ = uu___107_1230.expected_typ; sigtab = uu___107_1230.sigtab; is_pattern = uu___107_1230.is_pattern; instantiate_imp = uu___107_1230.instantiate_imp; effects = uu___107_1230.effects; generalize = uu___107_1230.generalize; letrecs = uu___107_1230.letrecs; top_level = uu___107_1230.top_level; check_uvars = uu___107_1230.check_uvars; use_eq = uu___107_1230.use_eq; is_iface = uu___107_1230.is_iface; admit = uu___107_1230.admit; lax = uu___107_1230.lax; lax_universes = uu___107_1230.lax_universes; type_of = uu___107_1230.type_of; universe_of = uu___107_1230.universe_of; use_bv_sorts = uu___107_1230.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1233, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___108_1239 = env
in {solver = uu___108_1239.solver; range = uu___108_1239.range; curmodule = uu___108_1239.curmodule; gamma = uu___108_1239.gamma; gamma_cache = uu___108_1239.gamma_cache; modules = uu___108_1239.modules; expected_typ = uu___108_1239.expected_typ; sigtab = uu___108_1239.sigtab; is_pattern = uu___108_1239.is_pattern; instantiate_imp = uu___108_1239.instantiate_imp; effects = uu___108_1239.effects; generalize = uu___108_1239.generalize; letrecs = uu___108_1239.letrecs; top_level = uu___108_1239.top_level; check_uvars = uu___108_1239.check_uvars; use_eq = uu___108_1239.use_eq; is_iface = uu___108_1239.is_iface; admit = uu___108_1239.admit; lax = uu___108_1239.lax; lax_universes = uu___108_1239.lax_universes; type_of = uu___108_1239.type_of; universe_of = uu___108_1239.universe_of; use_bv_sorts = uu___108_1239.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____1254 -> begin
(

let uu___109_1255 = e
in {solver = uu___109_1255.solver; range = r; curmodule = uu___109_1255.curmodule; gamma = uu___109_1255.gamma; gamma_cache = uu___109_1255.gamma_cache; modules = uu___109_1255.modules; expected_typ = uu___109_1255.expected_typ; sigtab = uu___109_1255.sigtab; is_pattern = uu___109_1255.is_pattern; instantiate_imp = uu___109_1255.instantiate_imp; effects = uu___109_1255.effects; generalize = uu___109_1255.generalize; letrecs = uu___109_1255.letrecs; top_level = uu___109_1255.top_level; check_uvars = uu___109_1255.check_uvars; use_eq = uu___109_1255.use_eq; is_iface = uu___109_1255.is_iface; admit = uu___109_1255.admit; lax = uu___109_1255.lax; lax_universes = uu___109_1255.lax_universes; type_of = uu___109_1255.type_of; universe_of = uu___109_1255.universe_of; use_bv_sorts = uu___109_1255.use_bv_sorts; qname_and_index = uu___109_1255.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___110_1272 = env
in {solver = uu___110_1272.solver; range = uu___110_1272.range; curmodule = lid; gamma = uu___110_1272.gamma; gamma_cache = uu___110_1272.gamma_cache; modules = uu___110_1272.modules; expected_typ = uu___110_1272.expected_typ; sigtab = uu___110_1272.sigtab; is_pattern = uu___110_1272.is_pattern; instantiate_imp = uu___110_1272.instantiate_imp; effects = uu___110_1272.effects; generalize = uu___110_1272.generalize; letrecs = uu___110_1272.letrecs; top_level = uu___110_1272.top_level; check_uvars = uu___110_1272.check_uvars; use_eq = uu___110_1272.use_eq; is_iface = uu___110_1272.is_iface; admit = uu___110_1272.admit; lax = uu___110_1272.lax; lax_universes = uu___110_1272.lax_universes; type_of = uu___110_1272.type_of; universe_of = uu___110_1272.universe_of; use_bv_sorts = uu___110_1272.use_bv_sorts; qname_and_index = uu___110_1272.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (

let uu____1294 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____1294)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1297 -> (

let uu____1298 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1298)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1321) -> begin
(

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (

let uu____1337 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____1337)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___93_1342 -> (match (uu___93_1342) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1356 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1366 = (inst_tscheme t)
in (match (uu____1366) with
| (us, t) -> begin
(

let uu____1373 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (uu____1373)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1385 -> (match (uu____1385) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs))) with
| true -> begin
(

let uu____1399 = (

let uu____1400 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (

let uu____1403 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____1406 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1407 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____1400 uu____1403 uu____1406 uu____1407)))))
in (failwith uu____1399))
end
| uu____1408 -> begin
()
end);
(

let uu____1409 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (Prims.snd uu____1409));
))
end
| uu____1413 -> begin
(

let uu____1414 = (

let uu____1415 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____1415))
in (failwith uu____1414))
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
| uu____1419 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1423 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1427 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1435 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], uu____1453) -> begin
Maybe
end
| (uu____1457, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| uu____1469 -> begin
No
end))
in (aux cur lns))))
end
| uu____1474 -> begin
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

let uu____1521 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1521) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___94_1538 -> (match (uu___94_1538) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____1557 = (

let uu____1565 = (inst_tscheme t)
in FStar_Util.Inl (uu____1565))
in Some (uu____1557))
end
| uu____1580 -> begin
None
end)
end
| Binding_sig (uu____1588, FStar_Syntax_Syntax.Sig_bundle (ses, uu____1590, uu____1591, uu____1592)) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1602 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1602) with
| true -> begin
(cache (FStar_Util.Inr (((se), (None)))))
end
| uu____1611 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1622) -> begin
Some (t)
end
| uu____1629 -> begin
(cache t)
end))
in (

let uu____1630 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1630) with
| true -> begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end
| uu____1646 -> begin
None
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1659 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1659) with
| true -> begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end
| uu____1682 -> begin
None
end))
end
| uu____1690 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1700 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1723 -> begin
(

let uu____1724 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1724) with
| true -> begin
(

let uu____1733 = (find_in_sigtab env lid)
in (match (uu____1733) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end))
end
| uu____1764 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1784, uu____1785, uu____1786) -> begin
(add_sigelts env ses)
end
| uu____1793 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1799) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1803 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___95_1819 -> (match (uu___95_1819) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| uu____1826 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____1841, (lb)::[]), uu____1843, uu____1844, uu____1845, uu____1846) -> begin
(

let uu____1857 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1857))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1865, lbs), uu____1867, uu____1868, uu____1869, uu____1870) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1888) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____1893 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1893) with
| true -> begin
(

let uu____1897 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in Some (uu____1897))
end
| uu____1905 -> begin
None
end))
end)))
end
| uu____1908 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1921) -> begin
(

let uu____1922 = (

let uu____1925 = (

let uu____1926 = (

let uu____1929 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____1929))
in ((ne.FStar_Syntax_Syntax.univs), (uu____1926)))
in (inst_tscheme uu____1925))
in Some (uu____1922))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____1939, uu____1940, uu____1941, uu____1942) -> begin
(

let uu____1947 = (

let uu____1950 = (

let uu____1951 = (

let uu____1954 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____1954))
in ((us), (uu____1951)))
in (inst_tscheme uu____1950))
in Some (uu____1947))
end
| uu____1961 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun uu___96_1988 -> (match (uu___96_1988) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2009, uvs, t, uu____2012, uu____2013, uu____2014, uu____2015, uu____2016), None) -> begin
(

let uu____2027 = (inst_tscheme ((uvs), (t)))
in Some (uu____2027))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, uu____2036), None) -> begin
(

let uu____2045 = (

let uu____2046 = (in_cur_mod env l)
in (uu____2046 = Yes))
in (match (uu____2045) with
| true -> begin
(

let uu____2050 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____2050) with
| true -> begin
(

let uu____2055 = (inst_tscheme ((uvs), (t)))
in Some (uu____2055))
end
| uu____2060 -> begin
None
end))
end
| uu____2063 -> begin
(

let uu____2064 = (inst_tscheme ((uvs), (t)))
in Some (uu____2064))
end))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2073, uu____2074, uu____2075, uu____2076), None) -> begin
(match (tps) with
| [] -> begin
(

let uu____2094 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _0_28 -> Some (_0_28)) uu____2094))
end
| uu____2104 -> begin
(

let uu____2105 = (

let uu____2108 = (

let uu____2109 = (

let uu____2112 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2112))
in ((uvs), (uu____2109)))
in (inst_tscheme uu____2108))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____2105))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____2128, uu____2129, uu____2130, uu____2131), Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____2150 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____2150))
end
| uu____2160 -> begin
(

let uu____2161 = (

let uu____2164 = (

let uu____2165 = (

let uu____2168 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____2168))
in ((uvs), (uu____2165)))
in (inst_tscheme_with uu____2164 us))
in (FStar_All.pipe_left (fun _0_31 -> Some (_0_31)) uu____2161))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (uu____2192), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2203 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (

let uu____2208 = (

let uu____2212 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____2212 mapper))
in (match (uu____2208) with
| Some (us, t) -> begin
Some (((us), ((

let uu___111_2245 = t
in {FStar_Syntax_Syntax.n = uu___111_2245.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___111_2245.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___111_2245.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2262 = (lookup_qname env l)
in (match (uu____2262) with
| None -> begin
false
end
| Some (uu____2278) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (

let uu____2299 = (try_lookup_bv env bv)
in (match (uu____2299) with
| None -> begin
(

let uu____2305 = (

let uu____2306 = (

let uu____2309 = (variable_not_found bv)
in (

let uu____2310 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((uu____2309), (uu____2310))))
in FStar_Errors.Error (uu____2306))
in (Prims.raise uu____2305))
end
| Some (t) -> begin
(

let uu____2316 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range uu____2316 t))
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (

let uu____2326 = (try_lookup_lid_aux env l)
in (match (uu____2326) with
| None -> begin
None
end
| Some (us, t) -> begin
(

let uu____2351 = (

let uu____2354 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (uu____2354)))
in Some (uu____2351))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (

let uu____2365 = (try_lookup_lid env l)
in (match (uu____2365) with
| None -> begin
(

let uu____2373 = (

let uu____2374 = (

let uu____2377 = (name_not_found l)
in ((uu____2377), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____2374))
in (Prims.raise uu____2373))
end
| Some (us, t) -> begin
((us), (t))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___97_2391 -> (match (uu___97_2391) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2393 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2404 = (lookup_qname env lid)
in (match (uu____2404) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2417, uvs, t, q, uu____2421), None)) -> begin
(

let uu____2437 = (

let uu____2443 = (

let uu____2446 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____2446)))
in ((uu____2443), (q)))
in Some (uu____2437))
end
| uu____2455 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2475 = (lookup_qname env lid)
in (match (uu____2475) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2486, uvs, t, uu____2489, uu____2490), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2506 -> begin
(

let uu____2515 = (

let uu____2516 = (

let uu____2519 = (name_not_found lid)
in ((uu____2519), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2516))
in (Prims.raise uu____2515))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2530 = (lookup_qname env lid)
in (match (uu____2530) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2541, uvs, t, uu____2544, uu____2545, uu____2546, uu____2547, uu____2548), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2566 -> begin
(

let uu____2575 = (

let uu____2576 = (

let uu____2579 = (name_not_found lid)
in ((uu____2579), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____2576))
in (Prims.raise uu____2575))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____2591 = (lookup_qname env lid)
in (match (uu____2591) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2603, uu____2604, uu____2605, uu____2606, uu____2607, dcs, uu____2609, uu____2610), uu____2611)) -> begin
((true), (dcs))
end
| uu____2633 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____2649 = (lookup_qname env lid)
in (match (uu____2649) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2658, uu____2659, uu____2660, l, uu____2662, uu____2663, uu____2664, uu____2665), uu____2666)) -> begin
l
end
| uu____2685 -> begin
(

let uu____2694 = (

let uu____2695 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____2695))
in (failwith uu____2694))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____2719 = (lookup_qname env lid)
in (match (uu____2719) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____2748, lbs), uu____2750, uu____2751, quals, uu____2753) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2770 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2770) with
| true -> begin
(

let uu____2775 = (

let uu____2779 = (

let uu____2780 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) uu____2780))
in ((lb.FStar_Syntax_Syntax.lbunivs), (uu____2779)))
in Some (uu____2775))
end
| uu____2785 -> begin
None
end)))))
end
| uu____2789 -> begin
None
end)
end
| uu____2792 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____2811 = (lookup_qname env ftv)
in (match (uu____2811) with
| Some (FStar_Util.Inr (se, None)) -> begin
(

let uu____2835 = (effect_signature se)
in (match (uu____2835) with
| None -> begin
None
end
| Some (uu____2842, t) -> begin
(

let uu____2846 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in Some (uu____2846))
end))
end
| uu____2847 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____2862 = (try_lookup_effect_lid env ftv)
in (match (uu____2862) with
| None -> begin
(

let uu____2864 = (

let uu____2865 = (

let uu____2868 = (name_not_found ftv)
in ((uu____2868), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____2865))
in (Prims.raise uu____2864))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____2882 = (lookup_qname env lid0)
in (match (uu____2882) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, uu____2899, uu____2900), None)) -> begin
(

let lid = (

let uu____2919 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid uu____2919))
in (

let uu____2920 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_2922 -> (match (uu___98_2922) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____2923 -> begin
false
end))))
in (match (uu____2920) with
| true -> begin
None
end
| uu____2929 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs))) with
| true -> begin
univ_insts
end
| uu____2935 -> begin
(match (((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____2938 -> begin
(

let uu____2939 = (

let uu____2940 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____2941 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" uu____2940 uu____2941)))
in (failwith uu____2939))
end)
end)
in (match (((binders), (univs))) with
| ([], uu____2947) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____2956, (uu____2957)::(uu____2958)::uu____2959) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(

let uu____2962 = (

let uu____2963 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____2964 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____2963 uu____2964)))
in (failwith uu____2962))
end
| uu____2970 -> begin
(

let uu____2973 = (

let uu____2976 = (

let uu____2977 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (uu____2977)))
in (inst_tscheme_with uu____2976 insts))
in (match (uu____2973) with
| (uu____2985, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (

let uu____2988 = (

let uu____2989 = (FStar_Syntax_Subst.compress t)
in uu____2989.FStar_Syntax_Syntax.n)
in (match (uu____2988) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| uu____3019 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____3023 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (

let uu____3047 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)
in (match (uu____3047) with
| None -> begin
None
end
| Some (uu____3054, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____3059 = (find l)
in (match (uu____3059) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____3064 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____3064) with
| Some (l) -> begin
l
end
| None -> begin
(

let uu____3067 = (find l)
in (match (uu____3067) with
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

let uu____3079 = (lookup_qname env l)
in (match (uu____3079) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3090), uu____3091)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____3106 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____3127 -> (

let uu____3128 = (

let uu____3129 = (FStar_Util.string_of_int i)
in (

let uu____3130 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____3129 uu____3130)))
in (failwith uu____3128)))
in (

let uu____3131 = (lookup_datacon env lid)
in (match (uu____3131) with
| (uu____3134, t) -> begin
(

let uu____3136 = (

let uu____3137 = (FStar_Syntax_Subst.compress t)
in uu____3137.FStar_Syntax_Syntax.n)
in (match (uu____3136) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3141) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____3156 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____3162 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right uu____3162 Prims.fst)))
end)
end
| uu____3167 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____3174 = (lookup_qname env l)
in (match (uu____3174) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____3183, uu____3184, uu____3185, quals, uu____3187), uu____3188)) -> begin
(FStar_Util.for_some (fun uu___99_3205 -> (match (uu___99_3205) with
| FStar_Syntax_Syntax.Projector (uu____3206) -> begin
true
end
| uu____3209 -> begin
false
end)) quals)
end
| uu____3210 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3225 = (lookup_qname env lid)
in (match (uu____3225) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____3234, uu____3235, uu____3236, uu____3237, uu____3238, uu____3239, uu____3240, uu____3241), uu____3242)) -> begin
true
end
| uu____3261 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3276 = (lookup_qname env lid)
in (match (uu____3276) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3285, uu____3286, uu____3287, uu____3288, uu____3289, uu____3290, tags, uu____3292), uu____3293)) -> begin
(FStar_Util.for_some (fun uu___100_3314 -> (match (uu___100_3314) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3317 -> begin
false
end)) tags)
end
| uu____3318 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3333 = (lookup_qname env lid)
in (match (uu____3333) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (uu____3342, uu____3343, uu____3344, tags, uu____3346), uu____3347)) -> begin
(FStar_Util.for_some (fun uu___101_3368 -> (match (uu___101_3368) with
| FStar_Syntax_Syntax.Action (uu____3369) -> begin
true
end
| uu____3370 -> begin
false
end)) tags)
end
| uu____3371 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (

let uu____3388 = (

let uu____3389 = (FStar_Syntax_Util.un_uinst head)
in uu____3389.FStar_Syntax_Syntax.n)
in (match (uu____3388) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3393 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun uu___102_3411 -> (match (uu___102_3411) with
| FStar_Util.Inl (uu____3420) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____3429) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3438, uu____3439, uu____3440, qs, uu____3442) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3445) -> begin
Some (true)
end
| uu____3457 -> begin
Some (false)
end)
end))
in (

let uu____3458 = (

let uu____3460 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____3460 mapper))
in (match (uu____3458) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____3483 = (lookup_qname env lid)
in (match (uu____3483) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3492, uu____3493, tps, uu____3495, uu____3496, uu____3497, uu____3498, uu____3499), uu____3500)) -> begin
(FStar_List.length tps)
end
| uu____3524 -> begin
(

let uu____3533 = (

let uu____3534 = (

let uu____3537 = (name_not_found lid)
in ((uu____3537), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____3534))
in (Prims.raise uu____3533))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____3554 = (effect_decl_opt env l)
in (match (uu____3554) with
| None -> begin
(

let uu____3556 = (

let uu____3557 = (

let uu____3560 = (name_not_found l)
in ((uu____3560), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____3557))
in (Prims.raise uu____3556))
end
| Some (md) -> begin
md
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = Some ((fun t wp e -> e))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____3591 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____3595 -> begin
(

let uu____3596 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____3620 -> (match (uu____3620) with
| (m1, m2, uu____3628, uu____3629, uu____3630) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____3596) with
| None -> begin
(

let uu____3639 = (

let uu____3640 = (

let uu____3643 = (

let uu____3644 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____3645 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____3644 uu____3645)))
in ((uu____3643), (env.range)))
in FStar_Errors.Error (uu____3640))
in (Prims.raise uu____3639))
end
| Some (uu____3649, uu____3650, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____3671 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____3687 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____3687) with
| None -> begin
(

let uu____3696 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____3696))
end
| Some (md) -> begin
(

let uu____3702 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____3702) with
| (uu____3709, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____3717))::((wp, uu____3719))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____3741 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (Some (res_u)))
end
| uu____3768 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (Some (res_u)))
end
| uu____3769 -> begin
(

let eff_name = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____3776 = (get_range env)
in (

let uu____3777 = (

let uu____3780 = (

let uu____3781 = (

let uu____3791 = (

let uu____3793 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____3793)::[])
in ((null_wp), (uu____3791)))
in FStar_Syntax_Syntax.Tm_app (uu____3781))
in (FStar_Syntax_Syntax.mk uu____3780))
in (uu____3777 None uu____3776)))
in (

let uu____3803 = (

let uu____3804 = (

let uu____3810 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____3810)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____3804; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____3803))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3818) -> begin
(

let effects = (

let uu___112_3820 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___112_3820.order; joins = uu___112_3820.joins})
in (

let uu___113_3821 = env
in {solver = uu___113_3821.solver; range = uu___113_3821.range; curmodule = uu___113_3821.curmodule; gamma = uu___113_3821.gamma; gamma_cache = uu___113_3821.gamma_cache; modules = uu___113_3821.modules; expected_typ = uu___113_3821.expected_typ; sigtab = uu___113_3821.sigtab; is_pattern = uu___113_3821.is_pattern; instantiate_imp = uu___113_3821.instantiate_imp; effects = effects; generalize = uu___113_3821.generalize; letrecs = uu___113_3821.letrecs; top_level = uu___113_3821.top_level; check_uvars = uu___113_3821.check_uvars; use_eq = uu___113_3821.use_eq; is_iface = uu___113_3821.is_iface; admit = uu___113_3821.admit; lax = uu___113_3821.lax; lax_universes = uu___113_3821.lax_universes; type_of = uu___113_3821.type_of; universe_of = uu___113_3821.universe_of; use_bv_sorts = uu___113_3821.use_bv_sorts; qname_and_index = uu___113_3821.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, uu____3823) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____3839 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____3839)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (Some (l1), Some (l2)) -> begin
Some ((fun t wp e -> (

let uu____3918 = (e1.mlift.mlift_wp t wp)
in (

let uu____3919 = (l1 t wp e)
in (l2 t uu____3918 uu____3919)))))
end
| uu____3920 -> begin
None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____3955 = (inst_tscheme lift_t)
in (match (uu____3955) with
| (uu____3960, lift_t) -> begin
(

let uu____3962 = (

let uu____3965 = (

let uu____3966 = (

let uu____3976 = (

let uu____3978 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____3979 = (

let uu____3981 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____3981)::[])
in (uu____3978)::uu____3979))
in ((lift_t), (uu____3976)))
in FStar_Syntax_Syntax.Tm_app (uu____3966))
in (FStar_Syntax_Syntax.mk uu____3965))
in (uu____3962 None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_wp = (match (sub.FStar_Syntax_Syntax.lift_wp) with
| Some (sub_lift_wp) -> begin
(mk_mlift_wp sub_lift_wp)
end
| None -> begin
(failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let mk_mlift_term = (fun lift_t r wp1 e -> (

let uu____4026 = (inst_tscheme lift_t)
in (match (uu____4026) with
| (uu____4031, lift_t) -> begin
(

let uu____4033 = (

let uu____4036 = (

let uu____4037 = (

let uu____4047 = (

let uu____4049 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____4050 = (

let uu____4052 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____4053 = (

let uu____4055 = (FStar_Syntax_Syntax.as_arg e)
in (uu____4055)::[])
in (uu____4052)::uu____4053))
in (uu____4049)::uu____4050))
in ((lift_t), (uu____4047)))
in FStar_Syntax_Syntax.Tm_app (uu____4037))
in (FStar_Syntax_Syntax.mk uu____4036))
in (uu____4033 None e.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_term = (FStar_Util.map_opt sub.FStar_Syntax_Syntax.lift mk_mlift_term)
in (

let edge = {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = {mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term}}
in (

let id_edge = (fun l -> {msource = sub.FStar_Syntax_Syntax.source; mtarget = sub.FStar_Syntax_Syntax.target; mlift = identity_mlift})
in (

let print_mlift = (fun l -> (

let bogus_term = (fun s -> (

let uu____4096 = (

let uu____4097 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____4097 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.fv_to_tm uu____4096)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____4101 = (

let uu____4102 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____4102))
in (

let uu____4103 = (

let uu____4104 = (FStar_Util.map_opt l.mlift_term (fun l -> (

let uu____4119 = (l arg wp e)
in (FStar_Syntax_Print.term_to_string uu____4119))))
in (FStar_Util.dflt "none" uu____4104))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4101 uu____4103))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order uu____4137 -> (match (uu____4137) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_32 -> Some (_0_32)))
end
| uu____4146 -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order = (

let fold_fun = (fun order k -> (

let uu____4162 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____4168 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____4173 -> begin
(

let uu____4174 = (

let uu____4179 = (find_edge order ((i), (k)))
in (

let uu____4181 = (find_edge order ((k), (j)))
in ((uu____4179), (uu____4181))))
in (match (uu____4174) with
| (Some (e1), Some (e2)) -> begin
(

let uu____4190 = (compose_edges e1 e2)
in (uu____4190)::[])
end
| uu____4191 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order uu____4162)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in ((FStar_All.pipe_right order (FStar_List.iter (fun edge -> (

let uu____4206 = ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (

let uu____4207 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right uu____4207 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____4206) with
| true -> begin
(

let uu____4210 = (

let uu____4211 = (

let uu____4214 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (

let uu____4215 = (get_range env)
in ((uu____4214), (uu____4215))))
in FStar_Errors.Error (uu____4211))
in (Prims.raise uu____4210))
end
| uu____4216 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____4262 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____4278 = (

let uu____4283 = (find_edge order ((i), (k)))
in (

let uu____4285 = (find_edge order ((j), (k)))
in ((uu____4283), (uu____4285))))
in (match (uu____4278) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____4308, uu____4309) -> begin
(

let uu____4313 = (

let uu____4316 = (

let uu____4317 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some uu____4317))
in (

let uu____4319 = (

let uu____4320 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some uu____4320))
in ((uu____4316), (uu____4319))))
in (match (uu____4313) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate");
bopt;
)
end
| uu____4331 -> begin
(failwith "Found a cycle in the lattice")
end)
end
| (false, false) -> begin
bopt
end
| (true, false) -> begin
Some (((k), (ik), (jk)))
end
| (false, true) -> begin
bopt
end))
end)
end
| uu____4339 -> begin
bopt
end))) None))
end)
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___114_4378 = env.effects
in {decls = uu___114_4378.decls; order = order; joins = joins})
in (

let uu___115_4379 = env
in {solver = uu___115_4379.solver; range = uu___115_4379.range; curmodule = uu___115_4379.curmodule; gamma = uu___115_4379.gamma; gamma_cache = uu___115_4379.gamma_cache; modules = uu___115_4379.modules; expected_typ = uu___115_4379.expected_typ; sigtab = uu___115_4379.sigtab; is_pattern = uu___115_4379.is_pattern; instantiate_imp = uu___115_4379.instantiate_imp; effects = effects; generalize = uu___115_4379.generalize; letrecs = uu___115_4379.letrecs; top_level = uu___115_4379.top_level; check_uvars = uu___115_4379.check_uvars; use_eq = uu___115_4379.use_eq; is_iface = uu___115_4379.is_iface; admit = uu___115_4379.admit; lax = uu___115_4379.lax; lax_universes = uu___115_4379.lax_universes; type_of = uu___115_4379.type_of; universe_of = uu___115_4379.universe_of; use_bv_sorts = uu___115_4379.use_bv_sorts; qname_and_index = uu___115_4379.qname_and_index})));
))))))))))))))
end
| uu____4380 -> begin
env
end))


let comp_to_comp_typ : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (Some (u))))
end
| uu____4402 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____4410 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____4410) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let uu____4420 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____4420) with
| (binders, cdef) -> begin
((match (((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____4437 = (

let uu____4438 = (

let uu____4441 = (

let uu____4442 = (FStar_Util.string_of_int (FStar_List.length binders))
in (

let uu____4448 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____4456 = (

let uu____4457 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____4457))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____4442 uu____4448 uu____4456))))
in ((uu____4441), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4438))
in (Prims.raise uu____4437))
end
| uu____4458 -> begin
()
end);
(

let inst = (

let uu____4461 = (

let uu____4467 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____4467)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____4474 uu____4475 -> (match (((uu____4474), (uu____4475))) with
| ((x, uu____4489), (t, uu____4491)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders uu____4461))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (

let uu____4506 = (

let uu___116_4507 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___116_4507.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___116_4507.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___116_4507.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___116_4507.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____4506 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c))));
)
end))
end))))


let effect_repr_aux = (fun only_reifiable env c u_c -> (

let uu____4537 = (

let uu____4539 = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (effect_decl_opt env uu____4539))
in (match (uu____4537) with
| None -> begin
None
end
| Some (ed) -> begin
(

let uu____4546 = (only_reifiable && (

let uu____4547 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____4547))))
in (match (uu____4546) with
| true -> begin
None
end
| uu____4554 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
None
end
| uu____4560 -> begin
(

let c = (unfold_effect_abbrev env c)
in (

let uu____4562 = (

let uu____4571 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (uu____4571)))
in (match (uu____4562) with
| (res_typ, wp) -> begin
(

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____4605 = (

let uu____4608 = (get_range env)
in (

let uu____4609 = (

let uu____4612 = (

let uu____4613 = (

let uu____4623 = (

let uu____4625 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____4625)::(wp)::[])
in ((repr), (uu____4623)))
in FStar_Syntax_Syntax.Tm_app (uu____4613))
in (FStar_Syntax_Syntax.mk uu____4612))
in (uu____4609 None uu____4608)))
in Some (uu____4605)))
end)))
end)
end))
end)))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____4669 = (

let uu____4670 = (

let uu____4673 = (

let uu____4674 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____4674))
in (

let uu____4675 = (get_range env)
in ((uu____4673), (uu____4675))))
in FStar_Errors.Error (uu____4670))
in (Prims.raise uu____4669)))
in (

let uu____4676 = (effect_repr_aux true env c u_c)
in (match (uu____4676) with
| None -> begin
(no_reify (FStar_Syntax_Util.comp_effect_name c))
end
| Some (tm) -> begin
tm
end))))


let is_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let quals = (lookup_effect_quals env effect_lid)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals)))


let is_reifiable : env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either  ->  Prims.bool = (fun env c -> (

let effect_lid = (match (c) with
| FStar_Util.Inl (lc) -> begin
lc.FStar_Syntax_Syntax.eff_name
end
| FStar_Util.Inr (eff_name, uu____4708) -> begin
eff_name
end)
in (is_reifiable_effect env effect_lid)))


let is_reifiable_comp : env  ->  FStar_Syntax_Syntax.comp  ->  Prims.bool = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name)
end
| uu____4721 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____4728 = (

let uu____4729 = (FStar_Syntax_Subst.compress t)
in uu____4729.FStar_Syntax_Syntax.n)
in (match (uu____4728) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4732, c) -> begin
(is_reifiable_comp env c)
end
| uu____4744 -> begin
false
end)))


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

let uu____4769 = (push x rest)
in (local)::uu____4769)
end))
in (

let uu___117_4771 = env
in (

let uu____4772 = (push s env.gamma)
in {solver = uu___117_4771.solver; range = uu___117_4771.range; curmodule = uu___117_4771.curmodule; gamma = uu____4772; gamma_cache = uu___117_4771.gamma_cache; modules = uu___117_4771.modules; expected_typ = uu___117_4771.expected_typ; sigtab = uu___117_4771.sigtab; is_pattern = uu___117_4771.is_pattern; instantiate_imp = uu___117_4771.instantiate_imp; effects = uu___117_4771.effects; generalize = uu___117_4771.generalize; letrecs = uu___117_4771.letrecs; top_level = uu___117_4771.top_level; check_uvars = uu___117_4771.check_uvars; use_eq = uu___117_4771.use_eq; is_iface = uu___117_4771.is_iface; admit = uu___117_4771.admit; lax = uu___117_4771.lax; lax_universes = uu___117_4771.lax_universes; type_of = uu___117_4771.type_of; universe_of = uu___117_4771.universe_of; use_bv_sorts = uu___117_4771.use_bv_sorts; qname_and_index = uu___117_4771.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___118_4799 = env
in {solver = uu___118_4799.solver; range = uu___118_4799.range; curmodule = uu___118_4799.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___118_4799.gamma_cache; modules = uu___118_4799.modules; expected_typ = uu___118_4799.expected_typ; sigtab = uu___118_4799.sigtab; is_pattern = uu___118_4799.is_pattern; instantiate_imp = uu___118_4799.instantiate_imp; effects = uu___118_4799.effects; generalize = uu___118_4799.generalize; letrecs = uu___118_4799.letrecs; top_level = uu___118_4799.top_level; check_uvars = uu___118_4799.check_uvars; use_eq = uu___118_4799.use_eq; is_iface = uu___118_4799.is_iface; admit = uu___118_4799.admit; lax = uu___118_4799.lax; lax_universes = uu___118_4799.lax_universes; type_of = uu___118_4799.type_of; universe_of = uu___118_4799.universe_of; use_bv_sorts = uu___118_4799.use_bv_sorts; qname_and_index = uu___118_4799.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env uu____4815 -> (match (uu____4815) with
| (x, uu____4819) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let x = (

let uu___119_4839 = x
in {FStar_Syntax_Syntax.ppname = uu___119_4839.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_4839.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___120_4869 = env
in {solver = uu___120_4869.solver; range = uu___120_4869.range; curmodule = uu___120_4869.curmodule; gamma = []; gamma_cache = uu___120_4869.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___120_4869.sigtab; is_pattern = uu___120_4869.is_pattern; instantiate_imp = uu___120_4869.instantiate_imp; effects = uu___120_4869.effects; generalize = uu___120_4869.generalize; letrecs = uu___120_4869.letrecs; top_level = uu___120_4869.top_level; check_uvars = uu___120_4869.check_uvars; use_eq = uu___120_4869.use_eq; is_iface = uu___120_4869.is_iface; admit = uu___120_4869.admit; lax = uu___120_4869.lax; lax_universes = uu___120_4869.lax_universes; type_of = uu___120_4869.type_of; universe_of = uu___120_4869.universe_of; use_bv_sorts = uu___120_4869.use_bv_sorts; qname_and_index = uu___120_4869.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___121_4884 = env
in {solver = uu___121_4884.solver; range = uu___121_4884.range; curmodule = uu___121_4884.curmodule; gamma = uu___121_4884.gamma; gamma_cache = uu___121_4884.gamma_cache; modules = uu___121_4884.modules; expected_typ = Some (t); sigtab = uu___121_4884.sigtab; is_pattern = uu___121_4884.is_pattern; instantiate_imp = uu___121_4884.instantiate_imp; effects = uu___121_4884.effects; generalize = uu___121_4884.generalize; letrecs = uu___121_4884.letrecs; top_level = uu___121_4884.top_level; check_uvars = uu___121_4884.check_uvars; use_eq = false; is_iface = uu___121_4884.is_iface; admit = uu___121_4884.admit; lax = uu___121_4884.lax; lax_universes = uu___121_4884.lax_universes; type_of = uu___121_4884.type_of; universe_of = uu___121_4884.universe_of; use_bv_sorts = uu___121_4884.use_bv_sorts; qname_and_index = uu___121_4884.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env_ -> (

let uu____4900 = (expected_typ env_)
in (((

let uu___122_4903 = env_
in {solver = uu___122_4903.solver; range = uu___122_4903.range; curmodule = uu___122_4903.curmodule; gamma = uu___122_4903.gamma; gamma_cache = uu___122_4903.gamma_cache; modules = uu___122_4903.modules; expected_typ = None; sigtab = uu___122_4903.sigtab; is_pattern = uu___122_4903.is_pattern; instantiate_imp = uu___122_4903.instantiate_imp; effects = uu___122_4903.effects; generalize = uu___122_4903.generalize; letrecs = uu___122_4903.letrecs; top_level = uu___122_4903.top_level; check_uvars = uu___122_4903.check_uvars; use_eq = false; is_iface = uu___122_4903.is_iface; admit = uu___122_4903.admit; lax = uu___122_4903.lax; lax_universes = uu___122_4903.lax_universes; type_of = uu___122_4903.type_of; universe_of = uu___122_4903.universe_of; use_bv_sorts = uu___122_4903.use_bv_sorts; qname_and_index = uu___122_4903.qname_and_index})), (uu____4900))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(

let uu____4914 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___103_4918 -> (match (uu___103_4918) with
| Binding_sig (uu____4920, se) -> begin
(se)::[]
end
| uu____4924 -> begin
[]
end))))
in (FStar_All.pipe_right uu____4914 FStar_List.rev))
end
| uu____4927 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___123_4929 = env
in {solver = uu___123_4929.solver; range = uu___123_4929.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___123_4929.gamma_cache; modules = (m)::env.modules; expected_typ = uu___123_4929.expected_typ; sigtab = uu___123_4929.sigtab; is_pattern = uu___123_4929.is_pattern; instantiate_imp = uu___123_4929.instantiate_imp; effects = uu___123_4929.effects; generalize = uu___123_4929.generalize; letrecs = uu___123_4929.letrecs; top_level = uu___123_4929.top_level; check_uvars = uu___123_4929.check_uvars; use_eq = uu___123_4929.use_eq; is_iface = uu___123_4929.is_iface; admit = uu___123_4929.admit; lax = uu___123_4929.lax; lax_universes = uu___123_4929.lax_universes; type_of = uu___123_4929.type_of; universe_of = uu___123_4929.universe_of; use_bv_sorts = uu___123_4929.use_bv_sorts; qname_and_index = uu___123_4929.qname_and_index});
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
| (Binding_univ (uu____4979))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____4994 = (

let uu____4998 = (FStar_Syntax_Free.uvars t)
in (ext out uu____4998))
in (aux uu____4994 tl))
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

let uu____5054 = (

let uu____5056 = (FStar_Syntax_Free.univs t)
in (ext out uu____5056))
in (aux uu____5054 tl))
end
| (Binding_sig (uu____5058))::uu____5059 -> begin
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
| (Binding_sig_inst (uu____5096))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(

let uu____5106 = (FStar_Util.set_add uname out)
in (aux uu____5106 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(

let uu____5120 = (

let uu____5122 = (FStar_Syntax_Free.univnames t)
in (ext out uu____5122))
in (aux uu____5120 tl))
end
| (Binding_sig (uu____5124))::uu____5125 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___104_5141 -> (match (uu___104_5141) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____5153 = (

let uu____5155 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____5155 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____5153 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___105_5206 -> (match (uu___105_5206) with
| Binding_sig (lids, uu____5210) -> begin
(FStar_List.append lids keys)
end
| uu____5213 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____5215 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun uu____5219 -> ()); push = (fun uu____5220 -> ()); pop = (fun uu____5221 -> ()); mark = (fun uu____5222 -> ()); reset_mark = (fun uu____5223 -> ()); commit_mark = (fun uu____5224 -> ()); encode_modul = (fun uu____5225 uu____5226 -> ()); encode_sig = (fun uu____5227 uu____5228 -> ()); solve = (fun uu____5229 uu____5230 uu____5231 -> ()); is_trivial = (fun uu____5235 uu____5236 -> false); finish = (fun uu____5237 -> ()); refresh = (fun uu____5238 -> ())}




