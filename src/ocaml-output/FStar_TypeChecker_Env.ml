
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


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun type_of universe_of solver module_lid -> (let _0_171 = (new_gamma_cache ())
in (let _0_170 = (new_sigtab ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = _0_171; modules = []; expected_typ = None; sigtab = _0_170; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = None})))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____868 -> (

let uu____869 = (FStar_ST.read query_indices)
in (match (uu____869) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____883 -> begin
(let _0_174 = (let _0_173 = (FStar_List.hd (FStar_ST.read query_indices))
in (let _0_172 = (FStar_ST.read query_indices)
in (_0_173)::_0_172))
in (FStar_ST.write query_indices _0_174))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____914 -> (

let uu____915 = (FStar_ST.read query_indices)
in (match (uu____915) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd)::tl -> begin
(FStar_ST.write query_indices tl)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____951 -> (match (uu____951) with
| (l, n) -> begin
(

let uu____956 = (FStar_ST.read query_indices)
in (match (uu____956) with
| (hd)::tl -> begin
(FStar_ST.write query_indices (((((l), (n)))::hd)::tl))
end
| uu____990 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____1000 -> (FStar_List.hd (FStar_ST.read query_indices)))


let commit_query_index_mark : Prims.unit  ->  Prims.unit = (fun uu____1012 -> (

let uu____1013 = (FStar_ST.read query_indices)
in (match (uu____1013) with
| (hd)::(uu____1025)::tl -> begin
(FStar_ST.write query_indices ((hd)::tl))
end
| uu____1052 -> begin
(failwith "Unmarked query index stack")
end)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((let _0_176 = (let _0_175 = (FStar_ST.read stack)
in (env)::_0_175)
in (FStar_ST.write stack _0_176));
(

let uu___106_1072 = env
in (let _0_178 = (FStar_Util.smap_copy (gamma_cache env))
in (let _0_177 = (FStar_Util.smap_copy (sigtab env))
in {solver = uu___106_1072.solver; range = uu___106_1072.range; curmodule = uu___106_1072.curmodule; gamma = uu___106_1072.gamma; gamma_cache = _0_178; modules = uu___106_1072.modules; expected_typ = uu___106_1072.expected_typ; sigtab = _0_177; is_pattern = uu___106_1072.is_pattern; instantiate_imp = uu___106_1072.instantiate_imp; effects = uu___106_1072.effects; generalize = uu___106_1072.generalize; letrecs = uu___106_1072.letrecs; top_level = uu___106_1072.top_level; check_uvars = uu___106_1072.check_uvars; use_eq = uu___106_1072.use_eq; is_iface = uu___106_1072.is_iface; admit = uu___106_1072.admit; lax = uu___106_1072.lax; lax_universes = uu___106_1072.lax_universes; type_of = uu___106_1072.type_of; universe_of = uu___106_1072.universe_of; use_bv_sorts = uu___106_1072.use_bv_sorts; qname_and_index = uu___106_1072.qname_and_index})));
))


let pop_stack : Prims.unit  ->  env = (fun uu____1075 -> (

let uu____1076 = (FStar_ST.read stack)
in (match (uu____1076) with
| (env)::tl -> begin
((FStar_ST.write stack tl);
env;
)
end
| uu____1088 -> begin
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
(Prims.ignore (pop_stack ()));
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

let uu____1138 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____1150 -> (match (uu____1150) with
| (m, uu____1154) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____1138) with
| None -> begin
(

let next = (n + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___107_1159 = env
in {solver = uu___107_1159.solver; range = uu___107_1159.range; curmodule = uu___107_1159.curmodule; gamma = uu___107_1159.gamma; gamma_cache = uu___107_1159.gamma_cache; modules = uu___107_1159.modules; expected_typ = uu___107_1159.expected_typ; sigtab = uu___107_1159.sigtab; is_pattern = uu___107_1159.is_pattern; instantiate_imp = uu___107_1159.instantiate_imp; effects = uu___107_1159.effects; generalize = uu___107_1159.generalize; letrecs = uu___107_1159.letrecs; top_level = uu___107_1159.top_level; check_uvars = uu___107_1159.check_uvars; use_eq = uu___107_1159.use_eq; is_iface = uu___107_1159.is_iface; admit = uu___107_1159.admit; lax = uu___107_1159.lax; lax_universes = uu___107_1159.lax_universes; type_of = uu___107_1159.type_of; universe_of = uu___107_1159.universe_of; use_bv_sorts = uu___107_1159.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end
| Some (uu____1162, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___108_1168 = env
in {solver = uu___108_1168.solver; range = uu___108_1168.range; curmodule = uu___108_1168.curmodule; gamma = uu___108_1168.gamma; gamma_cache = uu___108_1168.gamma_cache; modules = uu___108_1168.modules; expected_typ = uu___108_1168.expected_typ; sigtab = uu___108_1168.sigtab; is_pattern = uu___108_1168.is_pattern; instantiate_imp = uu___108_1168.instantiate_imp; effects = uu___108_1168.effects; generalize = uu___108_1168.generalize; letrecs = uu___108_1168.letrecs; top_level = uu___108_1168.top_level; check_uvars = uu___108_1168.check_uvars; use_eq = uu___108_1168.use_eq; is_iface = uu___108_1168.is_iface; admit = uu___108_1168.admit; lax = uu___108_1168.lax; lax_universes = uu___108_1168.lax_universes; type_of = uu___108_1168.type_of; universe_of = uu___108_1168.universe_of; use_bv_sorts = uu___108_1168.use_bv_sorts; qname_and_index = Some (((l), (next)))});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((r = FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____1183 -> begin
(

let uu___109_1184 = e
in {solver = uu___109_1184.solver; range = r; curmodule = uu___109_1184.curmodule; gamma = uu___109_1184.gamma; gamma_cache = uu___109_1184.gamma_cache; modules = uu___109_1184.modules; expected_typ = uu___109_1184.expected_typ; sigtab = uu___109_1184.sigtab; is_pattern = uu___109_1184.is_pattern; instantiate_imp = uu___109_1184.instantiate_imp; effects = uu___109_1184.effects; generalize = uu___109_1184.generalize; letrecs = uu___109_1184.letrecs; top_level = uu___109_1184.top_level; check_uvars = uu___109_1184.check_uvars; use_eq = uu___109_1184.use_eq; is_iface = uu___109_1184.is_iface; admit = uu___109_1184.admit; lax = uu___109_1184.lax; lax_universes = uu___109_1184.lax_universes; type_of = uu___109_1184.type_of; universe_of = uu___109_1184.universe_of; use_bv_sorts = uu___109_1184.use_bv_sorts; qname_and_index = uu___109_1184.qname_and_index})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___110_1201 = env
in {solver = uu___110_1201.solver; range = uu___110_1201.range; curmodule = lid; gamma = uu___110_1201.gamma; gamma_cache = uu___110_1201.gamma_cache; modules = uu___110_1201.modules; expected_typ = uu___110_1201.expected_typ; sigtab = uu___110_1201.sigtab; is_pattern = uu___110_1201.is_pattern; instantiate_imp = uu___110_1201.instantiate_imp; effects = uu___110_1201.effects; generalize = uu___110_1201.generalize; letrecs = uu___110_1201.letrecs; top_level = uu___110_1201.top_level; check_uvars = uu___110_1201.check_uvars; use_eq = uu___110_1201.use_eq; is_iface = uu___110_1201.is_iface; admit = uu___110_1201.admit; lax = uu___110_1201.lax; lax_universes = uu___110_1201.lax_universes; type_of = uu___110_1201.type_of; universe_of = uu___110_1201.universe_of; use_bv_sorts = uu___110_1201.use_bv_sorts; qname_and_index = uu___110_1201.qname_and_index}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt Prims.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v -> (let _0_179 = (FStar_Syntax_Print.bv_to_string v)
in (FStar_Util.format1 "Variable \"%s\" not found" _0_179)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____1225 -> FStar_Syntax_Syntax.U_unif ((FStar_Unionfind.fresh None)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____1246) -> begin
(

let n = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n - i)), (u))))))
in (let _0_180 = (FStar_Syntax_Subst.subst vs t)
in ((us), (_0_180)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___93_1266 -> (match (uu___93_1266) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____1280 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____1290 = (inst_tscheme t)
in (match (uu____1290) with
| (us, t) -> begin
(let _0_181 = (FStar_Syntax_Subst.set_use_range r t)
in ((us), (_0_181)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____1308 -> (match (uu____1308) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match (((FStar_List.length insts) <> (FStar_List.length univs))) with
| true -> begin
(failwith (let _0_185 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (let _0_184 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (let _0_183 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_182 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" _0_185 _0_184 _0_183 _0_182))))))
end
| uu____1326 -> begin
()
end);
(Prims.snd (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts));
))
end
| uu____1328 -> begin
(failwith (let _0_186 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" _0_186)))
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
| uu____1332 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____1336 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____1340 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((l.FStar_Ident.nsstr = cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____1348 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], uu____1366) -> begin
Maybe
end
| (uu____1370, []) -> begin
No
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| uu____1382 -> begin
No
end))
in (aux cur lns))))
end
| uu____1387 -> begin
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

let uu____1434 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____1434) with
| None -> begin
(FStar_Util.find_map env.gamma (fun uu___94_1451 -> (match (uu___94_1451) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
Some (FStar_Util.Inl ((inst_tscheme t)))
end
| uu____1482 -> begin
None
end)
end
| Binding_sig (uu____1490, FStar_Syntax_Syntax.Sig_bundle (ses, uu____1492, uu____1493, uu____1494)) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____1504 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1504) with
| true -> begin
(cache (FStar_Util.Inr (((se), (None)))))
end
| uu____1513 -> begin
None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____1524) -> begin
Some (t)
end
| uu____1531 -> begin
(cache t)
end))
in (

let uu____1532 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1532) with
| true -> begin
(maybe_cache (FStar_Util.Inr (((s), (None)))))
end
| uu____1548 -> begin
None
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____1561 = (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____1561) with
| true -> begin
Some (FStar_Util.Inr (((s), (Some (us)))))
end
| uu____1584 -> begin
None
end))
end
| uu____1592 -> begin
None
end)))
end
| se -> begin
se
end))
end
| uu____1602 -> begin
None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____1625 -> begin
(

let uu____1626 = ((cur_mod <> Yes) || (has_interface env env.curmodule))
in (match (uu____1626) with
| true -> begin
(

let uu____1635 = (find_in_sigtab env lid)
in (match (uu____1635) with
| Some (se) -> begin
Some (FStar_Util.Inr (((se), (None))))
end
| None -> begin
None
end))
end
| uu____1666 -> begin
None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1686, uu____1687, uu____1688) -> begin
(add_sigelts env ses)
end
| uu____1695 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1701) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____1705 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___95_1721 -> (match (uu___95_1721) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
Some (id.FStar_Syntax_Syntax.sort)
end
| uu____1728 -> begin
None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se lid -> (match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____1743, (lb)::[]), uu____1745, uu____1746, uu____1747, uu____1748) -> begin
Some ((inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))))
end
| FStar_Syntax_Syntax.Sig_let ((uu____1764, lbs), uu____1766, uu____1767, uu____1768, uu____1769) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____1787) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____1792 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____1792) with
| true -> begin
Some ((inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))))
end
| uu____1801 -> begin
None
end))
end)))
end
| uu____1804 -> begin
None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) Prims.option = (fun se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____1817) -> begin
Some ((inst_tscheme (let _0_188 = (let _0_187 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders _0_187))
in ((ne.FStar_Syntax_Syntax.univs), (_0_188)))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____1825, uu____1826, uu____1827, uu____1828) -> begin
Some ((inst_tscheme (let _0_190 = (let _0_189 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders _0_189))
in ((us), (_0_190)))))
end
| uu____1837 -> begin
None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.option = (fun env lid -> (

let mapper = (fun uu___96_1864 -> (match (uu___96_1864) with
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____1885, uvs, t, uu____1888, uu____1889, uu____1890, uu____1891, uu____1892), None) -> begin
Some ((inst_tscheme ((uvs), (t))))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t, qs, uu____1909), None) -> begin
(

let uu____1918 = (let _0_191 = (in_cur_mod env l)
in (_0_191 = Yes))
in (match (uu____1918) with
| true -> begin
(

let uu____1922 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____1922) with
| true -> begin
Some ((inst_tscheme ((uvs), (t))))
end
| uu____1929 -> begin
None
end))
end
| uu____1932 -> begin
Some ((inst_tscheme ((uvs), (t))))
end))
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____1939, uu____1940, uu____1941, uu____1942), None) -> begin
(match (tps) with
| [] -> begin
(let _0_193 = (inst_tscheme ((uvs), (k)))
in (FStar_All.pipe_left (fun _0_192 -> Some (_0_192)) _0_193))
end
| uu____1967 -> begin
(let _0_197 = (inst_tscheme (let _0_196 = (let _0_195 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _0_195))
in ((uvs), (_0_196))))
in (FStar_All.pipe_left (fun _0_194 -> Some (_0_194)) _0_197))
end)
end
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, tps, k, uu____1981, uu____1982, uu____1983, uu____1984), Some (us)) -> begin
(match (tps) with
| [] -> begin
(let _0_199 = (inst_tscheme_with ((uvs), (k)) us)
in (FStar_All.pipe_left (fun _0_198 -> Some (_0_198)) _0_199))
end
| uu____2010 -> begin
(let _0_204 = (let _0_203 = (let _0_202 = (let _0_201 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps _0_201))
in ((uvs), (_0_202)))
in (inst_tscheme_with _0_203 us))
in (FStar_All.pipe_left (fun _0_200 -> Some (_0_200)) _0_204))
end)
end
| FStar_Util.Inr (se) -> begin
(match (se) with
| (FStar_Syntax_Syntax.Sig_let (uu____2032), None) -> begin
(lookup_type_of_let (Prims.fst se) lid)
end
| uu____2043 -> begin
(effect_signature (Prims.fst se))
end)
end))
in (

let uu____2048 = (let _0_205 = (lookup_qname env lid)
in (FStar_Util.bind_opt _0_205 mapper))
in (match (uu____2048) with
| Some (us, t) -> begin
Some (((us), ((

let uu___111_2076 = t
in {FStar_Syntax_Syntax.n = uu___111_2076.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___111_2076.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___111_2076.FStar_Syntax_Syntax.vars}))))
end
| None -> begin
None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2093 = (lookup_qname env l)
in (match (uu____2093) with
| None -> begin
false
end
| Some (uu____2109) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ = (fun env bv -> (

let uu____2130 = (try_lookup_bv env bv)
in (match (uu____2130) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_207 = (variable_not_found bv)
in (let _0_206 = (FStar_Syntax_Syntax.range_of_bv bv)
in ((_0_207), (_0_206)))))))
end
| Some (t) -> begin
(let _0_208 = (FStar_Syntax_Syntax.range_of_bv bv)
in (FStar_Syntax_Subst.set_use_range _0_208 t))
end)))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) Prims.option = (fun env l -> (

let uu____2150 = (try_lookup_lid_aux env l)
in (match (uu____2150) with
| None -> begin
None
end
| Some (us, t) -> begin
Some ((let _0_209 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid l) t)
in ((us), (_0_209))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env l -> (

let uu____2185 = (try_lookup_lid env l)
in (match (uu____2185) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_210 = (name_not_found l)
in ((_0_210), ((FStar_Ident.range_of_lid l)))))))
end
| Some (us, t) -> begin
((us), (t))
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___97_2206 -> (match (uu___97_2206) with
| Binding_univ (y) -> begin
(x.FStar_Ident.idText = y.FStar_Ident.idText)
end
| uu____2208 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (

let uu____2219 = (lookup_qname env lid)
in (match (uu____2219) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2232, uvs, t, q, uu____2236), None)) -> begin
Some ((let _0_212 = (let _0_211 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (_0_211)))
in ((_0_212), (q))))
end
| uu____2260 -> begin
None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2280 = (lookup_qname env lid)
in (match (uu____2280) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2291, uvs, t, uu____2294, uu____2295), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2311 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_213 = (name_not_found lid)
in ((_0_213), ((FStar_Ident.range_of_lid lid)))))))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____2330 = (lookup_qname env lid)
in (match (uu____2330) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2341, uvs, t, uu____2344, uu____2345, uu____2346, uu____2347, uu____2348), None)) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____2366 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_214 = (name_not_found lid)
in ((_0_214), ((FStar_Ident.range_of_lid lid)))))))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____2386 = (lookup_qname env lid)
in (match (uu____2386) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____2398, uu____2399, uu____2400, uu____2401, uu____2402, dcs, uu____2404, uu____2405), uu____2406)) -> begin
((true), (dcs))
end
| uu____2428 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____2444 = (lookup_qname env lid)
in (match (uu____2444) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2453, uu____2454, uu____2455, l, uu____2457, uu____2458, uu____2459, uu____2460), uu____2461)) -> begin
l
end
| uu____2480 -> begin
(failwith (let _0_215 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" _0_215)))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) Prims.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____2512 = (lookup_qname env lid)
in (match (uu____2512) with
| Some (FStar_Util.Inr (se, None)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_let ((uu____2541, lbs), uu____2543, uu____2544, quals, uu____2546) when (visible quals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2563 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____2563) with
| true -> begin
Some ((let _0_217 = (let _0_216 = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) _0_216))
in ((lb.FStar_Syntax_Syntax.lbunivs), (_0_217))))
end
| uu____2572 -> begin
None
end)))))
end
| uu____2576 -> begin
None
end)
end
| uu____2579 -> begin
None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term Prims.option = (fun env ftv -> (

let uu____2598 = (lookup_qname env ftv)
in (match (uu____2598) with
| Some (FStar_Util.Inr (se, None)) -> begin
(

let uu____2622 = (effect_signature se)
in (match (uu____2622) with
| None -> begin
None
end
| Some (uu____2629, t) -> begin
Some ((FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t))
end))
end
| uu____2633 -> begin
None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____2648 = (try_lookup_effect_lid env ftv)
in (match (uu____2648) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_218 = (name_not_found ftv)
in ((_0_218), ((FStar_Ident.range_of_lid ftv)))))))
end
| Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) Prims.option = (fun env univ_insts lid0 -> (

let uu____2663 = (lookup_qname env lid0)
in (match (uu____2663) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs, binders, c, quals, uu____2680, uu____2681), None)) -> begin
(

let lid = (let _0_219 = (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) (FStar_Ident.range_of_lid lid0))
in (FStar_Ident.set_lid_range lid _0_219))
in (

let uu____2700 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___98_2702 -> (match (uu___98_2702) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____2703 -> begin
false
end))))
in (match (uu____2700) with
| true -> begin
None
end
| uu____2709 -> begin
(

let insts = (match (((FStar_List.length univ_insts) = (FStar_List.length univs))) with
| true -> begin
univ_insts
end
| uu____2715 -> begin
(match (((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid) && ((FStar_List.length univ_insts) = (Prims.parse_int "1")))) with
| true -> begin
(FStar_List.append univ_insts ((FStar_Syntax_Syntax.U_zero)::[]))
end
| uu____2718 -> begin
(failwith (let _0_221 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_220 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format2 "Unexpected instantiation of effect %s with %s universes" _0_221 _0_220))))
end)
end)
in (match (((binders), (univs))) with
| ([], uu____2724) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____2733, (uu____2734)::(uu____2735)::uu____2736) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))) -> begin
(failwith (let _0_223 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_222 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" _0_223 _0_222))))
end
| uu____2744 -> begin
(

let uu____2747 = (let _0_225 = (let _0_224 = (FStar_Syntax_Util.arrow binders c)
in ((univs), (_0_224)))
in (inst_tscheme_with _0_225 insts))
in (match (uu____2747) with
| (uu____2755, t) -> begin
(

let t = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in (

let uu____2758 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2758) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
Some (((binders), (c)))
end
| uu____2786 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____2790 -> begin
None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find = (fun l -> (

let uu____2814 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l)
in (match (uu____2814) with
| None -> begin
None
end
| Some (uu____2821, c) -> begin
(

let l = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____2826 = (find l)
in (match (uu____2826) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end)))
end)))
in (

let res = (

let uu____2831 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____2831) with
| Some (l) -> begin
l
end
| None -> begin
(

let uu____2834 = (find l)
in (match (uu____2834) with
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

let uu____2846 = (lookup_qname env l)
in (match (uu____2846) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_new_effect (ne, uu____2857), uu____2858)) -> begin
ne.FStar_Syntax_Syntax.qualifiers
end
| uu____2873 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____2894 -> (failwith (let _0_227 = (FStar_Util.string_of_int i)
in (let _0_226 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _0_227 _0_226)))))
in (

let uu____2895 = (lookup_datacon env lid)
in (match (uu____2895) with
| (uu____2898, t) -> begin
(

let uu____2900 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2900) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____2902) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____2917 -> begin
(

let b = (FStar_List.nth binders i)
in (let _0_228 = (FStar_Syntax_Util.mk_field_projector_name lid (Prims.fst b) i)
in (FStar_All.pipe_right _0_228 Prims.fst)))
end)
end
| uu____2925 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____2932 = (lookup_qname env l)
in (match (uu____2932) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_declare_typ (uu____2941, uu____2942, uu____2943, quals, uu____2945), uu____2946)) -> begin
(FStar_Util.for_some (fun uu___99_2963 -> (match (uu___99_2963) with
| FStar_Syntax_Syntax.Projector (uu____2964) -> begin
true
end
| uu____2967 -> begin
false
end)) quals)
end
| uu____2968 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____2983 = (lookup_qname env lid)
in (match (uu____2983) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_datacon (uu____2992, uu____2993, uu____2994, uu____2995, uu____2996, uu____2997, uu____2998, uu____2999), uu____3000)) -> begin
true
end
| uu____3019 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3034 = (lookup_qname env lid)
in (match (uu____3034) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3043, uu____3044, uu____3045, uu____3046, uu____3047, uu____3048, tags, uu____3050), uu____3051)) -> begin
(FStar_Util.for_some (fun uu___100_3072 -> (match (uu___100_3072) with
| (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) -> begin
true
end
| uu____3075 -> begin
false
end)) tags)
end
| uu____3076 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____3091 = (lookup_qname env lid)
in (match (uu____3091) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_let (uu____3100, uu____3101, uu____3102, tags, uu____3104), uu____3105)) -> begin
(FStar_Util.for_some (fun uu___101_3126 -> (match (uu___101_3126) with
| FStar_Syntax_Syntax.Action (uu____3127) -> begin
true
end
| uu____3128 -> begin
false
end)) tags)
end
| uu____3129 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (fun env head -> (

let uu____3146 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____3146) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| uu____3148 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun uu___102_3166 -> (match (uu___102_3166) with
| FStar_Util.Inl (uu____3175) -> begin
Some (false)
end
| FStar_Util.Inr (se, uu____3184) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3193, uu____3194, uu____3195, qs, uu____3197) -> begin
Some ((FStar_List.contains FStar_Syntax_Syntax.New qs))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3200) -> begin
Some (true)
end
| uu____3212 -> begin
Some (false)
end)
end))
in (

let uu____3213 = (let _0_229 = (lookup_qname env lid)
in (FStar_Util.bind_opt _0_229 mapper))
in (match (uu____3213) with
| Some (b) -> begin
b
end
| None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____3229 = (lookup_qname env lid)
in (match (uu____3229) with
| Some (FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (uu____3238, uu____3239, tps, uu____3241, uu____3242, uu____3243, uu____3244, uu____3245), uu____3246)) -> begin
(FStar_List.length tps)
end
| uu____3270 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_230 = (name_not_found lid)
in ((_0_230), ((FStar_Ident.range_of_lid lid)))))))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____3295 = (effect_decl_opt env l)
in (match (uu____3295) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_231 = (name_not_found l)
in ((_0_231), ((FStar_Ident.range_of_lid l)))))))
end
| Some (md) -> begin
md
end)))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3344 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((fun t wp -> wp)), ((fun t wp -> wp)))
end
| uu____3368 -> begin
(

let uu____3369 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____3393 -> (match (uu____3393) with
| (m1, m2, uu____3401, uu____3402, uu____3403) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____3369) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((let _0_234 = (let _0_233 = (FStar_Syntax_Print.lid_to_string l1)
in (let _0_232 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _0_233 _0_232)))
in ((_0_234), (env.range))))))
end
| Some (uu____3431, uu____3432, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Syntax_Const.effect_GTot_lid)))) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end
| uu____3463 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : FStar_Syntax_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____3479 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))))
in (match (uu____3479) with
| None -> begin
(failwith (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str))
end
| Some (md) -> begin
(

let uu____3493 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____3493) with
| (uu____3500, s) -> begin
(

let s = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____3508))::((wp, uu____3510))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____3532 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (Some (res_u)))
end
| uu____3559 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (Some (res_u)))
end
| uu____3560 -> begin
(

let eff_name = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (let _0_237 = (get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_236 = (let _0_235 = (FStar_Syntax_Syntax.as_arg res_t)
in (_0_235)::[])
in ((null_wp), (_0_236)))))) None _0_237))
in (FStar_Syntax_Syntax.mk_Comp (let _0_239 = (let _0_238 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (_0_238)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = _0_239; FStar_Syntax_Syntax.flags = []}))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect (ne, uu____3583) -> begin
(

let effects = (

let uu___112_3585 = env.effects
in {decls = (ne)::env.effects.decls; order = uu___112_3585.order; joins = uu___112_3585.joins})
in (

let uu___113_3586 = env
in {solver = uu___113_3586.solver; range = uu___113_3586.range; curmodule = uu___113_3586.curmodule; gamma = uu___113_3586.gamma; gamma_cache = uu___113_3586.gamma_cache; modules = uu___113_3586.modules; expected_typ = uu___113_3586.expected_typ; sigtab = uu___113_3586.sigtab; is_pattern = uu___113_3586.is_pattern; instantiate_imp = uu___113_3586.instantiate_imp; effects = effects; generalize = uu___113_3586.generalize; letrecs = uu___113_3586.letrecs; top_level = uu___113_3586.top_level; check_uvars = uu___113_3586.check_uvars; use_eq = uu___113_3586.use_eq; is_iface = uu___113_3586.is_iface; admit = uu___113_3586.admit; lax = uu___113_3586.lax; lax_universes = uu___113_3586.lax_universes; type_of = uu___113_3586.type_of; universe_of = uu___113_3586.universe_of; use_bv_sorts = uu___113_3586.use_bv_sorts; qname_and_index = uu___113_3586.qname_and_index}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, uu____3588) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _0_240 = (e1.mlift r wp1)
in (e2.mlift r _0_240)))})
in (

let mk_lift = (fun lift_t r wp1 -> (

let uu____3610 = (inst_tscheme lift_t)
in (match (uu____3610) with
| (uu____3615, lift_t) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_244 = (let _0_243 = (FStar_Syntax_Syntax.as_arg r)
in (let _0_242 = (let _0_241 = (FStar_Syntax_Syntax.as_arg wp1)
in (_0_241)::[])
in (_0_243)::_0_242))
in ((lift_t), (_0_244)))))) None wp1.FStar_Syntax_Syntax.pos)
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

let arg = (let _0_245 = (FStar_Ident.lid_of_path (("ARG")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _0_245 FStar_Syntax_Syntax.Delta_constant None))
in (

let wp = (let _0_246 = (FStar_Ident.lid_of_path (("WP")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _0_246 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Print.term_to_string (l arg wp)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Syntax_Syntax.mname)))
in (

let find_edge = (fun order uu____3668 -> (match (uu____3668) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_247 -> Some (_0_247)))
end
| uu____3677 -> begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _0_251 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____3693 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____3698 -> begin
(

let uu____3699 = (let _0_249 = (find_edge order ((i), (k)))
in (let _0_248 = (find_edge order ((k), (j)))
in ((_0_249), (_0_248))))
in (match (uu____3699) with
| (Some (e1), Some (e2)) -> begin
(let _0_250 = (compose_edges e1 e2)
in (_0_250)::[])
end
| uu____3711 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order _0_251))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in ((FStar_All.pipe_right order (FStar_List.iter (fun edge -> (

let uu____3723 = ((FStar_Ident.lid_equals edge.msource FStar_Syntax_Const.effect_DIV_lid) && (let _0_252 = (lookup_effect_quals env edge.mtarget)
in (FStar_All.pipe_right _0_252 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____3723) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_254 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge.mtarget.FStar_Ident.str)
in (let _0_253 = (get_range env)
in ((_0_254), (_0_253)))))))
end
| uu____3725 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____3819 = (let _0_256 = (find_edge order ((i), (k)))
in (let _0_255 = (find_edge order ((j), (k)))
in ((_0_256), (_0_255))))
in (match (uu____3819) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, uu____3845, uu____3846) -> begin
(

let uu____3850 = ((FStar_Util.is_some (find_edge order ((k), (ub)))) && (not ((FStar_Util.is_some (find_edge order ((ub), (k)))))))
in (match (uu____3850) with
| true -> begin
Some (((k), (ik), (jk)))
end
| uu____3858 -> begin
bopt
end))
end)
end
| uu____3859 -> begin
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

let uu___114_3938 = env.effects
in {decls = uu___114_3938.decls; order = order; joins = joins})
in (

let uu___115_3939 = env
in {solver = uu___115_3939.solver; range = uu___115_3939.range; curmodule = uu___115_3939.curmodule; gamma = uu___115_3939.gamma; gamma_cache = uu___115_3939.gamma_cache; modules = uu___115_3939.modules; expected_typ = uu___115_3939.expected_typ; sigtab = uu___115_3939.sigtab; is_pattern = uu___115_3939.is_pattern; instantiate_imp = uu___115_3939.instantiate_imp; effects = effects; generalize = uu___115_3939.generalize; letrecs = uu___115_3939.letrecs; top_level = uu___115_3939.top_level; check_uvars = uu___115_3939.check_uvars; use_eq = uu___115_3939.use_eq; is_iface = uu___115_3939.is_iface; admit = uu___115_3939.admit; lax = uu___115_3939.lax; lax_universes = uu___115_3939.lax_universes; type_of = uu___115_3939.type_of; universe_of = uu___115_3939.universe_of; use_bv_sorts = uu___115_3939.use_bv_sorts; qname_and_index = uu___115_3939.qname_and_index})));
))))))))))))
end
| uu____3940 -> begin
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
(let _0_257 = (push x rest)
in (local)::_0_257)
end))
in (

let uu___116_3965 = env
in (let _0_258 = (push s env.gamma)
in {solver = uu___116_3965.solver; range = uu___116_3965.range; curmodule = uu___116_3965.curmodule; gamma = _0_258; gamma_cache = uu___116_3965.gamma_cache; modules = uu___116_3965.modules; expected_typ = uu___116_3965.expected_typ; sigtab = uu___116_3965.sigtab; is_pattern = uu___116_3965.is_pattern; instantiate_imp = uu___116_3965.instantiate_imp; effects = uu___116_3965.effects; generalize = uu___116_3965.generalize; letrecs = uu___116_3965.letrecs; top_level = uu___116_3965.top_level; check_uvars = uu___116_3965.check_uvars; use_eq = uu___116_3965.use_eq; is_iface = uu___116_3965.is_iface; admit = uu___116_3965.admit; lax = uu___116_3965.lax; lax_universes = uu___116_3965.lax_universes; type_of = uu___116_3965.type_of; universe_of = uu___116_3965.universe_of; use_bv_sorts = uu___116_3965.use_bv_sorts; qname_and_index = uu___116_3965.qname_and_index}))))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___117_3991 = env
in {solver = uu___117_3991.solver; range = uu___117_3991.range; curmodule = uu___117_3991.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___117_3991.gamma_cache; modules = uu___117_3991.modules; expected_typ = uu___117_3991.expected_typ; sigtab = uu___117_3991.sigtab; is_pattern = uu___117_3991.is_pattern; instantiate_imp = uu___117_3991.instantiate_imp; effects = uu___117_3991.effects; generalize = uu___117_3991.generalize; letrecs = uu___117_3991.letrecs; top_level = uu___117_3991.top_level; check_uvars = uu___117_3991.check_uvars; use_eq = uu___117_3991.use_eq; is_iface = uu___117_3991.is_iface; admit = uu___117_3991.admit; lax = uu___117_3991.lax; lax_universes = uu___117_3991.lax_universes; type_of = uu___117_3991.type_of; universe_of = uu___117_3991.universe_of; use_bv_sorts = uu___117_3991.use_bv_sorts; qname_and_index = uu___117_3991.qname_and_index}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env uu____4007 -> (match (uu____4007) with
| (x, uu____4011) -> begin
(push_bv env x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x) -> begin
(

let x = (

let uu___118_4031 = x
in {FStar_Syntax_Syntax.ppname = uu___118_4031.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_4031.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (Prims.snd t)})
in Binding_var (x))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___119_4061 = env
in {solver = uu___119_4061.solver; range = uu___119_4061.range; curmodule = uu___119_4061.curmodule; gamma = []; gamma_cache = uu___119_4061.gamma_cache; modules = (m)::env.modules; expected_typ = None; sigtab = uu___119_4061.sigtab; is_pattern = uu___119_4061.is_pattern; instantiate_imp = uu___119_4061.instantiate_imp; effects = uu___119_4061.effects; generalize = uu___119_4061.generalize; letrecs = uu___119_4061.letrecs; top_level = uu___119_4061.top_level; check_uvars = uu___119_4061.check_uvars; use_eq = uu___119_4061.use_eq; is_iface = uu___119_4061.is_iface; admit = uu___119_4061.admit; lax = uu___119_4061.lax; lax_universes = uu___119_4061.lax_universes; type_of = uu___119_4061.type_of; universe_of = uu___119_4061.universe_of; use_bv_sorts = uu___119_4061.use_bv_sorts; qname_and_index = uu___119_4061.qname_and_index});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env x -> (push_local_binding env (Binding_univ (x)))) env xs))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___120_4076 = env
in {solver = uu___120_4076.solver; range = uu___120_4076.range; curmodule = uu___120_4076.curmodule; gamma = uu___120_4076.gamma; gamma_cache = uu___120_4076.gamma_cache; modules = uu___120_4076.modules; expected_typ = Some (t); sigtab = uu___120_4076.sigtab; is_pattern = uu___120_4076.is_pattern; instantiate_imp = uu___120_4076.instantiate_imp; effects = uu___120_4076.effects; generalize = uu___120_4076.generalize; letrecs = uu___120_4076.letrecs; top_level = uu___120_4076.top_level; check_uvars = uu___120_4076.check_uvars; use_eq = false; is_iface = uu___120_4076.is_iface; admit = uu___120_4076.admit; lax = uu___120_4076.lax; lax_universes = uu___120_4076.lax_universes; type_of = uu___120_4076.type_of; universe_of = uu___120_4076.universe_of; use_bv_sorts = uu___120_4076.use_bv_sorts; qname_and_index = uu___120_4076.qname_and_index}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ Prims.option) = (fun env_ -> (let _0_259 = (expected_typ env_)
in (((

let uu___121_4093 = env_
in {solver = uu___121_4093.solver; range = uu___121_4093.range; curmodule = uu___121_4093.curmodule; gamma = uu___121_4093.gamma; gamma_cache = uu___121_4093.gamma_cache; modules = uu___121_4093.modules; expected_typ = None; sigtab = uu___121_4093.sigtab; is_pattern = uu___121_4093.is_pattern; instantiate_imp = uu___121_4093.instantiate_imp; effects = uu___121_4093.effects; generalize = uu___121_4093.generalize; letrecs = uu___121_4093.letrecs; top_level = uu___121_4093.top_level; check_uvars = uu___121_4093.check_uvars; use_eq = false; is_iface = uu___121_4093.is_iface; admit = uu___121_4093.admit; lax = uu___121_4093.lax; lax_universes = uu___121_4093.lax_universes; type_of = uu___121_4093.type_of; universe_of = uu___121_4093.universe_of; use_bv_sorts = uu___121_4093.use_bv_sorts; qname_and_index = uu___121_4093.qname_and_index})), (_0_259))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
(let _0_260 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___103_4108 -> (match (uu___103_4108) with
| Binding_sig (uu____4110, se) -> begin
(se)::[]
end
| uu____4114 -> begin
[]
end))))
in (FStar_All.pipe_right _0_260 FStar_List.rev))
end
| uu____4115 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___122_4117 = env
in {solver = uu___122_4117.solver; range = uu___122_4117.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___122_4117.gamma_cache; modules = (m)::env.modules; expected_typ = uu___122_4117.expected_typ; sigtab = uu___122_4117.sigtab; is_pattern = uu___122_4117.is_pattern; instantiate_imp = uu___122_4117.instantiate_imp; effects = uu___122_4117.effects; generalize = uu___122_4117.generalize; letrecs = uu___122_4117.letrecs; top_level = uu___122_4117.top_level; check_uvars = uu___122_4117.check_uvars; use_eq = uu___122_4117.use_eq; is_iface = uu___122_4117.is_iface; admit = uu___122_4117.admit; lax = uu___122_4117.lax; lax_universes = uu___122_4117.lax_universes; type_of = uu___122_4117.type_of; universe_of = uu___122_4117.universe_of; use_bv_sorts = uu___122_4117.use_bv_sorts; qname_and_index = uu___122_4117.qname_and_index});
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
| (Binding_univ (uu____4167))::tl -> begin
(aux out tl)
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _0_262 = (let _0_261 = (FStar_Syntax_Free.uvars t)
in (ext out _0_261))
in (aux _0_262 tl))
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
(let _0_264 = (let _0_263 = (FStar_Syntax_Free.univs t)
in (ext out _0_263))
in (aux _0_264 tl))
end
| (Binding_sig (uu____4234))::uu____4235 -> begin
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
| (Binding_sig_inst (uu____4272))::tl -> begin
(aux out tl)
end
| (Binding_univ (uname))::tl -> begin
(let _0_265 = (FStar_Util.set_add uname out)
in (aux _0_265 tl))
end
| ((Binding_lid (_, (_, t)))::tl) | ((Binding_var ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}))::tl) -> begin
(let _0_267 = (let _0_266 = (FStar_Syntax_Free.univnames t)
in (ext out _0_266))
in (aux _0_267 tl))
end
| (Binding_sig (uu____4294))::uu____4295 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___104_4311 -> (match (uu___104_4311) with
| Binding_var (x) -> begin
(x)::[]
end
| (Binding_lid (_)) | (Binding_sig (_)) | (Binding_univ (_)) | (Binding_sig_inst (_)) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _0_269 = (let _0_268 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right _0_268 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right _0_269 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___105_4372 -> (match (uu___105_4372) with
| Binding_sig (lids, uu____4376) -> begin
(FStar_List.append lids keys)
end
| uu____4379 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____4381 v keys -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys)) keys)))


let dummy_solver : solver_t = {init = (fun uu____4385 -> ()); push = (fun uu____4386 -> ()); pop = (fun uu____4387 -> ()); mark = (fun uu____4388 -> ()); reset_mark = (fun uu____4389 -> ()); commit_mark = (fun uu____4390 -> ()); encode_modul = (fun uu____4391 uu____4392 -> ()); encode_sig = (fun uu____4393 uu____4394 -> ()); solve = (fun uu____4395 uu____4396 uu____4397 -> ()); is_trivial = (fun uu____4401 uu____4402 -> false); finish = (fun uu____4403 -> ()); refresh = (fun uu____4404 -> ())}




