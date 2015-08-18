
type binding =
| Binding_var of (Microsoft_FStar_Absyn_Syntax.bvvdef * Microsoft_FStar_Absyn_Syntax.typ)
| Binding_typ of (Microsoft_FStar_Absyn_Syntax.btvdef * Microsoft_FStar_Absyn_Syntax.knd)
| Binding_lid of (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.typ)
| Binding_sig of Microsoft_FStar_Absyn_Syntax.sigelt

let is_Binding_var = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_typ = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_lid = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_sig = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_var (_29_16) -> begin
_29_16
end))

let ___Binding_typ____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_typ (_29_19) -> begin
_29_19
end))

let ___Binding_lid____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_lid (_29_22) -> begin
_29_22
end))

let ___Binding_sig____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_sig (_29_25) -> begin
_29_25
end))

type sigtable =
Microsoft_FStar_Absyn_Syntax.sigelt Support.Microsoft.FStar.Util.smap

let default_table_size = 200

let strlid_of_sigelt = (fun ( se ) -> (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
(let _100_59 = (Microsoft_FStar_Absyn_Syntax.text_of_lid l)
in Some (_100_59))
end))

let signature_to_sigtables = (fun ( s ) -> (let ht = (Support.Microsoft.FStar.Util.smap_create default_table_size)
in (let _29_35 = (Support.List.iter (fun ( se ) -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun ( l ) -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun ( mods ) -> (let _100_66 = (Support.List.collect (fun ( _29_41 ) -> (match (_29_41) with
| (_29_39, m) -> begin
m.Microsoft_FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _100_66)))

type level =
| Expr
| Type
| Kind

let is_Expr = (fun ( _discr_ ) -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type = (fun ( _discr_ ) -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind = (fun ( _discr_ ) -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

type mlift =
Microsoft_FStar_Absyn_Syntax.typ  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  Microsoft_FStar_Absyn_Syntax.typ

type edge =
{msource : Microsoft_FStar_Absyn_Syntax.lident; mtarget : Microsoft_FStar_Absyn_Syntax.lident; mlift : mlift}

let is_Mkedge = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkedge"))

type effects =
{decls : Microsoft_FStar_Absyn_Syntax.eff_decl list; order : edge list; joins : (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.lident * mlift * mlift) list}

let is_Mkeffects = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkeffects"))

type env =
{solver : solver_t; range : Support.Microsoft.FStar.Range.range; curmodule : Microsoft_FStar_Absyn_Syntax.lident; gamma : binding list; modules : Microsoft_FStar_Absyn_Syntax.modul list; expected_typ : Microsoft_FStar_Absyn_Syntax.typ option; level : level; sigtab : sigtable list; is_pattern : bool; instantiate_targs : bool; instantiate_vargs : bool; effects : effects; generalize : bool; letrecs : (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.typ) list; top_level : bool; check_uvars : bool; use_eq : bool; is_iface : bool; admit : bool; default_effects : (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.lident) list} 
 and solver_t =
{init : env  ->  unit; push : string  ->  unit; pop : string  ->  unit; mark : string  ->  unit; reset_mark : string  ->  unit; commit_mark : string  ->  unit; encode_modul : env  ->  Microsoft_FStar_Absyn_Syntax.modul  ->  unit; encode_sig : env  ->  Microsoft_FStar_Absyn_Syntax.sigelt  ->  unit; solve : env  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  unit; is_trivial : env  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  bool; finish : unit  ->  unit; refresh : unit  ->  unit}

let is_Mkenv = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv"))

let is_Mksolver_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mksolver_t"))

let bound_vars = (fun ( env ) -> (Support.All.pipe_right env.gamma (Support.List.collect (fun ( _29_1 ) -> (match (_29_1) with
| Binding_typ ((a, k)) -> begin
(let _100_292 = (Support.All.pipe_left (fun ( _100_291 ) -> Support.Microsoft.FStar.Util.Inl (_100_291)) (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_100_292)::[])
end
| Binding_var ((x, t)) -> begin
(let _100_294 = (Support.All.pipe_left (fun ( _100_293 ) -> Support.Microsoft.FStar.Util.Inr (_100_293)) (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_100_294)::[])
end
| Binding_lid (_29_95) -> begin
[]
end
| Binding_sig (_29_98) -> begin
[]
end)))))

let has_interface = (fun ( env ) ( l ) -> (Support.All.pipe_right env.modules (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m.Microsoft_FStar_Absyn_Syntax.is_interface && (Microsoft_FStar_Absyn_Syntax.lid_equals m.Microsoft_FStar_Absyn_Syntax.name l))))))

let debug = (fun ( env ) ( l ) -> ((let _100_305 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.All.pipe_right _100_305 (Support.Microsoft.FStar.Util.for_some (fun ( x ) -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))))) && (Microsoft_FStar_Options.debug_level_geq l)))

let show = (fun ( env ) -> (let _100_309 = (Support.ST.read Microsoft_FStar_Options.show_signatures)
in (Support.All.pipe_right _100_309 (Support.Microsoft.FStar.Util.for_some (fun ( x ) -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))))))

let new_sigtab = (fun ( _29_108 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun ( env ) -> (Support.List.hd env.sigtab))

let push = (fun ( env ) ( msg ) -> (let _29_112 = (env.solver.push msg)
in (let _29_114 = env
in (let _100_319 = (let _100_318 = (let _100_317 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_copy _100_317))
in (_100_318)::env.sigtab)
in {solver = _29_114.solver; range = _29_114.range; curmodule = _29_114.curmodule; gamma = _29_114.gamma; modules = _29_114.modules; expected_typ = _29_114.expected_typ; level = _29_114.level; sigtab = _100_319; is_pattern = _29_114.is_pattern; instantiate_targs = _29_114.instantiate_targs; instantiate_vargs = _29_114.instantiate_vargs; effects = _29_114.effects; generalize = _29_114.generalize; letrecs = _29_114.letrecs; top_level = _29_114.top_level; check_uvars = _29_114.check_uvars; use_eq = _29_114.use_eq; is_iface = _29_114.is_iface; admit = _29_114.admit; default_effects = _29_114.default_effects}))))

let mark = (fun ( env ) -> (let _29_117 = (env.solver.mark "USER MARK")
in (let _29_119 = env
in (let _100_324 = (let _100_323 = (let _100_322 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_copy _100_322))
in (_100_323)::env.sigtab)
in {solver = _29_119.solver; range = _29_119.range; curmodule = _29_119.curmodule; gamma = _29_119.gamma; modules = _29_119.modules; expected_typ = _29_119.expected_typ; level = _29_119.level; sigtab = _100_324; is_pattern = _29_119.is_pattern; instantiate_targs = _29_119.instantiate_targs; instantiate_vargs = _29_119.instantiate_vargs; effects = _29_119.effects; generalize = _29_119.generalize; letrecs = _29_119.letrecs; top_level = _29_119.top_level; check_uvars = _29_119.check_uvars; use_eq = _29_119.use_eq; is_iface = _29_119.is_iface; admit = _29_119.admit; default_effects = _29_119.default_effects}))))

let commit_mark = (fun ( env ) -> (let _29_122 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_29_126::tl -> begin
(hd)::tl
end
| _29_131 -> begin
(Support.All.failwith "Impossible")
end)
in (let _29_133 = env
in {solver = _29_133.solver; range = _29_133.range; curmodule = _29_133.curmodule; gamma = _29_133.gamma; modules = _29_133.modules; expected_typ = _29_133.expected_typ; level = _29_133.level; sigtab = sigtab; is_pattern = _29_133.is_pattern; instantiate_targs = _29_133.instantiate_targs; instantiate_vargs = _29_133.instantiate_vargs; effects = _29_133.effects; generalize = _29_133.generalize; letrecs = _29_133.letrecs; top_level = _29_133.top_level; check_uvars = _29_133.check_uvars; use_eq = _29_133.use_eq; is_iface = _29_133.is_iface; admit = _29_133.admit; default_effects = _29_133.default_effects}))))

let reset_mark = (fun ( env ) -> (let _29_136 = (env.solver.reset_mark "USER MARK")
in (let _29_138 = env
in (let _100_329 = (Support.List.tl env.sigtab)
in {solver = _29_138.solver; range = _29_138.range; curmodule = _29_138.curmodule; gamma = _29_138.gamma; modules = _29_138.modules; expected_typ = _29_138.expected_typ; level = _29_138.level; sigtab = _100_329; is_pattern = _29_138.is_pattern; instantiate_targs = _29_138.instantiate_targs; instantiate_vargs = _29_138.instantiate_vargs; effects = _29_138.effects; generalize = _29_138.generalize; letrecs = _29_138.letrecs; top_level = _29_138.top_level; check_uvars = _29_138.check_uvars; use_eq = _29_138.use_eq; is_iface = _29_138.is_iface; admit = _29_138.admit; default_effects = _29_138.default_effects}))))

let pop = (fun ( env ) ( msg ) -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(Support.All.failwith "Too many pops")
end
| _29_148::tl -> begin
(let _29_150 = (env.solver.pop msg)
in (let _29_152 = env
in {solver = _29_152.solver; range = _29_152.range; curmodule = _29_152.curmodule; gamma = _29_152.gamma; modules = _29_152.modules; expected_typ = _29_152.expected_typ; level = _29_152.level; sigtab = tl; is_pattern = _29_152.is_pattern; instantiate_targs = _29_152.instantiate_targs; instantiate_vargs = _29_152.instantiate_vargs; effects = _29_152.effects; generalize = _29_152.generalize; letrecs = _29_152.letrecs; top_level = _29_152.top_level; check_uvars = _29_152.check_uvars; use_eq = _29_152.use_eq; is_iface = _29_152.is_iface; admit = _29_152.admit; default_effects = _29_152.default_effects}))
end))

let initial_env = (fun ( solver ) ( module_lid ) -> (let _100_339 = (let _100_338 = (new_sigtab ())
in (_100_338)::[])
in {solver = solver; range = Microsoft_FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _100_339; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

let effect_decl_opt = (fun ( env ) ( l ) -> (Support.All.pipe_right env.effects.decls (Support.Microsoft.FStar.Util.find_opt (fun ( d ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals d.Microsoft_FStar_Absyn_Syntax.mname l)))))

let name_not_found = (fun ( l ) -> (Support.Microsoft.FStar.Util.format1 "Name \"%s\" not found" l.Microsoft_FStar_Absyn_Syntax.str))

let variable_not_found = (fun ( v ) -> (let _100_348 = (Microsoft_FStar_Absyn_Print.strBvd v)
in (Support.Microsoft.FStar.Util.format1 "Variable \"%s\" not found" _100_348)))

let get_effect_decl = (fun ( env ) ( l ) -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _100_356 = (let _100_355 = (let _100_354 = (name_not_found l)
in (let _100_353 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (_100_354, _100_353)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_355))
in (raise (_100_356)))
end
| Some (md) -> begin
md
end))

let join = (fun ( env ) ( l1 ) ( l2 ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals l1 l2)) with
| true -> begin
(l1, (fun ( t ) ( wp ) -> wp), (fun ( t ) ( wp ) -> wp))
end
| false -> begin
(match ((Support.All.pipe_right env.effects.joins (Support.Microsoft.FStar.Util.find_opt (fun ( _29_181 ) -> (match (_29_181) with
| (m1, m2, _29_176, _29_178, _29_180) -> begin
((Microsoft_FStar_Absyn_Syntax.lid_equals l1 m1) && (Microsoft_FStar_Absyn_Syntax.lid_equals l2 m2))
end))))) with
| None -> begin
(let _100_412 = (let _100_411 = (let _100_410 = (let _100_409 = (Microsoft_FStar_Absyn_Print.sli l1)
in (let _100_408 = (Microsoft_FStar_Absyn_Print.sli l2)
in (Support.Microsoft.FStar.Util.format2 "Effects %s and %s cannot be composed" _100_409 _100_408)))
in (_100_410, env.range))
in Microsoft_FStar_Absyn_Syntax.Error (_100_411))
in (raise (_100_412)))
end
| Some ((_29_184, _29_186, m3, j1, j2)) -> begin
(m3, j1, j2)
end)
end))

let monad_leq = (fun ( env ) ( l1 ) ( l2 ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals l1 l2)) with
| true -> begin
Some ({msource = l1; mtarget = l2; mlift = (fun ( t ) ( wp ) -> wp)})
end
| false -> begin
(Support.All.pipe_right env.effects.order (Support.Microsoft.FStar.Util.find_opt (fun ( e ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals l1 e.msource) && (Microsoft_FStar_Absyn_Syntax.lid_equals l2 e.mtarget)))))
end))

let wp_sig_aux = (fun ( decls ) ( m ) -> (match ((Support.All.pipe_right decls (Support.Microsoft.FStar.Util.find_opt (fun ( d ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals d.Microsoft_FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _100_427 = (Support.Microsoft.FStar.Util.format1 "Impossible: declaration for monad %s not found" m.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _100_427))
end
| Some (md) -> begin
(match (md.Microsoft_FStar_Absyn_Syntax.signature.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _29_217)::(Support.Microsoft.FStar.Util.Inl (wp), _29_212)::(Support.Microsoft.FStar.Util.Inl (wlp), _29_207)::[], {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_effect; Microsoft_FStar_Absyn_Syntax.tk = _29_227; Microsoft_FStar_Absyn_Syntax.pos = _29_225; Microsoft_FStar_Absyn_Syntax.fvs = _29_223; Microsoft_FStar_Absyn_Syntax.uvs = _29_221})) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _29_233 -> begin
(Support.All.failwith "Impossible")
end)
end))

let wp_signature = (fun ( env ) ( m ) -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun ( env ) ( l ) -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun ( _29_240 ) -> (match (_29_240) with
| (l', m) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals l l')) with
| true -> begin
Some (m)
end
| false -> begin
None
end)
end))))

let build_lattice = (fun ( env ) ( se ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _29_245, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _29_2 ) -> (match (_29_2) with
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _29_255 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _29_259 = env
in {solver = _29_259.solver; range = _29_259.range; curmodule = _29_259.curmodule; gamma = _29_259.gamma; modules = _29_259.modules; expected_typ = _29_259.expected_typ; level = _29_259.level; sigtab = _29_259.sigtab; is_pattern = _29_259.is_pattern; instantiate_targs = _29_259.instantiate_targs; instantiate_vargs = _29_259.instantiate_vargs; effects = _29_259.effects; generalize = _29_259.generalize; letrecs = _29_259.letrecs; top_level = _29_259.top_level; check_uvars = _29_259.check_uvars; use_eq = _29_259.use_eq; is_iface = _29_259.is_iface; admit = _29_259.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _29_263)) -> begin
(let effects = (let _29_266 = env.effects
in {decls = (ne)::env.effects.decls; order = _29_266.order; joins = _29_266.joins})
in (let _29_269 = env
in {solver = _29_269.solver; range = _29_269.range; curmodule = _29_269.curmodule; gamma = _29_269.gamma; modules = _29_269.modules; expected_typ = _29_269.expected_typ; level = _29_269.level; sigtab = _29_269.sigtab; is_pattern = _29_269.is_pattern; instantiate_targs = _29_269.instantiate_targs; instantiate_vargs = _29_269.instantiate_vargs; effects = effects; generalize = _29_269.generalize; letrecs = _29_269.letrecs; top_level = _29_269.top_level; check_uvars = _29_269.check_uvars; use_eq = _29_269.use_eq; is_iface = _29_269.is_iface; admit = _29_269.admit; default_effects = _29_269.default_effects}))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((sub, _29_273)) -> begin
(let compose_edges = (fun ( e1 ) ( e2 ) -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun ( r ) ( wp1 ) -> (let _100_448 = (e1.mlift r wp1)
in (e2.mlift r _100_448)))})
in (let mk_lift = (fun ( lift_t ) ( r ) ( wp1 ) -> (let _100_459 = (let _100_458 = (let _100_457 = (Microsoft_FStar_Absyn_Syntax.targ r)
in (let _100_456 = (let _100_455 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (_100_455)::[])
in (_100_457)::_100_456))
in (lift_t, _100_458))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _100_459 None wp1.Microsoft_FStar_Absyn_Syntax.pos)))
in (let edge = {msource = sub.Microsoft_FStar_Absyn_Syntax.source; mtarget = sub.Microsoft_FStar_Absyn_Syntax.target; mlift = (mk_lift sub.Microsoft_FStar_Absyn_Syntax.lift)}
in (let id_edge = (fun ( l ) -> {msource = sub.Microsoft_FStar_Absyn_Syntax.source; mtarget = sub.Microsoft_FStar_Absyn_Syntax.target; mlift = (fun ( t ) ( wp ) -> wp)})
in (let print_mlift = (fun ( l ) -> (let arg = (let _100_476 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Util.ftv _100_476 Microsoft_FStar_Absyn_Syntax.mk_Kind_type))
in (let wp = (let _100_477 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("WP")::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Util.ftv _100_477 Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _100_478 = (l arg wp)
in (Microsoft_FStar_Absyn_Print.typ_to_string _100_478)))))
in (let order = (edge)::env.effects.order
in (let ms = (Support.All.pipe_right env.effects.decls (Support.List.map (fun ( e ) -> e.Microsoft_FStar_Absyn_Syntax.mname)))
in (let find_edge = (fun ( order ) ( _29_301 ) -> (match (_29_301) with
| (i, j) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals i j)) with
| true -> begin
(Support.All.pipe_right (id_edge i) (fun ( _100_484 ) -> Some (_100_484)))
end
| false -> begin
(Support.All.pipe_right order (Support.Microsoft.FStar.Util.find_opt (fun ( e ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals e.msource i) && (Microsoft_FStar_Absyn_Syntax.lid_equals e.mtarget j)))))
end)
end))
in (let order = (Support.All.pipe_right ms (Support.List.fold_left (fun ( order ) ( k ) -> (let _100_492 = (Support.All.pipe_right ms (Support.List.collect (fun ( i ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals i k)) with
| true -> begin
[]
end
| false -> begin
(Support.All.pipe_right ms (Support.List.collect (fun ( j ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals j k)) with
| true -> begin
[]
end
| false -> begin
(match ((let _100_491 = (find_edge order (i, k))
in (let _100_490 = (find_edge order (k, j))
in (_100_491, _100_490)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _29_313 -> begin
[]
end)
end))))
end))))
in (Support.List.append order _100_492))) order))
in (let order = (Support.Microsoft.FStar.Util.remove_dups (fun ( e1 ) ( e2 ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals e1.msource e2.msource) && (Microsoft_FStar_Absyn_Syntax.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (Support.All.pipe_right ms (Support.List.collect (fun ( i ) -> (Support.All.pipe_right ms (Support.List.collect (fun ( j ) -> (let join_opt = (Support.All.pipe_right ms (Support.List.fold_left (fun ( bopt ) ( k ) -> (match ((let _100_500 = (find_edge order (i, k))
in (let _100_499 = (find_edge order (j, k))
in (_100_500, _100_499)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some ((ub, _29_330, _29_332)) -> begin
(match (((let _100_501 = (find_edge order (k, ub))
in (Support.Microsoft.FStar.Util.is_some _100_501)) && (not ((let _100_502 = (find_edge order (ub, k))
in (Support.Microsoft.FStar.Util.is_some _100_502)))))) with
| true -> begin
Some ((k, ik, jk))
end
| false -> begin
bopt
end)
end)
end
| _29_336 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some ((k, e1, e2)) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _29_345 = env.effects
in {decls = _29_345.decls; order = order; joins = joins})
in (let _29_348 = env
in {solver = _29_348.solver; range = _29_348.range; curmodule = _29_348.curmodule; gamma = _29_348.gamma; modules = _29_348.modules; expected_typ = _29_348.expected_typ; level = _29_348.level; sigtab = _29_348.sigtab; is_pattern = _29_348.is_pattern; instantiate_targs = _29_348.instantiate_targs; instantiate_vargs = _29_348.instantiate_vargs; effects = effects; generalize = _29_348.generalize; letrecs = _29_348.letrecs; top_level = _29_348.top_level; check_uvars = _29_348.check_uvars; use_eq = _29_348.use_eq; is_iface = _29_348.is_iface; admit = _29_348.admit; default_effects = _29_348.default_effects})))))))))))))
end
| _29_351 -> begin
env
end))

let rec add_sigelt = (fun ( env ) ( se ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _29_356, _29_358, _29_360)) -> begin
(add_sigelts env ses)
end
| _29_364 -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun ( l ) -> (let _100_510 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_add _100_510 l.Microsoft_FStar_Absyn_Syntax.str se))) lids))
end))
and add_sigelts = (fun ( env ) ( ses ) -> (Support.All.pipe_right ses (Support.List.iter (add_sigelt env))))

let empty_lid = (let _100_514 = (let _100_513 = (Microsoft_FStar_Absyn_Syntax.id_of_text "")
in (_100_513)::[])
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _100_514))

let finish_module = (fun ( env ) ( m ) -> (let sigs = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals m.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)) with
| true -> begin
(Support.All.pipe_right env.gamma (Support.List.collect (fun ( _29_3 ) -> (match (_29_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _29_375 -> begin
[]
end))))
end
| false -> begin
m.Microsoft_FStar_Absyn_Syntax.exports
end)
in (let _29_377 = (add_sigelts env sigs)
in (let _29_379 = env
in {solver = _29_379.solver; range = _29_379.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _29_379.expected_typ; level = _29_379.level; sigtab = _29_379.sigtab; is_pattern = _29_379.is_pattern; instantiate_targs = _29_379.instantiate_targs; instantiate_vargs = _29_379.instantiate_vargs; effects = _29_379.effects; generalize = _29_379.generalize; letrecs = _29_379.letrecs; top_level = _29_379.top_level; check_uvars = _29_379.check_uvars; use_eq = _29_379.use_eq; is_iface = _29_379.is_iface; admit = _29_379.admit; default_effects = _29_379.default_effects}))))

let set_level = (fun ( env ) ( level ) -> (let _29_383 = env
in {solver = _29_383.solver; range = _29_383.range; curmodule = _29_383.curmodule; gamma = _29_383.gamma; modules = _29_383.modules; expected_typ = _29_383.expected_typ; level = level; sigtab = _29_383.sigtab; is_pattern = _29_383.is_pattern; instantiate_targs = _29_383.instantiate_targs; instantiate_vargs = _29_383.instantiate_vargs; effects = _29_383.effects; generalize = _29_383.generalize; letrecs = _29_383.letrecs; top_level = _29_383.top_level; check_uvars = _29_383.check_uvars; use_eq = _29_383.use_eq; is_iface = _29_383.is_iface; admit = _29_383.admit; default_effects = _29_383.default_effects}))

let is_level = (fun ( env ) ( level ) -> (env.level = level))

let modules = (fun ( env ) -> env.modules)

let current_module = (fun ( env ) -> env.curmodule)

let set_current_module = (fun ( env ) ( lid ) -> (let _29_391 = env
in {solver = _29_391.solver; range = _29_391.range; curmodule = lid; gamma = _29_391.gamma; modules = _29_391.modules; expected_typ = _29_391.expected_typ; level = _29_391.level; sigtab = _29_391.sigtab; is_pattern = _29_391.is_pattern; instantiate_targs = _29_391.instantiate_targs; instantiate_vargs = _29_391.instantiate_vargs; effects = _29_391.effects; generalize = _29_391.generalize; letrecs = _29_391.letrecs; top_level = _29_391.top_level; check_uvars = _29_391.check_uvars; use_eq = _29_391.use_eq; is_iface = _29_391.is_iface; admit = _29_391.admit; default_effects = _29_391.default_effects}))

let set_range = (fun ( e ) ( r ) -> (match ((r = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
e
end
| false -> begin
(let _29_395 = e
in {solver = _29_395.solver; range = r; curmodule = _29_395.curmodule; gamma = _29_395.gamma; modules = _29_395.modules; expected_typ = _29_395.expected_typ; level = _29_395.level; sigtab = _29_395.sigtab; is_pattern = _29_395.is_pattern; instantiate_targs = _29_395.instantiate_targs; instantiate_vargs = _29_395.instantiate_vargs; effects = _29_395.effects; generalize = _29_395.generalize; letrecs = _29_395.letrecs; top_level = _29_395.top_level; check_uvars = _29_395.check_uvars; use_eq = _29_395.use_eq; is_iface = _29_395.is_iface; admit = _29_395.admit; default_effects = _29_395.default_effects})
end))

let get_range = (fun ( e ) -> e.range)

let find_in_sigtab = (fun ( env ) ( lid ) -> (let _100_547 = (sigtab env)
in (let _100_546 = (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)
in (Support.Microsoft.FStar.Util.smap_try_find _100_547 _100_546))))

let lookup_bvvdef = (fun ( env ) ( bvvd ) -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun ( _29_4 ) -> (match (_29_4) with
| Binding_var ((id, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _29_408 -> begin
None
end))))

let lookup_bvar = (fun ( env ) ( bv ) -> (match ((lookup_bvvdef env bv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _100_559 = (let _100_558 = (let _100_557 = (variable_not_found bv.Microsoft_FStar_Absyn_Syntax.v)
in (_100_557, (Microsoft_FStar_Absyn_Util.range_of_bvd bv.Microsoft_FStar_Absyn_Syntax.v)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_558))
in (raise (_100_559)))
end
| Some (t) -> begin
t
end))

let lookup_qname = (fun ( env ) ( lid ) -> (let in_cur_mod = (fun ( l ) -> (let cur = (current_module env)
in (match ((l.Microsoft_FStar_Absyn_Syntax.nsstr = cur.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
true
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.nsstr cur.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let lns = (Support.List.append l.Microsoft_FStar_Absyn_Syntax.ns ((l.Microsoft_FStar_Absyn_Syntax.ident)::[]))
in (let cur = (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[]))
in (let rec aux = (fun ( c ) ( l ) -> (match ((c, l)) with
| ([], _29_426) -> begin
true
end
| (_29_429, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.Microsoft_FStar_Absyn_Syntax.idText = hd'.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(aux tl tl')
end
| _29_440 -> begin
false
end))
in (aux cur lns))))
end
| false -> begin
false
end)
end)))
in (let cur_mod = (in_cur_mod lid)
in (let found = (match (cur_mod) with
| true -> begin
(Support.Microsoft.FStar.Util.find_map env.gamma (fun ( _29_5 ) -> (match (_29_5) with
| Binding_lid ((l, t)) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals lid l)) with
| true -> begin
Some (Support.Microsoft.FStar.Util.Inl (t))
end
| false -> begin
None
end)
end
| Binding_sig (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _29_449, _29_451, _29_453))) -> begin
(Support.Microsoft.FStar.Util.find_map ses (fun ( se ) -> (match ((let _100_572 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.All.pipe_right _100_572 (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid))))) with
| true -> begin
Some (Support.Microsoft.FStar.Util.Inr (se))
end
| false -> begin
None
end)))
end
| Binding_sig (s) -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (match ((Support.All.pipe_right lids (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid)))) with
| true -> begin
Some (Support.Microsoft.FStar.Util.Inr (s))
end
| false -> begin
None
end))
end
| _29_462 -> begin
None
end)))
end
| false -> begin
None
end)
in (match ((Support.Microsoft.FStar.Util.is_some found)) with
| true -> begin
found
end
| false -> begin
(match (((not (cur_mod)) || (has_interface env env.curmodule))) with
| true -> begin
(match ((find_in_sigtab env lid)) with
| Some (se) -> begin
Some (Support.Microsoft.FStar.Util.Inr (se))
end
| None -> begin
None
end)
end
| false -> begin
None
end)
end)))))

let lookup_datacon = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_29_470, t, _29_473, _29_475, _29_477, _29_479)))) -> begin
t
end
| _29_485 -> begin
(let _100_580 = (let _100_579 = (let _100_578 = (name_not_found lid)
in (let _100_577 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_100_578, _100_577)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_579))
in (raise (_100_580)))
end))

let lookup_kind_abbrev = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _29_492)))) -> begin
(l, binders, k)
end
| _29_498 -> begin
(let _100_588 = (let _100_587 = (let _100_586 = (name_not_found lid)
in (let _100_585 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_100_586, _100_585)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_587))
in (raise (_100_588)))
end))

let lookup_projector = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _29_503 ) -> (match (()) with
| () -> begin
(let _100_599 = (let _100_598 = (Support.Microsoft.FStar.Util.string_of_int i)
in (let _100_597 = (Microsoft_FStar_Absyn_Print.sli lid)
in (Support.Microsoft.FStar.Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _100_598 _100_597)))
in (Support.All.failwith _100_599))
end))
in (let t = (lookup_datacon env lid)
in (match ((let _100_600 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _100_600.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _29_507)) -> begin
(match (((i < 0) || (i >= (Support.List.length binders)))) with
| true -> begin
(fail ())
end
| false -> begin
(let b = (Support.List.nth binders i)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _100_601 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (Support.All.pipe_right _100_601 Support.Prims.fst))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _100_602 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (Support.All.pipe_right _100_602 Support.Prims.fst))
end))
end)
end
| _29_516 -> begin
(fail ())
end))))

let try_lookup_val_decl = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_29_520, t, q, _29_524)))) -> begin
Some ((t, q))
end
| _29_530 -> begin
None
end))

let lookup_val_decl = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_29_534, t, _29_537, _29_539)))) -> begin
t
end
| _29_545 -> begin
(let _100_614 = (let _100_613 = (let _100_612 = (name_not_found lid)
in (let _100_611 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_100_612, _100_611)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_613))
in (raise (_100_614)))
end))

let lookup_lid = (fun ( env ) ( lid ) -> (let not_found = (fun ( _29_549 ) -> (match (()) with
| () -> begin
(let _100_624 = (let _100_623 = (let _100_622 = (name_not_found lid)
in (let _100_621 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_100_622, _100_621)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_623))
in (raise (_100_624)))
end))
in (let mapper = (fun ( _29_6 ) -> (match (_29_6) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, {Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_29_596, lbs), _29_600, _29_602, _29_604))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (_29_610) -> begin
(Support.All.failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inr (lid') -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals lid lid')) with
| true -> begin
Some (lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
end
| false -> begin
None
end)
end)))
end
| t -> begin
None
end))
in (match ((let _100_628 = (lookup_qname env lid)
in (Support.Microsoft.FStar.Util.bind_opt _100_628 mapper))) with
| Some (t) -> begin
(let _29_618 = t
in (let _100_629 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in {Microsoft_FStar_Absyn_Syntax.n = _29_618.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _29_618.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _100_629; Microsoft_FStar_Absyn_Syntax.fvs = _29_618.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _29_618.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_29_624, _29_626, quals, _29_629)))) -> begin
(Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _29_7 ) -> (match (_29_7) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _29_637 -> begin
false
end))))
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_29_639, t, _29_642, _29_644, _29_646, _29_648)))) -> begin
true
end
| _29_654 -> begin
false
end))

let is_record = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_29_658, _29_660, _29_662, _29_664, _29_666, tags, _29_669)))) -> begin
(Support.Microsoft.FStar.Util.for_some (fun ( _29_8 ) -> (match (_29_8) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _29_682 -> begin
false
end)) tags)
end
| _29_684 -> begin
false
end))

let lookup_datacons_of_typ = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_29_688, _29_690, _29_692, _29_694, datas, _29_697, _29_699)))) -> begin
(let _100_646 = (Support.List.map (fun ( l ) -> (let _100_645 = (lookup_lid env l)
in (l, _100_645))) datas)
in Some (_100_646))
end
| _29_706 -> begin
None
end))

let lookup_effect_abbrev = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, c, quals, _29_714)))) -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _29_9 ) -> (match (_29_9) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _29_722 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((binders, c))
end)
end
| _29_724 -> begin
None
end))

let lookup_typ_abbrev = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _29_730, t, quals, _29_734)))) -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _29_10 ) -> (match (_29_10) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _29_742 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let t = (Microsoft_FStar_Absyn_Util.close_with_lam tps t)
in (let _100_657 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_100_657)))
end)
end
| _29_745 -> begin
None
end))

let lookup_btvdef = (fun ( env ) ( btvd ) -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun ( _29_11 ) -> (match (_29_11) with
| Binding_typ ((id, k)) when (Microsoft_FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _29_754 -> begin
None
end))))

let lookup_btvar = (fun ( env ) ( btv ) -> (match ((lookup_btvdef env btv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _100_669 = (let _100_668 = (let _100_667 = (variable_not_found btv.Microsoft_FStar_Absyn_Syntax.v)
in (_100_667, (Microsoft_FStar_Absyn_Util.range_of_bvd btv.Microsoft_FStar_Absyn_Syntax.v)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_668))
in (raise (_100_669)))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid = (fun ( env ) ( ftv ) -> (match ((lookup_qname env ftv)) with
| (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _, _, _, _))))) | (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, _, _, _))))) -> begin
(Microsoft_FStar_Absyn_Util.close_kind tps k)
end
| _29_788 -> begin
(let _100_677 = (let _100_676 = (let _100_675 = (name_not_found ftv)
in (let _100_674 = (Microsoft_FStar_Absyn_Syntax.range_of_lid ftv)
in (_100_675, _100_674)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_676))
in (raise (_100_677)))
end))

let is_projector = (fun ( env ) ( l ) -> (match ((lookup_qname env l)) with
| (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, quals, _))))) | (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _))))) -> begin
(Support.Microsoft.FStar.Util.for_some (fun ( _29_12 ) -> (match (_29_12) with
| Microsoft_FStar_Absyn_Syntax.Projector (_29_820) -> begin
true
end
| _29_823 -> begin
false
end)) quals)
end
| _29_825 -> begin
false
end))

let try_lookup_effect_lid = (fun ( env ) ( ftv ) -> (match ((lookup_qname env ftv)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _29_830)))) -> begin
(let _100_688 = (Microsoft_FStar_Absyn_Util.close_kind ne.Microsoft_FStar_Absyn_Syntax.binders ne.Microsoft_FStar_Absyn_Syntax.signature)
in (Support.All.pipe_right _100_688 (fun ( _100_687 ) -> Some (_100_687))))
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, _29_838, _29_840, _29_842)))) -> begin
(let _100_690 = (Microsoft_FStar_Absyn_Util.close_kind binders Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
in (Support.All.pipe_right _100_690 (fun ( _100_689 ) -> Some (_100_689))))
end
| _29_848 -> begin
None
end))

let lookup_effect_lid = (fun ( env ) ( ftv ) -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _100_698 = (let _100_697 = (let _100_696 = (name_not_found ftv)
in (let _100_695 = (Microsoft_FStar_Absyn_Syntax.range_of_lid ftv)
in (_100_696, _100_695)))
in Microsoft_FStar_Absyn_Syntax.Error (_100_697))
in (raise (_100_698)))
end
| Some (k) -> begin
k
end))

let lookup_operator = (fun ( env ) ( opname ) -> (let primName = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::((Support.String.strcat "_dummy_" opname.Microsoft_FStar_Absyn_Syntax.idText))::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun ( env ) ( s ) -> (build_lattice (let _29_859 = env
in {solver = _29_859.solver; range = _29_859.range; curmodule = _29_859.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _29_859.modules; expected_typ = _29_859.expected_typ; level = _29_859.level; sigtab = _29_859.sigtab; is_pattern = _29_859.is_pattern; instantiate_targs = _29_859.instantiate_targs; instantiate_vargs = _29_859.instantiate_vargs; effects = _29_859.effects; generalize = _29_859.generalize; letrecs = _29_859.letrecs; top_level = _29_859.top_level; check_uvars = _29_859.check_uvars; use_eq = _29_859.use_eq; is_iface = _29_859.is_iface; admit = _29_859.admit; default_effects = _29_859.default_effects}) s))

let push_local_binding = (fun ( env ) ( b ) -> (let _29_863 = env
in {solver = _29_863.solver; range = _29_863.range; curmodule = _29_863.curmodule; gamma = (b)::env.gamma; modules = _29_863.modules; expected_typ = _29_863.expected_typ; level = _29_863.level; sigtab = _29_863.sigtab; is_pattern = _29_863.is_pattern; instantiate_targs = _29_863.instantiate_targs; instantiate_vargs = _29_863.instantiate_vargs; effects = _29_863.effects; generalize = _29_863.generalize; letrecs = _29_863.letrecs; top_level = _29_863.top_level; check_uvars = _29_863.check_uvars; use_eq = _29_863.use_eq; is_iface = _29_863.is_iface; admit = _29_863.admit; default_effects = _29_863.default_effects}))

let uvars_in_env = (fun ( env ) -> (let no_uvs = (let _100_715 = (Microsoft_FStar_Absyn_Syntax.new_uv_set ())
in (let _100_714 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in (let _100_713 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _100_715; Microsoft_FStar_Absyn_Syntax.uvars_t = _100_714; Microsoft_FStar_Absyn_Syntax.uvars_e = _100_713})))
in (let ext = (fun ( out ) ( uvs ) -> (let _29_870 = out
in (let _100_722 = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_k uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (let _100_721 = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_t uvs.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _100_720 = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_e uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _100_722; Microsoft_FStar_Absyn_Syntax.uvars_t = _100_721; Microsoft_FStar_Absyn_Syntax.uvars_e = _100_720})))))
in (let rec aux = (fun ( out ) ( g ) -> (match (g) with
| [] -> begin
out
end
| (Binding_lid ((_, t))::tl) | (Binding_var ((_, t))::tl) -> begin
(let _100_728 = (let _100_727 = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (ext out _100_727))
in (aux _100_728 tl))
end
| Binding_typ ((_29_890, k))::tl -> begin
(let _100_730 = (let _100_729 = (Microsoft_FStar_Absyn_Util.uvars_in_kind k)
in (ext out _100_729))
in (aux _100_730 tl))
end
| Binding_sig (_29_898)::_29_896 -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module = (fun ( env ) ( m ) -> (let _29_903 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _29_905 = env
in {solver = _29_905.solver; range = _29_905.range; curmodule = _29_905.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _29_905.level; sigtab = _29_905.sigtab; is_pattern = _29_905.is_pattern; instantiate_targs = _29_905.instantiate_targs; instantiate_vargs = _29_905.instantiate_vargs; effects = _29_905.effects; generalize = _29_905.generalize; letrecs = _29_905.letrecs; top_level = _29_905.top_level; check_uvars = _29_905.check_uvars; use_eq = _29_905.use_eq; is_iface = _29_905.is_iface; admit = _29_905.admit; default_effects = _29_905.default_effects})))

let set_expected_typ = (fun ( env ) ( t ) -> (let _29_909 = env
in {solver = _29_909.solver; range = _29_909.range; curmodule = _29_909.curmodule; gamma = _29_909.gamma; modules = _29_909.modules; expected_typ = Some (t); level = _29_909.level; sigtab = _29_909.sigtab; is_pattern = _29_909.is_pattern; instantiate_targs = _29_909.instantiate_targs; instantiate_vargs = _29_909.instantiate_vargs; effects = _29_909.effects; generalize = _29_909.generalize; letrecs = _29_909.letrecs; top_level = _29_909.top_level; check_uvars = _29_909.check_uvars; use_eq = false; is_iface = _29_909.is_iface; admit = _29_909.admit; default_effects = _29_909.default_effects}))

let expected_typ = (fun ( env ) -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun ( env ) -> (let _100_743 = (expected_typ env)
in ((let _29_916 = env
in {solver = _29_916.solver; range = _29_916.range; curmodule = _29_916.curmodule; gamma = _29_916.gamma; modules = _29_916.modules; expected_typ = None; level = _29_916.level; sigtab = _29_916.sigtab; is_pattern = _29_916.is_pattern; instantiate_targs = _29_916.instantiate_targs; instantiate_vargs = _29_916.instantiate_vargs; effects = _29_916.effects; generalize = _29_916.generalize; letrecs = _29_916.letrecs; top_level = _29_916.top_level; check_uvars = _29_916.check_uvars; use_eq = false; is_iface = _29_916.is_iface; admit = _29_916.admit; default_effects = _29_916.default_effects}), _100_743)))

let fold_env = (fun ( env ) ( f ) ( a ) -> (Support.List.fold_right (fun ( e ) ( a ) -> (f a e)) env.gamma a))

let binding_of_binder = (fun ( b ) -> (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, a.Microsoft_FStar_Absyn_Syntax.sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
end))

let binders = (fun ( env ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (match (b) with
| Binding_var ((x, t)) -> begin
(let _100_761 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_100_761)::out)
end
| Binding_typ ((a, k)) -> begin
(let _100_762 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_100_762)::out)
end
| _29_940 -> begin
out
end)) [] env.gamma))

let t_binders = (fun ( env ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (match (b) with
| Binding_var (_29_945) -> begin
out
end
| Binding_typ ((a, k)) -> begin
(let _100_767 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_100_767)::out)
end
| _29_952 -> begin
out
end)) [] env.gamma))

let idents = (fun ( env ) -> (let _100_771 = (let _100_770 = (binders env)
in (Support.All.pipe_right _100_770 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Syntax.freevars_of_list _100_771)))

let lidents = (fun ( env ) -> (let keys = (Support.List.fold_left (fun ( keys ) ( _29_13 ) -> (match (_29_13) with
| Binding_sig (s) -> begin
(let _100_776 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (Support.List.append _100_776 keys))
end
| _29_960 -> begin
keys
end)) [] env.gamma)
in (let _100_781 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_fold _100_781 (fun ( _29_962 ) ( v ) ( keys ) -> (let _100_780 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt v)
in (Support.List.append _100_780 keys))) keys))))




