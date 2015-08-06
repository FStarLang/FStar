
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

type sigtable =
Microsoft_FStar_Absyn_Syntax.sigelt Support.Microsoft.FStar.Util.smap

let default_table_size = 200

let strlid_of_sigelt = (fun ( se ) -> (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
(let _70_11412 = (Microsoft_FStar_Absyn_Syntax.text_of_lid l)
in Some (_70_11412))
end))

let signature_to_sigtables = (fun ( s ) -> (let ht = (Support.Microsoft.FStar.Util.smap_create default_table_size)
in (let _29_31 = (Support.List.iter (fun ( se ) -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun ( l ) -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun ( mods ) -> (let _70_11419 = (Support.List.collect (fun ( _29_37 ) -> (match (_29_37) with
| (_29_35, m) -> begin
m.Microsoft_FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _70_11419)))

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
(let _70_11645 = (Support.All.pipe_left (fun ( _70_11644 ) -> Support.Microsoft.FStar.Util.Inl (_70_11644)) (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_11645)::[])
end
| Binding_var ((x, t)) -> begin
(let _70_11647 = (Support.All.pipe_left (fun ( _70_11646 ) -> Support.Microsoft.FStar.Util.Inr (_70_11646)) (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_11647)::[])
end
| Binding_lid (_29_91) -> begin
[]
end
| Binding_sig (_29_94) -> begin
[]
end)))))

let has_interface = (fun ( env ) ( l ) -> (Support.All.pipe_right env.modules (Support.Microsoft.FStar.Util.for_some (fun ( m ) -> (m.Microsoft_FStar_Absyn_Syntax.is_interface && (Microsoft_FStar_Absyn_Syntax.lid_equals m.Microsoft_FStar_Absyn_Syntax.name l))))))

let debug = (fun ( env ) ( l ) -> ((let _70_11658 = (Support.ST.read Microsoft_FStar_Options.debug)
in (Support.All.pipe_right _70_11658 (Support.Microsoft.FStar.Util.for_some (fun ( x ) -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))))) && (Microsoft_FStar_Options.debug_level_geq l)))

let show = (fun ( env ) -> (let _70_11662 = (Support.ST.read Microsoft_FStar_Options.show_signatures)
in (Support.All.pipe_right _70_11662 (Support.Microsoft.FStar.Util.for_some (fun ( x ) -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))))))

let new_sigtab = (fun ( _29_104 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun ( env ) -> (Support.List.hd env.sigtab))

let push = (fun ( env ) ( msg ) -> (let _29_108 = (env.solver.push msg)
in (let _29_110 = env
in (let _70_11672 = (let _70_11671 = (let _70_11670 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_copy _70_11670))
in (_70_11671)::env.sigtab)
in {solver = _29_110.solver; range = _29_110.range; curmodule = _29_110.curmodule; gamma = _29_110.gamma; modules = _29_110.modules; expected_typ = _29_110.expected_typ; level = _29_110.level; sigtab = _70_11672; is_pattern = _29_110.is_pattern; instantiate_targs = _29_110.instantiate_targs; instantiate_vargs = _29_110.instantiate_vargs; effects = _29_110.effects; generalize = _29_110.generalize; letrecs = _29_110.letrecs; top_level = _29_110.top_level; check_uvars = _29_110.check_uvars; use_eq = _29_110.use_eq; is_iface = _29_110.is_iface; admit = _29_110.admit; default_effects = _29_110.default_effects}))))

let mark = (fun ( env ) -> (let _29_113 = (env.solver.mark "USER MARK")
in (let _29_115 = env
in (let _70_11677 = (let _70_11676 = (let _70_11675 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_copy _70_11675))
in (_70_11676)::env.sigtab)
in {solver = _29_115.solver; range = _29_115.range; curmodule = _29_115.curmodule; gamma = _29_115.gamma; modules = _29_115.modules; expected_typ = _29_115.expected_typ; level = _29_115.level; sigtab = _70_11677; is_pattern = _29_115.is_pattern; instantiate_targs = _29_115.instantiate_targs; instantiate_vargs = _29_115.instantiate_vargs; effects = _29_115.effects; generalize = _29_115.generalize; letrecs = _29_115.letrecs; top_level = _29_115.top_level; check_uvars = _29_115.check_uvars; use_eq = _29_115.use_eq; is_iface = _29_115.is_iface; admit = _29_115.admit; default_effects = _29_115.default_effects}))))

let commit_mark = (fun ( env ) -> (let _29_118 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_29_122::tl -> begin
(hd)::tl
end
| _29_127 -> begin
(Support.All.failwith "Impossible")
end)
in (let _29_129 = env
in {solver = _29_129.solver; range = _29_129.range; curmodule = _29_129.curmodule; gamma = _29_129.gamma; modules = _29_129.modules; expected_typ = _29_129.expected_typ; level = _29_129.level; sigtab = sigtab; is_pattern = _29_129.is_pattern; instantiate_targs = _29_129.instantiate_targs; instantiate_vargs = _29_129.instantiate_vargs; effects = _29_129.effects; generalize = _29_129.generalize; letrecs = _29_129.letrecs; top_level = _29_129.top_level; check_uvars = _29_129.check_uvars; use_eq = _29_129.use_eq; is_iface = _29_129.is_iface; admit = _29_129.admit; default_effects = _29_129.default_effects}))))

let reset_mark = (fun ( env ) -> (let _29_132 = (env.solver.reset_mark "USER MARK")
in (let _29_134 = env
in (let _70_11682 = (Support.List.tl env.sigtab)
in {solver = _29_134.solver; range = _29_134.range; curmodule = _29_134.curmodule; gamma = _29_134.gamma; modules = _29_134.modules; expected_typ = _29_134.expected_typ; level = _29_134.level; sigtab = _70_11682; is_pattern = _29_134.is_pattern; instantiate_targs = _29_134.instantiate_targs; instantiate_vargs = _29_134.instantiate_vargs; effects = _29_134.effects; generalize = _29_134.generalize; letrecs = _29_134.letrecs; top_level = _29_134.top_level; check_uvars = _29_134.check_uvars; use_eq = _29_134.use_eq; is_iface = _29_134.is_iface; admit = _29_134.admit; default_effects = _29_134.default_effects}))))

let pop = (fun ( env ) ( msg ) -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(Support.All.failwith "Too many pops")
end
| _29_144::tl -> begin
(let _29_146 = (env.solver.pop msg)
in (let _29_148 = env
in {solver = _29_148.solver; range = _29_148.range; curmodule = _29_148.curmodule; gamma = _29_148.gamma; modules = _29_148.modules; expected_typ = _29_148.expected_typ; level = _29_148.level; sigtab = tl; is_pattern = _29_148.is_pattern; instantiate_targs = _29_148.instantiate_targs; instantiate_vargs = _29_148.instantiate_vargs; effects = _29_148.effects; generalize = _29_148.generalize; letrecs = _29_148.letrecs; top_level = _29_148.top_level; check_uvars = _29_148.check_uvars; use_eq = _29_148.use_eq; is_iface = _29_148.is_iface; admit = _29_148.admit; default_effects = _29_148.default_effects}))
end))

let initial_env = (fun ( solver ) ( module_lid ) -> (let _70_11692 = (let _70_11691 = (new_sigtab ())
in (_70_11691)::[])
in {solver = solver; range = Microsoft_FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _70_11692; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

let effect_decl_opt = (fun ( env ) ( l ) -> (Support.All.pipe_right env.effects.decls (Support.Microsoft.FStar.Util.find_opt (fun ( d ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals d.Microsoft_FStar_Absyn_Syntax.mname l)))))

let name_not_found = (fun ( l ) -> (Support.Microsoft.FStar.Util.format1 "Name \"%s\" not found" l.Microsoft_FStar_Absyn_Syntax.str))

let variable_not_found = (fun ( v ) -> (let _70_11701 = (Microsoft_FStar_Absyn_Print.strBvd v)
in (Support.Microsoft.FStar.Util.format1 "Variable \"%s\" not found" _70_11701)))

let get_effect_decl = (fun ( env ) ( l ) -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _70_11709 = (let _70_11708 = (let _70_11707 = (name_not_found l)
in (let _70_11706 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (_70_11707, _70_11706)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11708))
in (raise (_70_11709)))
end
| Some (md) -> begin
md
end))

let join = (fun ( env ) ( l1 ) ( l2 ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals l1 l2)) with
| true -> begin
(l1, (fun ( t ) ( wp ) -> wp), (fun ( t ) ( wp ) -> wp))
end
| false -> begin
(match ((Support.All.pipe_right env.effects.joins (Support.Microsoft.FStar.Util.find_opt (fun ( _29_177 ) -> (match (_29_177) with
| (m1, m2, _29_172, _29_174, _29_176) -> begin
((Microsoft_FStar_Absyn_Syntax.lid_equals l1 m1) && (Microsoft_FStar_Absyn_Syntax.lid_equals l2 m2))
end))))) with
| None -> begin
(let _70_11765 = (let _70_11764 = (let _70_11763 = (let _70_11762 = (Microsoft_FStar_Absyn_Print.sli l1)
in (let _70_11761 = (Microsoft_FStar_Absyn_Print.sli l2)
in (Support.Microsoft.FStar.Util.format2 "Effects %s and %s cannot be composed" _70_11762 _70_11761)))
in (_70_11763, env.range))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11764))
in (raise (_70_11765)))
end
| Some ((_29_180, _29_182, m3, j1, j2)) -> begin
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
(let _70_11780 = (Support.Microsoft.FStar.Util.format1 "Impossible: declaration for monad %s not found" m.Microsoft_FStar_Absyn_Syntax.str)
in (Support.All.failwith _70_11780))
end
| Some (md) -> begin
(match (md.Microsoft_FStar_Absyn_Syntax.signature.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _29_213)::(Support.Microsoft.FStar.Util.Inl (wp), _29_208)::(Support.Microsoft.FStar.Util.Inl (wlp), _29_203)::[], {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_effect; Microsoft_FStar_Absyn_Syntax.tk = _29_223; Microsoft_FStar_Absyn_Syntax.pos = _29_221; Microsoft_FStar_Absyn_Syntax.fvs = _29_219; Microsoft_FStar_Absyn_Syntax.uvs = _29_217})) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _29_229 -> begin
(Support.All.failwith "Impossible")
end)
end))

let wp_signature = (fun ( env ) ( m ) -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun ( env ) ( l ) -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun ( _29_236 ) -> (match (_29_236) with
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
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _29_241, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun ( _29_2 ) -> (match (_29_2) with
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _29_251 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _29_255 = env
in {solver = _29_255.solver; range = _29_255.range; curmodule = _29_255.curmodule; gamma = _29_255.gamma; modules = _29_255.modules; expected_typ = _29_255.expected_typ; level = _29_255.level; sigtab = _29_255.sigtab; is_pattern = _29_255.is_pattern; instantiate_targs = _29_255.instantiate_targs; instantiate_vargs = _29_255.instantiate_vargs; effects = _29_255.effects; generalize = _29_255.generalize; letrecs = _29_255.letrecs; top_level = _29_255.top_level; check_uvars = _29_255.check_uvars; use_eq = _29_255.use_eq; is_iface = _29_255.is_iface; admit = _29_255.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _29_259)) -> begin
(let effects = (let _29_262 = env.effects
in {decls = (ne)::env.effects.decls; order = _29_262.order; joins = _29_262.joins})
in (let _29_265 = env
in {solver = _29_265.solver; range = _29_265.range; curmodule = _29_265.curmodule; gamma = _29_265.gamma; modules = _29_265.modules; expected_typ = _29_265.expected_typ; level = _29_265.level; sigtab = _29_265.sigtab; is_pattern = _29_265.is_pattern; instantiate_targs = _29_265.instantiate_targs; instantiate_vargs = _29_265.instantiate_vargs; effects = effects; generalize = _29_265.generalize; letrecs = _29_265.letrecs; top_level = _29_265.top_level; check_uvars = _29_265.check_uvars; use_eq = _29_265.use_eq; is_iface = _29_265.is_iface; admit = _29_265.admit; default_effects = _29_265.default_effects}))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((sub, _29_269)) -> begin
(let compose_edges = (fun ( e1 ) ( e2 ) -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun ( r ) ( wp1 ) -> (let _70_11801 = (e1.mlift r wp1)
in (e2.mlift r _70_11801)))})
in (let mk_lift = (fun ( lift_t ) ( r ) ( wp1 ) -> (let _70_11812 = (let _70_11811 = (let _70_11810 = (Microsoft_FStar_Absyn_Syntax.targ r)
in (let _70_11809 = (let _70_11808 = (Microsoft_FStar_Absyn_Syntax.targ wp1)
in (_70_11808)::[])
in (_70_11810)::_70_11809))
in (lift_t, _70_11811))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _70_11812 None wp1.Microsoft_FStar_Absyn_Syntax.pos)))
in (let edge = {msource = sub.Microsoft_FStar_Absyn_Syntax.source; mtarget = sub.Microsoft_FStar_Absyn_Syntax.target; mlift = (mk_lift sub.Microsoft_FStar_Absyn_Syntax.lift)}
in (let id_edge = (fun ( l ) -> {msource = sub.Microsoft_FStar_Absyn_Syntax.source; mtarget = sub.Microsoft_FStar_Absyn_Syntax.target; mlift = (fun ( t ) ( wp ) -> wp)})
in (let print_mlift = (fun ( l ) -> (let arg = (let _70_11829 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Util.ftv _70_11829 Microsoft_FStar_Absyn_Syntax.mk_Kind_type))
in (let wp = (let _70_11830 = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("WP")::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Util.ftv _70_11830 Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _70_11831 = (l arg wp)
in (Microsoft_FStar_Absyn_Print.typ_to_string _70_11831)))))
in (let order = (edge)::env.effects.order
in (let ms = (Support.All.pipe_right env.effects.decls (Support.List.map (fun ( e ) -> e.Microsoft_FStar_Absyn_Syntax.mname)))
in (let find_edge = (fun ( order ) ( _29_297 ) -> (match (_29_297) with
| (i, j) -> begin
(match ((Microsoft_FStar_Absyn_Syntax.lid_equals i j)) with
| true -> begin
(Support.All.pipe_right (id_edge i) (fun ( _70_11837 ) -> Some (_70_11837)))
end
| false -> begin
(Support.All.pipe_right order (Support.Microsoft.FStar.Util.find_opt (fun ( e ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals e.msource i) && (Microsoft_FStar_Absyn_Syntax.lid_equals e.mtarget j)))))
end)
end))
in (let order = (Support.All.pipe_right ms (Support.List.fold_left (fun ( order ) ( k ) -> (let _70_11845 = (Support.All.pipe_right ms (Support.List.collect (fun ( i ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals i k)) with
| true -> begin
[]
end
| false -> begin
(Support.All.pipe_right ms (Support.List.collect (fun ( j ) -> (match ((Microsoft_FStar_Absyn_Syntax.lid_equals j k)) with
| true -> begin
[]
end
| false -> begin
(match ((let _70_11844 = (find_edge order (i, k))
in (let _70_11843 = (find_edge order (k, j))
in (_70_11844, _70_11843)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _29_309 -> begin
[]
end)
end))))
end))))
in (Support.List.append order _70_11845))) order))
in (let order = (Support.Microsoft.FStar.Util.remove_dups (fun ( e1 ) ( e2 ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals e1.msource e2.msource) && (Microsoft_FStar_Absyn_Syntax.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (Support.All.pipe_right ms (Support.List.collect (fun ( i ) -> (Support.All.pipe_right ms (Support.List.collect (fun ( j ) -> (let join_opt = (Support.All.pipe_right ms (Support.List.fold_left (fun ( bopt ) ( k ) -> (match ((let _70_11853 = (find_edge order (i, k))
in (let _70_11852 = (find_edge order (j, k))
in (_70_11853, _70_11852)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some ((ub, _29_326, _29_328)) -> begin
(match (((let _70_11854 = (find_edge order (k, ub))
in (Support.Microsoft.FStar.Util.is_some _70_11854)) && (not ((let _70_11855 = (find_edge order (ub, k))
in (Support.Microsoft.FStar.Util.is_some _70_11855)))))) with
| true -> begin
Some ((k, ik, jk))
end
| false -> begin
bopt
end)
end)
end
| _29_332 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some ((k, e1, e2)) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _29_341 = env.effects
in {decls = _29_341.decls; order = order; joins = joins})
in (let _29_344 = env
in {solver = _29_344.solver; range = _29_344.range; curmodule = _29_344.curmodule; gamma = _29_344.gamma; modules = _29_344.modules; expected_typ = _29_344.expected_typ; level = _29_344.level; sigtab = _29_344.sigtab; is_pattern = _29_344.is_pattern; instantiate_targs = _29_344.instantiate_targs; instantiate_vargs = _29_344.instantiate_vargs; effects = effects; generalize = _29_344.generalize; letrecs = _29_344.letrecs; top_level = _29_344.top_level; check_uvars = _29_344.check_uvars; use_eq = _29_344.use_eq; is_iface = _29_344.is_iface; admit = _29_344.admit; default_effects = _29_344.default_effects})))))))))))))
end
| _29_347 -> begin
env
end))

let rec add_sigelt = (fun ( env ) ( se ) -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _29_352, _29_354, _29_356)) -> begin
(add_sigelts env ses)
end
| _29_360 -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun ( l ) -> (let _70_11863 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_add _70_11863 l.Microsoft_FStar_Absyn_Syntax.str se))) lids))
end))
and add_sigelts = (fun ( env ) ( ses ) -> (Support.All.pipe_right ses (Support.List.iter (add_sigelt env))))

let empty_lid = (let _70_11867 = (let _70_11866 = (Microsoft_FStar_Absyn_Syntax.id_of_text "")
in (_70_11866)::[])
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _70_11867))

let finish_module = (fun ( env ) ( m ) -> (let sigs = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals m.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid)) with
| true -> begin
(Support.All.pipe_right env.gamma (Support.List.collect (fun ( _29_3 ) -> (match (_29_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _29_371 -> begin
[]
end))))
end
| false -> begin
m.Microsoft_FStar_Absyn_Syntax.exports
end)
in (let _29_373 = (add_sigelts env sigs)
in (let _29_375 = env
in {solver = _29_375.solver; range = _29_375.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _29_375.expected_typ; level = _29_375.level; sigtab = _29_375.sigtab; is_pattern = _29_375.is_pattern; instantiate_targs = _29_375.instantiate_targs; instantiate_vargs = _29_375.instantiate_vargs; effects = _29_375.effects; generalize = _29_375.generalize; letrecs = _29_375.letrecs; top_level = _29_375.top_level; check_uvars = _29_375.check_uvars; use_eq = _29_375.use_eq; is_iface = _29_375.is_iface; admit = _29_375.admit; default_effects = _29_375.default_effects}))))

let set_level = (fun ( env ) ( level ) -> (let _29_379 = env
in {solver = _29_379.solver; range = _29_379.range; curmodule = _29_379.curmodule; gamma = _29_379.gamma; modules = _29_379.modules; expected_typ = _29_379.expected_typ; level = level; sigtab = _29_379.sigtab; is_pattern = _29_379.is_pattern; instantiate_targs = _29_379.instantiate_targs; instantiate_vargs = _29_379.instantiate_vargs; effects = _29_379.effects; generalize = _29_379.generalize; letrecs = _29_379.letrecs; top_level = _29_379.top_level; check_uvars = _29_379.check_uvars; use_eq = _29_379.use_eq; is_iface = _29_379.is_iface; admit = _29_379.admit; default_effects = _29_379.default_effects}))

let is_level = (fun ( env ) ( level ) -> (env.level = level))

let modules = (fun ( env ) -> env.modules)

let current_module = (fun ( env ) -> env.curmodule)

let set_current_module = (fun ( env ) ( lid ) -> (let _29_387 = env
in {solver = _29_387.solver; range = _29_387.range; curmodule = lid; gamma = _29_387.gamma; modules = _29_387.modules; expected_typ = _29_387.expected_typ; level = _29_387.level; sigtab = _29_387.sigtab; is_pattern = _29_387.is_pattern; instantiate_targs = _29_387.instantiate_targs; instantiate_vargs = _29_387.instantiate_vargs; effects = _29_387.effects; generalize = _29_387.generalize; letrecs = _29_387.letrecs; top_level = _29_387.top_level; check_uvars = _29_387.check_uvars; use_eq = _29_387.use_eq; is_iface = _29_387.is_iface; admit = _29_387.admit; default_effects = _29_387.default_effects}))

let set_range = (fun ( e ) ( r ) -> (match ((r = Microsoft_FStar_Absyn_Syntax.dummyRange)) with
| true -> begin
e
end
| false -> begin
(let _29_391 = e
in {solver = _29_391.solver; range = r; curmodule = _29_391.curmodule; gamma = _29_391.gamma; modules = _29_391.modules; expected_typ = _29_391.expected_typ; level = _29_391.level; sigtab = _29_391.sigtab; is_pattern = _29_391.is_pattern; instantiate_targs = _29_391.instantiate_targs; instantiate_vargs = _29_391.instantiate_vargs; effects = _29_391.effects; generalize = _29_391.generalize; letrecs = _29_391.letrecs; top_level = _29_391.top_level; check_uvars = _29_391.check_uvars; use_eq = _29_391.use_eq; is_iface = _29_391.is_iface; admit = _29_391.admit; default_effects = _29_391.default_effects})
end))

let get_range = (fun ( e ) -> e.range)

let find_in_sigtab = (fun ( env ) ( lid ) -> (let _70_11900 = (sigtab env)
in (let _70_11899 = (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)
in (Support.Microsoft.FStar.Util.smap_try_find _70_11900 _70_11899))))

let lookup_bvvdef = (fun ( env ) ( bvvd ) -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun ( _29_4 ) -> (match (_29_4) with
| Binding_var ((id, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _29_404 -> begin
None
end))))

let lookup_bvar = (fun ( env ) ( bv ) -> (match ((lookup_bvvdef env bv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _70_11912 = (let _70_11911 = (let _70_11910 = (variable_not_found bv.Microsoft_FStar_Absyn_Syntax.v)
in (_70_11910, (Microsoft_FStar_Absyn_Util.range_of_bvd bv.Microsoft_FStar_Absyn_Syntax.v)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11911))
in (raise (_70_11912)))
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
| ([], _29_422) -> begin
true
end
| (_29_425, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.Microsoft_FStar_Absyn_Syntax.idText = hd'.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(aux tl tl')
end
| _29_436 -> begin
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
| Binding_sig (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _29_445, _29_447, _29_449))) -> begin
(Support.Microsoft.FStar.Util.find_map ses (fun ( se ) -> (match ((let _70_11925 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.All.pipe_right _70_11925 (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid))))) with
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
| _29_458 -> begin
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
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_29_466, t, _29_469, _29_471, _29_473, _29_475)))) -> begin
t
end
| _29_481 -> begin
(let _70_11933 = (let _70_11932 = (let _70_11931 = (name_not_found lid)
in (let _70_11930 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_70_11931, _70_11930)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11932))
in (raise (_70_11933)))
end))

let lookup_kind_abbrev = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _29_488)))) -> begin
(l, binders, k)
end
| _29_494 -> begin
(let _70_11941 = (let _70_11940 = (let _70_11939 = (name_not_found lid)
in (let _70_11938 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_70_11939, _70_11938)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11940))
in (raise (_70_11941)))
end))

let lookup_projector = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _29_499 ) -> (match (()) with
| () -> begin
(let _70_11952 = (let _70_11951 = (Support.Microsoft.FStar.Util.string_of_int i)
in (let _70_11950 = (Microsoft_FStar_Absyn_Print.sli lid)
in (Support.Microsoft.FStar.Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _70_11951 _70_11950)))
in (Support.All.failwith _70_11952))
end))
in (let t = (lookup_datacon env lid)
in (match ((let _70_11953 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_11953.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _29_503)) -> begin
(match (((i < 0) || (i >= (Support.List.length binders)))) with
| true -> begin
(fail ())
end
| false -> begin
(let b = (Support.List.nth binders i)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_11954 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i)
in (Support.All.pipe_right _70_11954 Support.Prims.fst))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_11955 = (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i)
in (Support.All.pipe_right _70_11955 Support.Prims.fst))
end))
end)
end
| _29_512 -> begin
(fail ())
end))))

let try_lookup_val_decl = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_29_516, t, q, _29_520)))) -> begin
Some ((t, q))
end
| _29_526 -> begin
None
end))

let lookup_val_decl = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_29_530, t, _29_533, _29_535)))) -> begin
t
end
| _29_541 -> begin
(let _70_11967 = (let _70_11966 = (let _70_11965 = (name_not_found lid)
in (let _70_11964 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_70_11965, _70_11964)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11966))
in (raise (_70_11967)))
end))

let lookup_lid = (fun ( env ) ( lid ) -> (let not_found = (fun ( _29_545 ) -> (match (()) with
| () -> begin
(let _70_11977 = (let _70_11976 = (let _70_11975 = (name_not_found lid)
in (let _70_11974 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in (_70_11975, _70_11974)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_11976))
in (raise (_70_11977)))
end))
in (let mapper = (fun ( _29_6 ) -> (match (_29_6) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, {Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_29_592, lbs), _29_596, _29_598, _29_600))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun ( lb ) -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (_29_606) -> begin
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
in (match ((let _70_11981 = (lookup_qname env lid)
in (Support.Microsoft.FStar.Util.bind_opt _70_11981 mapper))) with
| Some (t) -> begin
(let _29_614 = t
in (let _70_11982 = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)
in {Microsoft_FStar_Absyn_Syntax.n = _29_614.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _29_614.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _70_11982; Microsoft_FStar_Absyn_Syntax.fvs = _29_614.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _29_614.Microsoft_FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_29_620, _29_622, quals, _29_625)))) -> begin
(Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _29_7 ) -> (match (_29_7) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _29_633 -> begin
false
end))))
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_29_635, t, _29_638, _29_640, _29_642, _29_644)))) -> begin
true
end
| _29_650 -> begin
false
end))

let is_record = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_29_654, _29_656, _29_658, _29_660, _29_662, tags, _29_665)))) -> begin
(Support.Microsoft.FStar.Util.for_some (fun ( _29_8 ) -> (match (_29_8) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _29_678 -> begin
false
end)) tags)
end
| _29_680 -> begin
false
end))

let lookup_datacons_of_typ = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_29_684, _29_686, _29_688, _29_690, datas, _29_693, _29_695)))) -> begin
(let _70_11999 = (Support.List.map (fun ( l ) -> (let _70_11998 = (lookup_lid env l)
in (l, _70_11998))) datas)
in Some (_70_11999))
end
| _29_702 -> begin
None
end))

let lookup_effect_abbrev = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, c, quals, _29_710)))) -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _29_9 ) -> (match (_29_9) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _29_718 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((binders, c))
end)
end
| _29_720 -> begin
None
end))

let lookup_typ_abbrev = (fun ( env ) ( lid ) -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _29_726, t, quals, _29_730)))) -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _29_10 ) -> (match (_29_10) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _29_738 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
(let t = (Microsoft_FStar_Absyn_Util.close_with_lam tps t)
in (let _70_12010 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_70_12010)))
end)
end
| _29_741 -> begin
None
end))

let lookup_btvdef = (fun ( env ) ( btvd ) -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun ( _29_11 ) -> (match (_29_11) with
| Binding_typ ((id, k)) when (Microsoft_FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _29_750 -> begin
None
end))))

let lookup_btvar = (fun ( env ) ( btv ) -> (match ((lookup_btvdef env btv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(let _70_12022 = (let _70_12021 = (let _70_12020 = (variable_not_found btv.Microsoft_FStar_Absyn_Syntax.v)
in (_70_12020, (Microsoft_FStar_Absyn_Util.range_of_bvd btv.Microsoft_FStar_Absyn_Syntax.v)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_12021))
in (raise (_70_12022)))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid = (fun ( env ) ( ftv ) -> (match ((lookup_qname env ftv)) with
| (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _, _, _, _))))) | (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, _, _, _))))) -> begin
(Microsoft_FStar_Absyn_Util.close_kind tps k)
end
| _29_784 -> begin
(let _70_12030 = (let _70_12029 = (let _70_12028 = (name_not_found ftv)
in (let _70_12027 = (Microsoft_FStar_Absyn_Syntax.range_of_lid ftv)
in (_70_12028, _70_12027)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_12029))
in (raise (_70_12030)))
end))

let is_projector = (fun ( env ) ( l ) -> (match ((lookup_qname env l)) with
| (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, quals, _))))) | (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _))))) -> begin
(Support.Microsoft.FStar.Util.for_some (fun ( _29_12 ) -> (match (_29_12) with
| Microsoft_FStar_Absyn_Syntax.Projector (_29_816) -> begin
true
end
| _29_819 -> begin
false
end)) quals)
end
| _29_821 -> begin
false
end))

let try_lookup_effect_lid = (fun ( env ) ( ftv ) -> (match ((lookup_qname env ftv)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _29_826)))) -> begin
(let _70_12041 = (Microsoft_FStar_Absyn_Util.close_kind ne.Microsoft_FStar_Absyn_Syntax.binders ne.Microsoft_FStar_Absyn_Syntax.signature)
in (Support.All.pipe_right _70_12041 (fun ( _70_12040 ) -> Some (_70_12040))))
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, _29_834, _29_836, _29_838)))) -> begin
(let _70_12043 = (Microsoft_FStar_Absyn_Util.close_kind binders Microsoft_FStar_Absyn_Syntax.mk_Kind_effect)
in (Support.All.pipe_right _70_12043 (fun ( _70_12042 ) -> Some (_70_12042))))
end
| _29_844 -> begin
None
end))

let lookup_effect_lid = (fun ( env ) ( ftv ) -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _70_12051 = (let _70_12050 = (let _70_12049 = (name_not_found ftv)
in (let _70_12048 = (Microsoft_FStar_Absyn_Syntax.range_of_lid ftv)
in (_70_12049, _70_12048)))
in Microsoft_FStar_Absyn_Syntax.Error (_70_12050))
in (raise (_70_12051)))
end
| Some (k) -> begin
k
end))

let lookup_operator = (fun ( env ) ( opname ) -> (let primName = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::((Support.String.strcat "_dummy_" opname.Microsoft_FStar_Absyn_Syntax.idText))::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun ( env ) ( s ) -> (build_lattice (let _29_855 = env
in {solver = _29_855.solver; range = _29_855.range; curmodule = _29_855.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _29_855.modules; expected_typ = _29_855.expected_typ; level = _29_855.level; sigtab = _29_855.sigtab; is_pattern = _29_855.is_pattern; instantiate_targs = _29_855.instantiate_targs; instantiate_vargs = _29_855.instantiate_vargs; effects = _29_855.effects; generalize = _29_855.generalize; letrecs = _29_855.letrecs; top_level = _29_855.top_level; check_uvars = _29_855.check_uvars; use_eq = _29_855.use_eq; is_iface = _29_855.is_iface; admit = _29_855.admit; default_effects = _29_855.default_effects}) s))

let push_local_binding = (fun ( env ) ( b ) -> (let _29_859 = env
in {solver = _29_859.solver; range = _29_859.range; curmodule = _29_859.curmodule; gamma = (b)::env.gamma; modules = _29_859.modules; expected_typ = _29_859.expected_typ; level = _29_859.level; sigtab = _29_859.sigtab; is_pattern = _29_859.is_pattern; instantiate_targs = _29_859.instantiate_targs; instantiate_vargs = _29_859.instantiate_vargs; effects = _29_859.effects; generalize = _29_859.generalize; letrecs = _29_859.letrecs; top_level = _29_859.top_level; check_uvars = _29_859.check_uvars; use_eq = _29_859.use_eq; is_iface = _29_859.is_iface; admit = _29_859.admit; default_effects = _29_859.default_effects}))

let uvars_in_env = (fun ( env ) -> (let no_uvs = (let _70_12068 = (Microsoft_FStar_Absyn_Syntax.new_uv_set ())
in (let _70_12067 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in (let _70_12066 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _70_12068; Microsoft_FStar_Absyn_Syntax.uvars_t = _70_12067; Microsoft_FStar_Absyn_Syntax.uvars_e = _70_12066})))
in (let ext = (fun ( out ) ( uvs ) -> (let _29_866 = out
in (let _70_12075 = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_k uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (let _70_12074 = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_t uvs.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _70_12073 = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_e uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _70_12075; Microsoft_FStar_Absyn_Syntax.uvars_t = _70_12074; Microsoft_FStar_Absyn_Syntax.uvars_e = _70_12073})))))
in (let rec aux = (fun ( out ) ( g ) -> (match (g) with
| [] -> begin
out
end
| (Binding_lid ((_, t))::tl) | (Binding_var ((_, t))::tl) -> begin
(let _70_12081 = (let _70_12080 = (Microsoft_FStar_Absyn_Util.uvars_in_typ t)
in (ext out _70_12080))
in (aux _70_12081 tl))
end
| Binding_typ ((_29_886, k))::tl -> begin
(let _70_12083 = (let _70_12082 = (Microsoft_FStar_Absyn_Util.uvars_in_kind k)
in (ext out _70_12082))
in (aux _70_12083 tl))
end
| Binding_sig (_29_894)::_29_892 -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module = (fun ( env ) ( m ) -> (let _29_899 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _29_901 = env
in {solver = _29_901.solver; range = _29_901.range; curmodule = _29_901.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _29_901.level; sigtab = _29_901.sigtab; is_pattern = _29_901.is_pattern; instantiate_targs = _29_901.instantiate_targs; instantiate_vargs = _29_901.instantiate_vargs; effects = _29_901.effects; generalize = _29_901.generalize; letrecs = _29_901.letrecs; top_level = _29_901.top_level; check_uvars = _29_901.check_uvars; use_eq = _29_901.use_eq; is_iface = _29_901.is_iface; admit = _29_901.admit; default_effects = _29_901.default_effects})))

let set_expected_typ = (fun ( env ) ( t ) -> (let _29_905 = env
in {solver = _29_905.solver; range = _29_905.range; curmodule = _29_905.curmodule; gamma = _29_905.gamma; modules = _29_905.modules; expected_typ = Some (t); level = _29_905.level; sigtab = _29_905.sigtab; is_pattern = _29_905.is_pattern; instantiate_targs = _29_905.instantiate_targs; instantiate_vargs = _29_905.instantiate_vargs; effects = _29_905.effects; generalize = _29_905.generalize; letrecs = _29_905.letrecs; top_level = _29_905.top_level; check_uvars = _29_905.check_uvars; use_eq = false; is_iface = _29_905.is_iface; admit = _29_905.admit; default_effects = _29_905.default_effects}))

let expected_typ = (fun ( env ) -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun ( env ) -> (let _70_12096 = (expected_typ env)
in ((let _29_912 = env
in {solver = _29_912.solver; range = _29_912.range; curmodule = _29_912.curmodule; gamma = _29_912.gamma; modules = _29_912.modules; expected_typ = None; level = _29_912.level; sigtab = _29_912.sigtab; is_pattern = _29_912.is_pattern; instantiate_targs = _29_912.instantiate_targs; instantiate_vargs = _29_912.instantiate_vargs; effects = _29_912.effects; generalize = _29_912.generalize; letrecs = _29_912.letrecs; top_level = _29_912.top_level; check_uvars = _29_912.check_uvars; use_eq = false; is_iface = _29_912.is_iface; admit = _29_912.admit; default_effects = _29_912.default_effects}), _70_12096)))

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
(let _70_12114 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_70_12114)::out)
end
| Binding_typ ((a, k)) -> begin
(let _70_12115 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_12115)::out)
end
| _29_936 -> begin
out
end)) [] env.gamma))

let t_binders = (fun ( env ) -> (Support.List.fold_left (fun ( out ) ( b ) -> (match (b) with
| Binding_var (_29_941) -> begin
out
end
| Binding_typ ((a, k)) -> begin
(let _70_12120 = (Support.All.pipe_left Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_70_12120)::out)
end
| _29_948 -> begin
out
end)) [] env.gamma))

let idents = (fun ( env ) -> (let _70_12124 = (let _70_12123 = (binders env)
in (Support.All.pipe_right _70_12123 (Support.List.map Support.Prims.fst)))
in (Microsoft_FStar_Absyn_Syntax.freevars_of_list _70_12124)))

let lidents = (fun ( env ) -> (let keys = (Support.List.fold_left (fun ( keys ) ( _29_13 ) -> (match (_29_13) with
| Binding_sig (s) -> begin
(let _70_12129 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in (Support.List.append _70_12129 keys))
end
| _29_956 -> begin
keys
end)) [] env.gamma)
in (let _70_12134 = (sigtab env)
in (Support.Microsoft.FStar.Util.smap_fold _70_12134 (fun ( _29_958 ) ( v ) ( keys ) -> (let _70_12133 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt v)
in (Support.List.append _70_12133 keys))) keys))))




