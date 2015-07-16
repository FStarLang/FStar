
type binding =
| Binding_var of (Microsoft_FStar_Absyn_Syntax.bvvdef * Microsoft_FStar_Absyn_Syntax.typ)
| Binding_typ of (Microsoft_FStar_Absyn_Syntax.btvdef * Microsoft_FStar_Absyn_Syntax.knd)
| Binding_lid of (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.typ)
| Binding_sig of Microsoft_FStar_Absyn_Syntax.sigelt

type sigtable =
Microsoft_FStar_Absyn_Syntax.sigelt Support.Microsoft.FStar.Util.smap

let default_table_size = 200

let strlid_of_sigelt = (fun se -> (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
Some ((Microsoft_FStar_Absyn_Syntax.text_of_lid l))
end))

let signature_to_sigtables = (fun s -> (let ht = (Support.Microsoft.FStar.Util.smap_create default_table_size)
in (let _22_31 = (Support.List.iter (fun se -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun l -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (signature_to_sigtables (Support.List.collect (fun _22_37 -> (match (_22_37) with
| (_, m) -> begin
m.Microsoft_FStar_Absyn_Syntax.declarations
end)) mods)))

type level =
| Expr
| Type
| Kind

type mlift =
Microsoft_FStar_Absyn_Syntax.typ  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  Microsoft_FStar_Absyn_Syntax.typ

type edge =
{msource : Microsoft_FStar_Absyn_Syntax.lident; mtarget : Microsoft_FStar_Absyn_Syntax.lident; mlift : mlift}

type effects =
{decls : Microsoft_FStar_Absyn_Syntax.eff_decl list; order : edge list; joins : (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.lident * mlift * mlift) list}

type env =
{solver : solver_t; range : Support.Microsoft.FStar.Range.range; curmodule : Microsoft_FStar_Absyn_Syntax.lident; gamma : binding list; modules : Microsoft_FStar_Absyn_Syntax.modul list; expected_typ : Microsoft_FStar_Absyn_Syntax.typ option; level : level; sigtab : sigtable list; is_pattern : bool; instantiate_targs : bool; instantiate_vargs : bool; effects : effects; generalize : bool; letrecs : (Microsoft_FStar_Absyn_Syntax.lbname * Microsoft_FStar_Absyn_Syntax.typ) list; top_level : bool; check_uvars : bool; use_eq : bool; is_iface : bool; admit : bool; default_effects : (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.lident) list} and solver_t =
{init : env  ->  unit; push : string  ->  unit; pop : string  ->  unit; mark : string  ->  unit; reset_mark : string  ->  unit; commit_mark : string  ->  unit; encode_modul : env  ->  Microsoft_FStar_Absyn_Syntax.modul  ->  unit; encode_sig : env  ->  Microsoft_FStar_Absyn_Syntax.sigelt  ->  unit; solve : env  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  unit; is_trivial : env  ->  Microsoft_FStar_Absyn_Syntax.typ  ->  bool; finish : unit  ->  unit; refresh : unit  ->  unit}

let bound_vars = (fun env -> ((Support.List.collect (fun _22_1 -> (match (_22_1) with
| Binding_typ ((a, k)) -> begin
((Support.Microsoft.FStar.Util.Inl (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)))::[]
end
| Binding_var ((x, t)) -> begin
((Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)))::[]
end
| Binding_lid (_) -> begin
[]
end
| Binding_sig (_) -> begin
[]
end))) env.gamma))

let has_interface = (fun env l -> ((Support.Microsoft.FStar.Util.for_some (fun m -> (m.Microsoft_FStar_Absyn_Syntax.is_interface && (Microsoft_FStar_Absyn_Syntax.lid_equals m.Microsoft_FStar_Absyn_Syntax.name l)))) env.modules))

let debug = (fun env l -> (((Support.Microsoft.FStar.Util.for_some (fun x -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))) (! (Microsoft_FStar_Options.debug))) && (Microsoft_FStar_Options.debug_level_geq l)))

let show = (fun env -> ((Support.Microsoft.FStar.Util.for_some (fun x -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))) (! (Microsoft_FStar_Options.show_signatures))))

let new_sigtab = (fun _22_104 -> (match (_22_104) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (Support.List.hd env.sigtab))

let push = (fun env msg -> (let _22_108 = (env.solver.push msg)
in (let _22_110 = env
in {solver = _22_110.solver; range = _22_110.range; curmodule = _22_110.curmodule; gamma = _22_110.gamma; modules = _22_110.modules; expected_typ = _22_110.expected_typ; level = _22_110.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _22_110.is_pattern; instantiate_targs = _22_110.instantiate_targs; instantiate_vargs = _22_110.instantiate_vargs; effects = _22_110.effects; generalize = _22_110.generalize; letrecs = _22_110.letrecs; top_level = _22_110.top_level; check_uvars = _22_110.check_uvars; use_eq = _22_110.use_eq; is_iface = _22_110.is_iface; admit = _22_110.admit; default_effects = _22_110.default_effects})))

let mark = (fun env -> (let _22_113 = (env.solver.mark "USER MARK")
in (let _22_115 = env
in {solver = _22_115.solver; range = _22_115.range; curmodule = _22_115.curmodule; gamma = _22_115.gamma; modules = _22_115.modules; expected_typ = _22_115.expected_typ; level = _22_115.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _22_115.is_pattern; instantiate_targs = _22_115.instantiate_targs; instantiate_vargs = _22_115.instantiate_vargs; effects = _22_115.effects; generalize = _22_115.generalize; letrecs = _22_115.letrecs; top_level = _22_115.top_level; check_uvars = _22_115.check_uvars; use_eq = _22_115.use_eq; is_iface = _22_115.is_iface; admit = _22_115.admit; default_effects = _22_115.default_effects})))

let commit_mark = (fun env -> (let _22_118 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_::tl -> begin
(hd)::tl
end
| _ -> begin
(failwith "Impossible")
end)
in (let _22_129 = env
in {solver = _22_129.solver; range = _22_129.range; curmodule = _22_129.curmodule; gamma = _22_129.gamma; modules = _22_129.modules; expected_typ = _22_129.expected_typ; level = _22_129.level; sigtab = sigtab; is_pattern = _22_129.is_pattern; instantiate_targs = _22_129.instantiate_targs; instantiate_vargs = _22_129.instantiate_vargs; effects = _22_129.effects; generalize = _22_129.generalize; letrecs = _22_129.letrecs; top_level = _22_129.top_level; check_uvars = _22_129.check_uvars; use_eq = _22_129.use_eq; is_iface = _22_129.is_iface; admit = _22_129.admit; default_effects = _22_129.default_effects}))))

let reset_mark = (fun env -> (let _22_132 = (env.solver.reset_mark "USER MARK")
in (let _22_134 = env
in {solver = _22_134.solver; range = _22_134.range; curmodule = _22_134.curmodule; gamma = _22_134.gamma; modules = _22_134.modules; expected_typ = _22_134.expected_typ; level = _22_134.level; sigtab = (Support.List.tl env.sigtab); is_pattern = _22_134.is_pattern; instantiate_targs = _22_134.instantiate_targs; instantiate_vargs = _22_134.instantiate_vargs; effects = _22_134.effects; generalize = _22_134.generalize; letrecs = _22_134.letrecs; top_level = _22_134.top_level; check_uvars = _22_134.check_uvars; use_eq = _22_134.use_eq; is_iface = _22_134.is_iface; admit = _22_134.admit; default_effects = _22_134.default_effects})))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(failwith "Too many pops")
end
| _::tl -> begin
(let _22_146 = (env.solver.pop msg)
in (let _22_148 = env
in {solver = _22_148.solver; range = _22_148.range; curmodule = _22_148.curmodule; gamma = _22_148.gamma; modules = _22_148.modules; expected_typ = _22_148.expected_typ; level = _22_148.level; sigtab = tl; is_pattern = _22_148.is_pattern; instantiate_targs = _22_148.instantiate_targs; instantiate_vargs = _22_148.instantiate_vargs; effects = _22_148.effects; generalize = _22_148.generalize; letrecs = _22_148.letrecs; top_level = _22_148.top_level; check_uvars = _22_148.check_uvars; use_eq = _22_148.use_eq; is_iface = _22_148.is_iface; admit = _22_148.admit; default_effects = _22_148.default_effects}))
end))

let initial_env = (fun solver module_lid -> {solver = solver; range = Microsoft_FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = ((new_sigtab ()))::[]; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []})

let effect_decl_opt = (fun env l -> ((Support.Microsoft.FStar.Util.find_opt (fun d -> (Microsoft_FStar_Absyn_Syntax.lid_equals d.Microsoft_FStar_Absyn_Syntax.mname l))) env.effects.decls))

let name_not_found = (fun l -> (Support.Microsoft.FStar.Util.format1 "Name \"%s\" not found" l.Microsoft_FStar_Absyn_Syntax.str))

let variable_not_found = (fun v -> (Support.Microsoft.FStar.Util.format1 "Variable \"%s\" not found" (Microsoft_FStar_Absyn_Print.strBvd v)))

let get_effect_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found l), (Microsoft_FStar_Absyn_Syntax.range_of_lid l)))))
end
| Some (md) -> begin
md
end))

let join = (fun env l1 l2 -> if (Microsoft_FStar_Absyn_Syntax.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match (((Support.Microsoft.FStar.Util.find_opt (fun _22_177 -> (match (_22_177) with
| (m1, m2, _, _, _) -> begin
((Microsoft_FStar_Absyn_Syntax.lid_equals l1 m1) && (Microsoft_FStar_Absyn_Syntax.lid_equals l2 m2))
end))) env.effects.joins)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.Microsoft.FStar.Util.format2 "Effects %s and %s cannot be composed" (Microsoft_FStar_Absyn_Print.sli l1) (Microsoft_FStar_Absyn_Print.sli l2)), env.range))))
end
| Some ((_, _, m3, j1, j2)) -> begin
(m3, j1, j2)
end)
end)

let monad_leq = (fun env l1 l2 -> if (Microsoft_FStar_Absyn_Syntax.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
((Support.Microsoft.FStar.Util.find_opt (fun e -> ((Microsoft_FStar_Absyn_Syntax.lid_equals l1 e.msource) && (Microsoft_FStar_Absyn_Syntax.lid_equals l2 e.mtarget)))) env.effects.order)
end)

let wp_sig_aux = (fun decls m -> (match (((Support.Microsoft.FStar.Util.find_opt (fun d -> (Microsoft_FStar_Absyn_Syntax.lid_equals d.Microsoft_FStar_Absyn_Syntax.mname m))) decls)) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Impossible: declaration for monad %s not found" m.Microsoft_FStar_Absyn_Syntax.str))
end
| Some (md) -> begin
(match (md.Microsoft_FStar_Absyn_Syntax.signature.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _)::(Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (wlp), _)::[], {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_effect; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _ -> begin
(failwith "Impossible")
end)
end))

let wp_signature = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun env l -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun _22_236 -> (match (_22_236) with
| (l', m) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun _22_2 -> (match (_22_2) with
| Microsoft_FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _ -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _22_255 = env
in {solver = _22_255.solver; range = _22_255.range; curmodule = _22_255.curmodule; gamma = _22_255.gamma; modules = _22_255.modules; expected_typ = _22_255.expected_typ; level = _22_255.level; sigtab = _22_255.sigtab; is_pattern = _22_255.is_pattern; instantiate_targs = _22_255.instantiate_targs; instantiate_vargs = _22_255.instantiate_vargs; effects = _22_255.effects; generalize = _22_255.generalize; letrecs = _22_255.letrecs; top_level = _22_255.top_level; check_uvars = _22_255.check_uvars; use_eq = _22_255.use_eq; is_iface = _22_255.is_iface; admit = _22_255.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
(let effects = (let _22_262 = env.effects
in {decls = (ne)::env.effects.decls; order = _22_262.order; joins = _22_262.joins})
in (let _22_265 = env
in {solver = _22_265.solver; range = _22_265.range; curmodule = _22_265.curmodule; gamma = _22_265.gamma; modules = _22_265.modules; expected_typ = _22_265.expected_typ; level = _22_265.level; sigtab = _22_265.sigtab; is_pattern = _22_265.is_pattern; instantiate_targs = _22_265.instantiate_targs; instantiate_vargs = _22_265.instantiate_vargs; effects = effects; generalize = _22_265.generalize; letrecs = _22_265.letrecs; top_level = _22_265.top_level; check_uvars = _22_265.check_uvars; use_eq = _22_265.use_eq; is_iface = _22_265.is_iface; admit = _22_265.admit; default_effects = _22_265.default_effects}))
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((sub, _)) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (e2.mlift r (e1.mlift r wp1)))})
in (let mk_lift = (fun lift_t r wp1 -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (lift_t, ((Microsoft_FStar_Absyn_Syntax.targ r))::((Microsoft_FStar_Absyn_Syntax.targ wp1))::[]) None wp1.Microsoft_FStar_Absyn_Syntax.pos))
in (let edge = {msource = sub.Microsoft_FStar_Absyn_Syntax.source; mtarget = sub.Microsoft_FStar_Absyn_Syntax.target; mlift = (mk_lift sub.Microsoft_FStar_Absyn_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.Microsoft_FStar_Absyn_Syntax.source; mtarget = sub.Microsoft_FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) Microsoft_FStar_Absyn_Syntax.dummyRange) Microsoft_FStar_Absyn_Syntax.mk_Kind_type)
in (let wp = (Microsoft_FStar_Absyn_Util.ftv (Microsoft_FStar_Absyn_Syntax.lid_of_path (("WP")::[]) Microsoft_FStar_Absyn_Syntax.dummyRange) Microsoft_FStar_Absyn_Syntax.mk_Kind_unknown)
in (Microsoft_FStar_Absyn_Print.typ_to_string (l arg wp)))))
in (let order = (edge)::env.effects.order
in (let ms = ((Support.List.map (fun e -> e.Microsoft_FStar_Absyn_Syntax.mname)) env.effects.decls)
in (let find_edge = (fun order _22_297 -> (match (_22_297) with
| (i, j) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals i j) then begin
((fun __dataconst_1 -> Some (__dataconst_1)) (id_edge i))
end else begin
((Support.Microsoft.FStar.Util.find_opt (fun e -> ((Microsoft_FStar_Absyn_Syntax.lid_equals e.msource i) && (Microsoft_FStar_Absyn_Syntax.lid_equals e.mtarget j)))) order)
end
end))
in (let order = ((Support.List.fold_left (fun order k -> (Support.List.append order ((Support.List.collect (fun i -> if (Microsoft_FStar_Absyn_Syntax.lid_equals i k) then begin
[]
end else begin
((Support.List.collect (fun j -> if (Microsoft_FStar_Absyn_Syntax.lid_equals j k) then begin
[]
end else begin
(match (((find_edge order (i, k)), (find_edge order (k, j)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _ -> begin
[]
end)
end)) ms)
end)) ms))) order) ms)
in (let order = (Support.Microsoft.FStar.Util.remove_dups (fun e1 e2 -> ((Microsoft_FStar_Absyn_Syntax.lid_equals e1.msource e2.msource) && (Microsoft_FStar_Absyn_Syntax.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = ((Support.List.collect (fun i -> ((Support.List.collect (fun j -> (let join_opt = ((Support.List.fold_left (fun bopt k -> (match (((find_edge order (i, k)), (find_edge order (j, k)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some ((ub, _, _)) -> begin
if ((Support.Microsoft.FStar.Util.is_some (find_edge order (k, ub))) && (not ((Support.Microsoft.FStar.Util.is_some (find_edge order (ub, k)))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _ -> begin
bopt
end)) None) ms)
in (match (join_opt) with
| None -> begin
[]
end
| Some ((k, e1, e2)) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end)))) ms))) ms)
in (let effects = (let _22_341 = env.effects
in {decls = _22_341.decls; order = order; joins = joins})
in (let _22_344 = env
in {solver = _22_344.solver; range = _22_344.range; curmodule = _22_344.curmodule; gamma = _22_344.gamma; modules = _22_344.modules; expected_typ = _22_344.expected_typ; level = _22_344.level; sigtab = _22_344.sigtab; is_pattern = _22_344.is_pattern; instantiate_targs = _22_344.instantiate_targs; instantiate_vargs = _22_344.instantiate_vargs; effects = effects; generalize = _22_344.generalize; letrecs = _22_344.letrecs; top_level = _22_344.top_level; check_uvars = _22_344.check_uvars; use_eq = _22_344.use_eq; is_iface = _22_344.is_iface; admit = _22_344.admit; default_effects = _22_344.default_effects})))))))))))))
end
| _ -> begin
env
end))

let rec add_sigelt = (fun env se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
(add_sigelts env ses)
end
| _ -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun l -> (Support.Microsoft.FStar.Util.smap_add (sigtab env) l.Microsoft_FStar_Absyn_Syntax.str se)) lids))
end))
and add_sigelts = (fun env ses -> ((Support.List.iter (add_sigelt env)) ses))

let empty_lid = (Microsoft_FStar_Absyn_Syntax.lid_of_ids (((Microsoft_FStar_Absyn_Syntax.id_of_text ""))::[]))

let finish_module = (fun env m -> (let sigs = if (Microsoft_FStar_Absyn_Syntax.lid_equals m.Microsoft_FStar_Absyn_Syntax.name Microsoft_FStar_Absyn_Const.prims_lid) then begin
((Support.List.collect (fun _22_3 -> (match (_22_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _ -> begin
[]
end))) env.gamma)
end else begin
m.Microsoft_FStar_Absyn_Syntax.exports
end
in (let _22_373 = (add_sigelts env sigs)
in (let _22_375 = env
in {solver = _22_375.solver; range = _22_375.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _22_375.expected_typ; level = _22_375.level; sigtab = _22_375.sigtab; is_pattern = _22_375.is_pattern; instantiate_targs = _22_375.instantiate_targs; instantiate_vargs = _22_375.instantiate_vargs; effects = _22_375.effects; generalize = _22_375.generalize; letrecs = _22_375.letrecs; top_level = _22_375.top_level; check_uvars = _22_375.check_uvars; use_eq = _22_375.use_eq; is_iface = _22_375.is_iface; admit = _22_375.admit; default_effects = _22_375.default_effects}))))

let set_level = (fun env level -> (let _22_379 = env
in {solver = _22_379.solver; range = _22_379.range; curmodule = _22_379.curmodule; gamma = _22_379.gamma; modules = _22_379.modules; expected_typ = _22_379.expected_typ; level = level; sigtab = _22_379.sigtab; is_pattern = _22_379.is_pattern; instantiate_targs = _22_379.instantiate_targs; instantiate_vargs = _22_379.instantiate_vargs; effects = _22_379.effects; generalize = _22_379.generalize; letrecs = _22_379.letrecs; top_level = _22_379.top_level; check_uvars = _22_379.check_uvars; use_eq = _22_379.use_eq; is_iface = _22_379.is_iface; admit = _22_379.admit; default_effects = _22_379.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _22_387 = env
in {solver = _22_387.solver; range = _22_387.range; curmodule = lid; gamma = _22_387.gamma; modules = _22_387.modules; expected_typ = _22_387.expected_typ; level = _22_387.level; sigtab = _22_387.sigtab; is_pattern = _22_387.is_pattern; instantiate_targs = _22_387.instantiate_targs; instantiate_vargs = _22_387.instantiate_vargs; effects = _22_387.effects; generalize = _22_387.generalize; letrecs = _22_387.letrecs; top_level = _22_387.top_level; check_uvars = _22_387.check_uvars; use_eq = _22_387.use_eq; is_iface = _22_387.is_iface; admit = _22_387.admit; default_effects = _22_387.default_effects}))

let set_range = (fun e r -> if (r = Microsoft_FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _22_391 = e
in {solver = _22_391.solver; range = r; curmodule = _22_391.curmodule; gamma = _22_391.gamma; modules = _22_391.modules; expected_typ = _22_391.expected_typ; level = _22_391.level; sigtab = _22_391.sigtab; is_pattern = _22_391.is_pattern; instantiate_targs = _22_391.instantiate_targs; instantiate_vargs = _22_391.instantiate_vargs; effects = _22_391.effects; generalize = _22_391.generalize; letrecs = _22_391.letrecs; top_level = _22_391.top_level; check_uvars = _22_391.check_uvars; use_eq = _22_391.use_eq; is_iface = _22_391.is_iface; admit = _22_391.admit; default_effects = _22_391.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (Support.Microsoft.FStar.Util.smap_try_find (sigtab env) (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)))

let lookup_bvvdef = (fun env bvvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _22_4 -> (match (_22_4) with
| Binding_var ((id, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _ -> begin
None
end))))

let lookup_bvar = (fun env bv -> (match ((lookup_bvvdef env bv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((variable_not_found bv.Microsoft_FStar_Absyn_Syntax.v), (Microsoft_FStar_Absyn_Util.range_of_bvd bv.Microsoft_FStar_Absyn_Syntax.v)))))
end
| Some (t) -> begin
t
end))

let lookup_qname = (fun env lid -> (let in_cur_mod = (fun l -> (let cur = (current_module env)
in if (l.Microsoft_FStar_Absyn_Syntax.nsstr = cur.Microsoft_FStar_Absyn_Syntax.str) then begin
true
end else begin
if (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.nsstr cur.Microsoft_FStar_Absyn_Syntax.str) then begin
(let lns = (Support.List.append l.Microsoft_FStar_Absyn_Syntax.ns ((l.Microsoft_FStar_Absyn_Syntax.ident)::[]))
in (let cur = (Support.List.append cur.Microsoft_FStar_Absyn_Syntax.ns ((cur.Microsoft_FStar_Absyn_Syntax.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _) -> begin
true
end
| (_, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.Microsoft_FStar_Absyn_Syntax.idText = hd'.Microsoft_FStar_Absyn_Syntax.idText) -> begin
(aux tl tl')
end
| _ -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))
in (let cur_mod = (in_cur_mod lid)
in (let found = if cur_mod then begin
(Support.Microsoft.FStar.Util.find_map env.gamma (fun _22_5 -> (match (_22_5) with
| Binding_lid ((l, t)) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals lid l) then begin
Some (Support.Microsoft.FStar.Util.Inl (t))
end else begin
None
end
end
| Binding_sig (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _))) -> begin
(Support.Microsoft.FStar.Util.find_map ses (fun se -> if ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid)) (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)) then begin
Some (Support.Microsoft.FStar.Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt s)
in if ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid)) lids) then begin
Some (Support.Microsoft.FStar.Util.Inr (s))
end else begin
None
end)
end
| _ -> begin
None
end)))
end else begin
None
end
in if (Support.Microsoft.FStar.Util.is_some found) then begin
found
end else begin
if ((not (cur_mod)) || (has_interface env env.curmodule)) then begin
(match ((find_in_sigtab env lid)) with
| Some (se) -> begin
Some (Support.Microsoft.FStar.Util.Inr (se))
end
| None -> begin
None
end)
end else begin
None
end
end))))

let lookup_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) -> begin
t
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))

let lookup_kind_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((l, binders, k, _)))) -> begin
(l, binders, k)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))

let lookup_projector = (fun env lid i -> (let fail = (fun _22_499 -> (match (_22_499) with
| () -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" (Support.Microsoft.FStar.Util.string_of_int i) (Microsoft_FStar_Absyn_Print.sli lid)))
end))
in (let t = (lookup_datacon env lid)
in (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _)) -> begin
if ((i < 0) || (i >= (Support.List.length binders))) then begin
(fail ())
end else begin
(let b = (Support.List.nth binders i)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
((Support.Prims.fst) (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid a i))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
((Support.Prims.fst) (Microsoft_FStar_Absyn_Util.mk_field_projector_name lid x i))
end))
end
end
| _ -> begin
(fail ())
end))))

let try_lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, q, _)))) -> begin
Some ((t, q))
end
| _ -> begin
None
end))

let lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) -> begin
t
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))

let lookup_lid = (fun env lid -> (let not_found = (fun _22_545 -> (match (_22_545) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))
in (let mapper = (fun _22_6 -> (match (_22_6) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, {Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, lbs), _, _, _))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun lb -> (match (lb.Microsoft_FStar_Absyn_Syntax.lbname) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(failwith "impossible")
end
| Support.Microsoft.FStar.Util.Inr (lid') -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals lid lid') then begin
Some (lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
end else begin
None
end
end)))
end
| t -> begin
None
end))
in (match ((Support.Microsoft.FStar.Util.bind_opt (lookup_qname env lid) mapper)) with
| Some (t) -> begin
(let _22_614 = t
in {Microsoft_FStar_Absyn_Syntax.n = _22_614.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _22_614.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid); Microsoft_FStar_Absyn_Syntax.fvs = _22_614.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _22_614.Microsoft_FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)))) -> begin
((Support.Microsoft.FStar.Util.for_some (fun _22_7 -> (match (_22_7) with
| Microsoft_FStar_Absyn_Syntax.Assumption -> begin
true
end
| _ -> begin
false
end))) quals)
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) -> begin
true
end
| _ -> begin
false
end))

let is_record = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, tags, _)))) -> begin
(Support.Microsoft.FStar.Util.for_some (fun _22_8 -> (match (_22_8) with
| (Microsoft_FStar_Absyn_Syntax.RecordType (_)) | (Microsoft_FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _ -> begin
false
end)) tags)
end
| _ -> begin
false
end))

let lookup_datacons_of_typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, datas, _, _)))) -> begin
Some ((Support.List.map (fun l -> (l, (lookup_lid env l))) datas))
end
| _ -> begin
None
end))

let lookup_effect_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, c, quals, _)))) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _22_9 -> (match (_22_9) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))) quals) then begin
None
end else begin
Some ((binders, c))
end
end
| _ -> begin
None
end))

let lookup_typ_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _, t, quals, _)))) -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _22_10 -> (match (_22_10) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))) quals) then begin
None
end else begin
(let t = (Microsoft_FStar_Absyn_Util.close_with_lam tps t)
in Some ((Microsoft_FStar_Absyn_Syntax.mk_Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, lid))))))
end
end
| _ -> begin
None
end))

let lookup_btvdef = (fun env btvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _22_11 -> (match (_22_11) with
| Binding_typ ((id, k)) when (Microsoft_FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _ -> begin
None
end))))

let lookup_btvar = (fun env btv -> (match ((lookup_btvdef env btv.Microsoft_FStar_Absyn_Syntax.v)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((variable_not_found btv.Microsoft_FStar_Absyn_Syntax.v), (Microsoft_FStar_Absyn_Util.range_of_bvd btv.Microsoft_FStar_Absyn_Syntax.v)))))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _, _, _, _))))) | (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, _, _, _))))) -> begin
(Microsoft_FStar_Absyn_Util.close_kind tps k)
end
| _ -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found ftv), (Microsoft_FStar_Absyn_Syntax.range_of_lid ftv)))))
end))

let is_projector = (fun env l -> (match ((lookup_qname env l)) with
| (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, quals, _))))) | (Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _))))) -> begin
(Support.Microsoft.FStar.Util.for_some (fun _22_12 -> (match (_22_12) with
| Microsoft_FStar_Absyn_Syntax.Projector (_) -> begin
true
end
| _ -> begin
false
end)) quals)
end
| _ -> begin
false
end))

let try_lookup_effect_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)))) -> begin
((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.close_kind ne.Microsoft_FStar_Absyn_Syntax.binders ne.Microsoft_FStar_Absyn_Syntax.signature))
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, _, _, _)))) -> begin
((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.close_kind binders Microsoft_FStar_Absyn_Syntax.mk_Kind_effect))
end
| _ -> begin
None
end))

let lookup_effect_lid = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found ftv), (Microsoft_FStar_Absyn_Syntax.range_of_lid ftv)))))
end
| Some (k) -> begin
k
end))

let lookup_operator = (fun env opname -> (let primName = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::((Support.String.strcat "_dummy_" opname.Microsoft_FStar_Absyn_Syntax.idText))::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun env s -> (build_lattice (let _22_855 = env
in {solver = _22_855.solver; range = _22_855.range; curmodule = _22_855.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _22_855.modules; expected_typ = _22_855.expected_typ; level = _22_855.level; sigtab = _22_855.sigtab; is_pattern = _22_855.is_pattern; instantiate_targs = _22_855.instantiate_targs; instantiate_vargs = _22_855.instantiate_vargs; effects = _22_855.effects; generalize = _22_855.generalize; letrecs = _22_855.letrecs; top_level = _22_855.top_level; check_uvars = _22_855.check_uvars; use_eq = _22_855.use_eq; is_iface = _22_855.is_iface; admit = _22_855.admit; default_effects = _22_855.default_effects}) s))

let push_local_binding = (fun env b -> (let _22_859 = env
in {solver = _22_859.solver; range = _22_859.range; curmodule = _22_859.curmodule; gamma = (b)::env.gamma; modules = _22_859.modules; expected_typ = _22_859.expected_typ; level = _22_859.level; sigtab = _22_859.sigtab; is_pattern = _22_859.is_pattern; instantiate_targs = _22_859.instantiate_targs; instantiate_vargs = _22_859.instantiate_vargs; effects = _22_859.effects; generalize = _22_859.generalize; letrecs = _22_859.letrecs; top_level = _22_859.top_level; check_uvars = _22_859.check_uvars; use_eq = _22_859.use_eq; is_iface = _22_859.is_iface; admit = _22_859.admit; default_effects = _22_859.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = {Microsoft_FStar_Absyn_Syntax.uvars_k = (Microsoft_FStar_Absyn_Syntax.new_uv_set ()); Microsoft_FStar_Absyn_Syntax.uvars_t = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ()); Microsoft_FStar_Absyn_Syntax.uvars_e = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())}
in (let ext = (fun out uvs -> (let _22_866 = out
in {Microsoft_FStar_Absyn_Syntax.uvars_k = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_k uvs.Microsoft_FStar_Absyn_Syntax.uvars_k); Microsoft_FStar_Absyn_Syntax.uvars_t = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_t uvs.Microsoft_FStar_Absyn_Syntax.uvars_t); Microsoft_FStar_Absyn_Syntax.uvars_e = (Support.Microsoft.FStar.Util.set_union out.Microsoft_FStar_Absyn_Syntax.uvars_e uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)}))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid ((_, t))::tl) | (Binding_var ((_, t))::tl) -> begin
(aux (ext out (Microsoft_FStar_Absyn_Util.uvars_in_typ t)) tl)
end
| Binding_typ ((_, k))::tl -> begin
(aux (ext out (Microsoft_FStar_Absyn_Util.uvars_in_kind k)) tl)
end
| Binding_sig (_)::_ -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module = (fun env m -> (let _22_899 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _22_901 = env
in {solver = _22_901.solver; range = _22_901.range; curmodule = _22_901.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _22_901.level; sigtab = _22_901.sigtab; is_pattern = _22_901.is_pattern; instantiate_targs = _22_901.instantiate_targs; instantiate_vargs = _22_901.instantiate_vargs; effects = _22_901.effects; generalize = _22_901.generalize; letrecs = _22_901.letrecs; top_level = _22_901.top_level; check_uvars = _22_901.check_uvars; use_eq = _22_901.use_eq; is_iface = _22_901.is_iface; admit = _22_901.admit; default_effects = _22_901.default_effects})))

let set_expected_typ = (fun env t -> (let _22_905 = env
in {solver = _22_905.solver; range = _22_905.range; curmodule = _22_905.curmodule; gamma = _22_905.gamma; modules = _22_905.modules; expected_typ = Some (t); level = _22_905.level; sigtab = _22_905.sigtab; is_pattern = _22_905.is_pattern; instantiate_targs = _22_905.instantiate_targs; instantiate_vargs = _22_905.instantiate_vargs; effects = _22_905.effects; generalize = _22_905.generalize; letrecs = _22_905.letrecs; top_level = _22_905.top_level; check_uvars = _22_905.check_uvars; use_eq = false; is_iface = _22_905.is_iface; admit = _22_905.admit; default_effects = _22_905.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> ((let _22_912 = env
in {solver = _22_912.solver; range = _22_912.range; curmodule = _22_912.curmodule; gamma = _22_912.gamma; modules = _22_912.modules; expected_typ = None; level = _22_912.level; sigtab = _22_912.sigtab; is_pattern = _22_912.is_pattern; instantiate_targs = _22_912.instantiate_targs; instantiate_vargs = _22_912.instantiate_vargs; effects = _22_912.effects; generalize = _22_912.generalize; letrecs = _22_912.letrecs; top_level = _22_912.top_level; check_uvars = _22_912.check_uvars; use_eq = false; is_iface = _22_912.is_iface; admit = _22_912.admit; default_effects = _22_912.default_effects}), (expected_typ env)))

let fold_env = (fun env f a -> (Support.List.fold_right (fun e a -> (f a e)) env.gamma a))

let binding_of_binder = (fun b -> (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
Binding_typ ((a.Microsoft_FStar_Absyn_Syntax.v, a.Microsoft_FStar_Absyn_Syntax.sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
Binding_var ((x.Microsoft_FStar_Absyn_Syntax.v, x.Microsoft_FStar_Absyn_Syntax.sort))
end))

let binders = (fun env -> (Support.List.fold_left (fun out b -> (match (b) with
| Binding_var ((x, t)) -> begin
((Microsoft_FStar_Absyn_Syntax.v_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s x t)))::out
end
| Binding_typ ((a, k)) -> begin
((Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)))::out
end
| _ -> begin
out
end)) [] env.gamma))

let t_binders = (fun env -> (Support.List.fold_left (fun out b -> (match (b) with
| Binding_var (_) -> begin
out
end
| Binding_typ ((a, k)) -> begin
((Microsoft_FStar_Absyn_Syntax.t_binder (Microsoft_FStar_Absyn_Util.bvd_to_bvar_s a k)))::out
end
| _ -> begin
out
end)) [] env.gamma))

let idents = (fun env -> (Microsoft_FStar_Absyn_Syntax.freevars_of_list ((Support.List.map (Support.Prims.fst)) (binders env))))

let lidents = (fun env -> (let keys = (Support.List.fold_left (fun keys _22_13 -> (match (_22_13) with
| Binding_sig (s) -> begin
(Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt s) keys)
end
| _ -> begin
keys
end)) [] env.gamma)
in (Support.Microsoft.FStar.Util.smap_fold (sigtab env) (fun _22_958 v keys -> (Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt v) keys)) keys)))




