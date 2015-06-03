
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
in (let _180228 = (Support.List.iter (fun se -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun l -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (signature_to_sigtables (Support.List.collect (fun _180234 -> (match (_180234) with
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

let bound_vars = (fun env -> ((Support.List.collect (fun _180197 -> (match (_180197) with
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

let debug = (fun env l -> (((Support.Microsoft.FStar.Util.for_some (fun x -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))) (Support.ST.read Microsoft_FStar_Options.debug)) && (Microsoft_FStar_Options.debug_level_geq l)))

let show = (fun env -> ((Support.Microsoft.FStar.Util.for_some (fun x -> (env.curmodule.Microsoft_FStar_Absyn_Syntax.str = x))) (Support.ST.read Microsoft_FStar_Options.show_signatures)))

let new_sigtab = (fun _180301 -> (match (_180301) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (Support.List.hd env.sigtab))

let push = (fun env msg -> (let _180305 = (env.solver.push msg)
in (let _180307 = env
in {solver = _180307.solver; range = _180307.range; curmodule = _180307.curmodule; gamma = _180307.gamma; modules = _180307.modules; expected_typ = _180307.expected_typ; level = _180307.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _180307.is_pattern; instantiate_targs = _180307.instantiate_targs; instantiate_vargs = _180307.instantiate_vargs; effects = _180307.effects; generalize = _180307.generalize; letrecs = _180307.letrecs; top_level = _180307.top_level; check_uvars = _180307.check_uvars; use_eq = _180307.use_eq; is_iface = _180307.is_iface; admit = _180307.admit; default_effects = _180307.default_effects})))

let mark = (fun env -> (let _180310 = (env.solver.mark "USER MARK")
in (let _180312 = env
in {solver = _180312.solver; range = _180312.range; curmodule = _180312.curmodule; gamma = _180312.gamma; modules = _180312.modules; expected_typ = _180312.expected_typ; level = _180312.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _180312.is_pattern; instantiate_targs = _180312.instantiate_targs; instantiate_vargs = _180312.instantiate_vargs; effects = _180312.effects; generalize = _180312.generalize; letrecs = _180312.letrecs; top_level = _180312.top_level; check_uvars = _180312.check_uvars; use_eq = _180312.use_eq; is_iface = _180312.is_iface; admit = _180312.admit; default_effects = _180312.default_effects})))

let commit_mark = (fun env -> (let _180315 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_::tl -> begin
(hd)::tl
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let _180326 = env
in {solver = _180326.solver; range = _180326.range; curmodule = _180326.curmodule; gamma = _180326.gamma; modules = _180326.modules; expected_typ = _180326.expected_typ; level = _180326.level; sigtab = sigtab; is_pattern = _180326.is_pattern; instantiate_targs = _180326.instantiate_targs; instantiate_vargs = _180326.instantiate_vargs; effects = _180326.effects; generalize = _180326.generalize; letrecs = _180326.letrecs; top_level = _180326.top_level; check_uvars = _180326.check_uvars; use_eq = _180326.use_eq; is_iface = _180326.is_iface; admit = _180326.admit; default_effects = _180326.default_effects}))))

let reset_mark = (fun env -> (let _180329 = (env.solver.reset_mark "USER MARK")
in (let _180331 = env
in {solver = _180331.solver; range = _180331.range; curmodule = _180331.curmodule; gamma = _180331.gamma; modules = _180331.modules; expected_typ = _180331.expected_typ; level = _180331.level; sigtab = (Support.List.tl env.sigtab); is_pattern = _180331.is_pattern; instantiate_targs = _180331.instantiate_targs; instantiate_vargs = _180331.instantiate_vargs; effects = _180331.effects; generalize = _180331.generalize; letrecs = _180331.letrecs; top_level = _180331.top_level; check_uvars = _180331.check_uvars; use_eq = _180331.use_eq; is_iface = _180331.is_iface; admit = _180331.admit; default_effects = _180331.default_effects})))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(failwith ("Too many pops"))
end
| _::tl -> begin
(let _180343 = (env.solver.pop msg)
in (let _180345 = env
in {solver = _180345.solver; range = _180345.range; curmodule = _180345.curmodule; gamma = _180345.gamma; modules = _180345.modules; expected_typ = _180345.expected_typ; level = _180345.level; sigtab = tl; is_pattern = _180345.is_pattern; instantiate_targs = _180345.instantiate_targs; instantiate_vargs = _180345.instantiate_vargs; effects = _180345.effects; generalize = _180345.generalize; letrecs = _180345.letrecs; top_level = _180345.top_level; check_uvars = _180345.check_uvars; use_eq = _180345.use_eq; is_iface = _180345.is_iface; admit = _180345.admit; default_effects = _180345.default_effects}))
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
(match (((Support.Microsoft.FStar.Util.find_opt (fun _180380 -> (match (_180380) with
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
(failwith ((Support.Microsoft.FStar.Util.format1 "Impossible: declaration for monad %s not found" m.Microsoft_FStar_Absyn_Syntax.str)))
end
| Some (md) -> begin
(match (md.Microsoft_FStar_Absyn_Syntax.signature.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (((Support.Microsoft.FStar.Util.Inl (a), _)::(Support.Microsoft.FStar.Util.Inl (wp), _)::(Support.Microsoft.FStar.Util.Inl (wlp), _)::[], {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Kind_effect; Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(a, wp.Microsoft_FStar_Absyn_Syntax.sort)
end
| _ -> begin
(failwith ("Impossible"))
end)
end))

let wp_signature = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun env l -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun _180433 -> (match (_180433) with
| (l', m) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun _180198 -> (match (_180198) with
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
(let _180447 = env
in {solver = _180447.solver; range = _180447.range; curmodule = _180447.curmodule; gamma = _180447.gamma; modules = _180447.modules; expected_typ = _180447.expected_typ; level = _180447.level; sigtab = _180447.sigtab; is_pattern = _180447.is_pattern; instantiate_targs = _180447.instantiate_targs; instantiate_vargs = _180447.instantiate_vargs; effects = _180447.effects; generalize = _180447.generalize; letrecs = _180447.letrecs; top_level = _180447.top_level; check_uvars = _180447.check_uvars; use_eq = _180447.use_eq; is_iface = _180447.is_iface; admit = _180447.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
(let effects = (let _180459 = env.effects
in {decls = (ne)::env.effects.decls; order = _180459.order; joins = _180459.joins})
in (let _180462 = env
in {solver = _180462.solver; range = _180462.range; curmodule = _180462.curmodule; gamma = _180462.gamma; modules = _180462.modules; expected_typ = _180462.expected_typ; level = _180462.level; sigtab = _180462.sigtab; is_pattern = _180462.is_pattern; instantiate_targs = _180462.instantiate_targs; instantiate_vargs = _180462.instantiate_vargs; effects = effects; generalize = _180462.generalize; letrecs = _180462.letrecs; top_level = _180462.top_level; check_uvars = _180462.check_uvars; use_eq = _180462.use_eq; is_iface = _180462.is_iface; admit = _180462.admit; default_effects = _180462.default_effects}))
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
in (let find_edge = (fun order _180494 -> (match (_180494) with
| (i, j) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals i j) then begin
(Some (id_edge i))
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
in (let effects = (let _180538 = env.effects
in {decls = _180538.decls; order = order; joins = joins})
in (let _180541 = env
in {solver = _180541.solver; range = _180541.range; curmodule = _180541.curmodule; gamma = _180541.gamma; modules = _180541.modules; expected_typ = _180541.expected_typ; level = _180541.level; sigtab = _180541.sigtab; is_pattern = _180541.is_pattern; instantiate_targs = _180541.instantiate_targs; instantiate_vargs = _180541.instantiate_vargs; effects = effects; generalize = _180541.generalize; letrecs = _180541.letrecs; top_level = _180541.top_level; check_uvars = _180541.check_uvars; use_eq = _180541.use_eq; is_iface = _180541.is_iface; admit = _180541.admit; default_effects = _180541.default_effects})))))))))))))
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
((Support.List.collect (fun _180199 -> (match (_180199) with
| Binding_sig (se) -> begin
(se)::[]
end
| _ -> begin
[]
end))) env.gamma)
end else begin
m.Microsoft_FStar_Absyn_Syntax.exports
end
in (let _180570 = (add_sigelts env sigs)
in (let _180572 = env
in {solver = _180572.solver; range = _180572.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _180572.expected_typ; level = _180572.level; sigtab = _180572.sigtab; is_pattern = _180572.is_pattern; instantiate_targs = _180572.instantiate_targs; instantiate_vargs = _180572.instantiate_vargs; effects = _180572.effects; generalize = _180572.generalize; letrecs = _180572.letrecs; top_level = _180572.top_level; check_uvars = _180572.check_uvars; use_eq = _180572.use_eq; is_iface = _180572.is_iface; admit = _180572.admit; default_effects = _180572.default_effects}))))

let set_level = (fun env level -> (let _180576 = env
in {solver = _180576.solver; range = _180576.range; curmodule = _180576.curmodule; gamma = _180576.gamma; modules = _180576.modules; expected_typ = _180576.expected_typ; level = level; sigtab = _180576.sigtab; is_pattern = _180576.is_pattern; instantiate_targs = _180576.instantiate_targs; instantiate_vargs = _180576.instantiate_vargs; effects = _180576.effects; generalize = _180576.generalize; letrecs = _180576.letrecs; top_level = _180576.top_level; check_uvars = _180576.check_uvars; use_eq = _180576.use_eq; is_iface = _180576.is_iface; admit = _180576.admit; default_effects = _180576.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _180584 = env
in {solver = _180584.solver; range = _180584.range; curmodule = lid; gamma = _180584.gamma; modules = _180584.modules; expected_typ = _180584.expected_typ; level = _180584.level; sigtab = _180584.sigtab; is_pattern = _180584.is_pattern; instantiate_targs = _180584.instantiate_targs; instantiate_vargs = _180584.instantiate_vargs; effects = _180584.effects; generalize = _180584.generalize; letrecs = _180584.letrecs; top_level = _180584.top_level; check_uvars = _180584.check_uvars; use_eq = _180584.use_eq; is_iface = _180584.is_iface; admit = _180584.admit; default_effects = _180584.default_effects}))

let set_range = (fun e r -> if (r = Microsoft_FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _180588 = e
in {solver = _180588.solver; range = r; curmodule = _180588.curmodule; gamma = _180588.gamma; modules = _180588.modules; expected_typ = _180588.expected_typ; level = _180588.level; sigtab = _180588.sigtab; is_pattern = _180588.is_pattern; instantiate_targs = _180588.instantiate_targs; instantiate_vargs = _180588.instantiate_vargs; effects = _180588.effects; generalize = _180588.generalize; letrecs = _180588.letrecs; top_level = _180588.top_level; check_uvars = _180588.check_uvars; use_eq = _180588.use_eq; is_iface = _180588.is_iface; admit = _180588.admit; default_effects = _180588.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (Support.Microsoft.FStar.Util.smap_try_find (sigtab env) (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)))

let lookup_bvvdef = (fun env bvvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _180200 -> (match (_180200) with
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
(Support.Microsoft.FStar.Util.find_map env.gamma (fun _180201 -> (match (_180201) with
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

let lookup_projector = (fun env lid i -> (let fail = (fun _180696 -> (match (_180696) with
| () -> begin
(failwith ((Support.Microsoft.FStar.Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" (Support.Microsoft.FStar.Util.string_of_int i) (Microsoft_FStar_Absyn_Print.sli lid))))
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

let lookup_lid = (fun env lid -> (let not_found = (fun _180742 -> (match (_180742) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))
in (let mapper = (fun _180203 -> (match (_180203) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, (_, t, _)::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, lbs), _, _, _))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun _180202 -> (match (_180202) with
| (Support.Microsoft.FStar.Util.Inl (_), _, _) -> begin
(failwith ("impossible"))
end
| (Support.Microsoft.FStar.Util.Inr (lid'), t, e) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals lid lid') then begin
Some (t)
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
(let _180817 = t
in {Microsoft_FStar_Absyn_Syntax.n = _180817.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _180817.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid); Microsoft_FStar_Absyn_Syntax.fvs = _180817.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _180817.Microsoft_FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)))) -> begin
((Support.Microsoft.FStar.Util.for_some (fun _180204 -> (match (_180204) with
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
(Support.Microsoft.FStar.Util.for_some (fun _180205 -> (match (_180205) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _180206 -> (match (_180206) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _180207 -> (match (_180207) with
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

let lookup_btvdef = (fun env btvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _180208 -> (match (_180208) with
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
(Support.Microsoft.FStar.Util.for_some (fun _180209 -> (match (_180209) with
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
(Some (Microsoft_FStar_Absyn_Util.close_kind ne.Microsoft_FStar_Absyn_Syntax.binders ne.Microsoft_FStar_Absyn_Syntax.signature))
end
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, binders, _, _, _)))) -> begin
(Some (Microsoft_FStar_Absyn_Util.close_kind binders Microsoft_FStar_Absyn_Syntax.mk_Kind_effect))
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

let lookup_operator = (fun env opname -> (let primName = (Microsoft_FStar_Absyn_Syntax.lid_of_path (("Prims")::((Support.String.strcat "\x5fdummy\x5f" opname.Microsoft_FStar_Absyn_Syntax.idText))::[]) Microsoft_FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun env s -> (build_lattice (let _181058 = env
in {solver = _181058.solver; range = _181058.range; curmodule = _181058.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _181058.modules; expected_typ = _181058.expected_typ; level = _181058.level; sigtab = _181058.sigtab; is_pattern = _181058.is_pattern; instantiate_targs = _181058.instantiate_targs; instantiate_vargs = _181058.instantiate_vargs; effects = _181058.effects; generalize = _181058.generalize; letrecs = _181058.letrecs; top_level = _181058.top_level; check_uvars = _181058.check_uvars; use_eq = _181058.use_eq; is_iface = _181058.is_iface; admit = _181058.admit; default_effects = _181058.default_effects}) s))

let push_local_binding = (fun env b -> (let _181062 = env
in {solver = _181062.solver; range = _181062.range; curmodule = _181062.curmodule; gamma = (b)::env.gamma; modules = _181062.modules; expected_typ = _181062.expected_typ; level = _181062.level; sigtab = _181062.sigtab; is_pattern = _181062.is_pattern; instantiate_targs = _181062.instantiate_targs; instantiate_vargs = _181062.instantiate_vargs; effects = _181062.effects; generalize = _181062.generalize; letrecs = _181062.letrecs; top_level = _181062.top_level; check_uvars = _181062.check_uvars; use_eq = _181062.use_eq; is_iface = _181062.is_iface; admit = _181062.admit; default_effects = _181062.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = {Microsoft_FStar_Absyn_Syntax.uvars_k = (Microsoft_FStar_Absyn_Syntax.new_uv_set ()); Microsoft_FStar_Absyn_Syntax.uvars_t = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ()); Microsoft_FStar_Absyn_Syntax.uvars_e = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())}
in (let ext = (fun out uvs -> (let _181069 = out
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

let push_module = (fun env m -> (let _181102 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _181104 = env
in {solver = _181104.solver; range = _181104.range; curmodule = _181104.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _181104.level; sigtab = _181104.sigtab; is_pattern = _181104.is_pattern; instantiate_targs = _181104.instantiate_targs; instantiate_vargs = _181104.instantiate_vargs; effects = _181104.effects; generalize = _181104.generalize; letrecs = _181104.letrecs; top_level = _181104.top_level; check_uvars = _181104.check_uvars; use_eq = _181104.use_eq; is_iface = _181104.is_iface; admit = _181104.admit; default_effects = _181104.default_effects})))

let set_expected_typ = (fun env t -> (let _181108 = env
in {solver = _181108.solver; range = _181108.range; curmodule = _181108.curmodule; gamma = _181108.gamma; modules = _181108.modules; expected_typ = Some (t); level = _181108.level; sigtab = _181108.sigtab; is_pattern = _181108.is_pattern; instantiate_targs = _181108.instantiate_targs; instantiate_vargs = _181108.instantiate_vargs; effects = _181108.effects; generalize = _181108.generalize; letrecs = _181108.letrecs; top_level = _181108.top_level; check_uvars = _181108.check_uvars; use_eq = false; is_iface = _181108.is_iface; admit = _181108.admit; default_effects = _181108.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> ((let _181115 = env
in {solver = _181115.solver; range = _181115.range; curmodule = _181115.curmodule; gamma = _181115.gamma; modules = _181115.modules; expected_typ = None; level = _181115.level; sigtab = _181115.sigtab; is_pattern = _181115.is_pattern; instantiate_targs = _181115.instantiate_targs; instantiate_vargs = _181115.instantiate_vargs; effects = _181115.effects; generalize = _181115.generalize; letrecs = _181115.letrecs; top_level = _181115.top_level; check_uvars = _181115.check_uvars; use_eq = false; is_iface = _181115.is_iface; admit = _181115.admit; default_effects = _181115.default_effects}), (expected_typ env)))

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

let lidents = (fun env -> (let keys = (Support.List.fold_left (fun keys _180210 -> (match (_180210) with
| Binding_sig (s) -> begin
(Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt s) keys)
end
| _ -> begin
keys
end)) [] env.gamma)
in (Support.Microsoft.FStar.Util.smap_fold (sigtab env) (fun _181161 v keys -> (Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt v) keys)) keys)))




