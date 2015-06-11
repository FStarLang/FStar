
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
in (let _112335 = (Support.List.iter (fun se -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun l -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (signature_to_sigtables (Support.List.collect (fun _112341 -> (match (_112341) with
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

let bound_vars = (fun env -> ((Support.List.collect (fun _112304 -> (match (_112304) with
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

let new_sigtab = (fun _112408 -> (match (_112408) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (Support.List.hd env.sigtab))

let push = (fun env msg -> (let _112412 = (env.solver.push msg)
in (let _112414 = env
in {solver = _112414.solver; range = _112414.range; curmodule = _112414.curmodule; gamma = _112414.gamma; modules = _112414.modules; expected_typ = _112414.expected_typ; level = _112414.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _112414.is_pattern; instantiate_targs = _112414.instantiate_targs; instantiate_vargs = _112414.instantiate_vargs; effects = _112414.effects; generalize = _112414.generalize; letrecs = _112414.letrecs; top_level = _112414.top_level; check_uvars = _112414.check_uvars; use_eq = _112414.use_eq; is_iface = _112414.is_iface; admit = _112414.admit; default_effects = _112414.default_effects})))

let mark = (fun env -> (let _112417 = (env.solver.mark "USER MARK")
in (let _112419 = env
in {solver = _112419.solver; range = _112419.range; curmodule = _112419.curmodule; gamma = _112419.gamma; modules = _112419.modules; expected_typ = _112419.expected_typ; level = _112419.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _112419.is_pattern; instantiate_targs = _112419.instantiate_targs; instantiate_vargs = _112419.instantiate_vargs; effects = _112419.effects; generalize = _112419.generalize; letrecs = _112419.letrecs; top_level = _112419.top_level; check_uvars = _112419.check_uvars; use_eq = _112419.use_eq; is_iface = _112419.is_iface; admit = _112419.admit; default_effects = _112419.default_effects})))

let commit_mark = (fun env -> (let _112422 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_::tl -> begin
(hd)::tl
end
| _ -> begin
(failwith "Impossible")
end)
in (let _112433 = env
in {solver = _112433.solver; range = _112433.range; curmodule = _112433.curmodule; gamma = _112433.gamma; modules = _112433.modules; expected_typ = _112433.expected_typ; level = _112433.level; sigtab = sigtab; is_pattern = _112433.is_pattern; instantiate_targs = _112433.instantiate_targs; instantiate_vargs = _112433.instantiate_vargs; effects = _112433.effects; generalize = _112433.generalize; letrecs = _112433.letrecs; top_level = _112433.top_level; check_uvars = _112433.check_uvars; use_eq = _112433.use_eq; is_iface = _112433.is_iface; admit = _112433.admit; default_effects = _112433.default_effects}))))

let reset_mark = (fun env -> (let _112436 = (env.solver.reset_mark "USER MARK")
in (let _112438 = env
in {solver = _112438.solver; range = _112438.range; curmodule = _112438.curmodule; gamma = _112438.gamma; modules = _112438.modules; expected_typ = _112438.expected_typ; level = _112438.level; sigtab = (Support.List.tl env.sigtab); is_pattern = _112438.is_pattern; instantiate_targs = _112438.instantiate_targs; instantiate_vargs = _112438.instantiate_vargs; effects = _112438.effects; generalize = _112438.generalize; letrecs = _112438.letrecs; top_level = _112438.top_level; check_uvars = _112438.check_uvars; use_eq = _112438.use_eq; is_iface = _112438.is_iface; admit = _112438.admit; default_effects = _112438.default_effects})))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(failwith "Too many pops")
end
| _::tl -> begin
(let _112450 = (env.solver.pop msg)
in (let _112452 = env
in {solver = _112452.solver; range = _112452.range; curmodule = _112452.curmodule; gamma = _112452.gamma; modules = _112452.modules; expected_typ = _112452.expected_typ; level = _112452.level; sigtab = tl; is_pattern = _112452.is_pattern; instantiate_targs = _112452.instantiate_targs; instantiate_vargs = _112452.instantiate_vargs; effects = _112452.effects; generalize = _112452.generalize; letrecs = _112452.letrecs; top_level = _112452.top_level; check_uvars = _112452.check_uvars; use_eq = _112452.use_eq; is_iface = _112452.is_iface; admit = _112452.admit; default_effects = _112452.default_effects}))
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
(match (((Support.Microsoft.FStar.Util.find_opt (fun _112481 -> (match (_112481) with
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

let default_effect = (fun env l -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun _112540 -> (match (_112540) with
| (l', m) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun _112305 -> (match (_112305) with
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
(let _112559 = env
in {solver = _112559.solver; range = _112559.range; curmodule = _112559.curmodule; gamma = _112559.gamma; modules = _112559.modules; expected_typ = _112559.expected_typ; level = _112559.level; sigtab = _112559.sigtab; is_pattern = _112559.is_pattern; instantiate_targs = _112559.instantiate_targs; instantiate_vargs = _112559.instantiate_vargs; effects = _112559.effects; generalize = _112559.generalize; letrecs = _112559.letrecs; top_level = _112559.top_level; check_uvars = _112559.check_uvars; use_eq = _112559.use_eq; is_iface = _112559.is_iface; admit = _112559.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
(let effects = (let _112566 = env.effects
in {decls = (ne)::env.effects.decls; order = _112566.order; joins = _112566.joins})
in (let _112569 = env
in {solver = _112569.solver; range = _112569.range; curmodule = _112569.curmodule; gamma = _112569.gamma; modules = _112569.modules; expected_typ = _112569.expected_typ; level = _112569.level; sigtab = _112569.sigtab; is_pattern = _112569.is_pattern; instantiate_targs = _112569.instantiate_targs; instantiate_vargs = _112569.instantiate_vargs; effects = effects; generalize = _112569.generalize; letrecs = _112569.letrecs; top_level = _112569.top_level; check_uvars = _112569.check_uvars; use_eq = _112569.use_eq; is_iface = _112569.is_iface; admit = _112569.admit; default_effects = _112569.default_effects}))
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
in (let find_edge = (fun order _112601 -> (match (_112601) with
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
in (let effects = (let _112645 = env.effects
in {decls = _112645.decls; order = order; joins = joins})
in (let _112648 = env
in {solver = _112648.solver; range = _112648.range; curmodule = _112648.curmodule; gamma = _112648.gamma; modules = _112648.modules; expected_typ = _112648.expected_typ; level = _112648.level; sigtab = _112648.sigtab; is_pattern = _112648.is_pattern; instantiate_targs = _112648.instantiate_targs; instantiate_vargs = _112648.instantiate_vargs; effects = effects; generalize = _112648.generalize; letrecs = _112648.letrecs; top_level = _112648.top_level; check_uvars = _112648.check_uvars; use_eq = _112648.use_eq; is_iface = _112648.is_iface; admit = _112648.admit; default_effects = _112648.default_effects})))))))))))))
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
((Support.List.collect (fun _112306 -> (match (_112306) with
| Binding_sig (se) -> begin
(se)::[]
end
| _ -> begin
[]
end))) env.gamma)
end else begin
m.Microsoft_FStar_Absyn_Syntax.exports
end
in (let _112677 = (add_sigelts env sigs)
in (let _112679 = env
in {solver = _112679.solver; range = _112679.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _112679.expected_typ; level = _112679.level; sigtab = _112679.sigtab; is_pattern = _112679.is_pattern; instantiate_targs = _112679.instantiate_targs; instantiate_vargs = _112679.instantiate_vargs; effects = _112679.effects; generalize = _112679.generalize; letrecs = _112679.letrecs; top_level = _112679.top_level; check_uvars = _112679.check_uvars; use_eq = _112679.use_eq; is_iface = _112679.is_iface; admit = _112679.admit; default_effects = _112679.default_effects}))))

let set_level = (fun env level -> (let _112683 = env
in {solver = _112683.solver; range = _112683.range; curmodule = _112683.curmodule; gamma = _112683.gamma; modules = _112683.modules; expected_typ = _112683.expected_typ; level = level; sigtab = _112683.sigtab; is_pattern = _112683.is_pattern; instantiate_targs = _112683.instantiate_targs; instantiate_vargs = _112683.instantiate_vargs; effects = _112683.effects; generalize = _112683.generalize; letrecs = _112683.letrecs; top_level = _112683.top_level; check_uvars = _112683.check_uvars; use_eq = _112683.use_eq; is_iface = _112683.is_iface; admit = _112683.admit; default_effects = _112683.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _112691 = env
in {solver = _112691.solver; range = _112691.range; curmodule = lid; gamma = _112691.gamma; modules = _112691.modules; expected_typ = _112691.expected_typ; level = _112691.level; sigtab = _112691.sigtab; is_pattern = _112691.is_pattern; instantiate_targs = _112691.instantiate_targs; instantiate_vargs = _112691.instantiate_vargs; effects = _112691.effects; generalize = _112691.generalize; letrecs = _112691.letrecs; top_level = _112691.top_level; check_uvars = _112691.check_uvars; use_eq = _112691.use_eq; is_iface = _112691.is_iface; admit = _112691.admit; default_effects = _112691.default_effects}))

let set_range = (fun e r -> if (r = Microsoft_FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _112695 = e
in {solver = _112695.solver; range = r; curmodule = _112695.curmodule; gamma = _112695.gamma; modules = _112695.modules; expected_typ = _112695.expected_typ; level = _112695.level; sigtab = _112695.sigtab; is_pattern = _112695.is_pattern; instantiate_targs = _112695.instantiate_targs; instantiate_vargs = _112695.instantiate_vargs; effects = _112695.effects; generalize = _112695.generalize; letrecs = _112695.letrecs; top_level = _112695.top_level; check_uvars = _112695.check_uvars; use_eq = _112695.use_eq; is_iface = _112695.is_iface; admit = _112695.admit; default_effects = _112695.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (Support.Microsoft.FStar.Util.smap_try_find (sigtab env) (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)))

let lookup_bvvdef = (fun env bvvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _112307 -> (match (_112307) with
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
(Support.Microsoft.FStar.Util.find_map env.gamma (fun _112308 -> (match (_112308) with
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

let lookup_projector = (fun env lid i -> (let fail = (fun _112803 -> (match (_112803) with
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

let lookup_lid = (fun env lid -> (let not_found = (fun _112849 -> (match (_112849) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))
in (let mapper = (fun _112310 -> (match (_112310) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, (_, t, _)::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, lbs), _, _, _))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun _112309 -> (match (_112309) with
| (Support.Microsoft.FStar.Util.Inl (_), _, _) -> begin
(failwith "impossible")
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
(let _112924 = t
in {Microsoft_FStar_Absyn_Syntax.n = _112924.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _112924.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid); Microsoft_FStar_Absyn_Syntax.fvs = _112924.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _112924.Microsoft_FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)))) -> begin
((Support.Microsoft.FStar.Util.for_some (fun _112311 -> (match (_112311) with
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
(Support.Microsoft.FStar.Util.for_some (fun _112312 -> (match (_112312) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _112313 -> (match (_112313) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _112314 -> (match (_112314) with
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

let lookup_btvdef = (fun env btvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _112315 -> (match (_112315) with
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
(Support.Microsoft.FStar.Util.for_some (fun _112316 -> (match (_112316) with
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

let push_sigelt = (fun env s -> (build_lattice (let _113165 = env
in {solver = _113165.solver; range = _113165.range; curmodule = _113165.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _113165.modules; expected_typ = _113165.expected_typ; level = _113165.level; sigtab = _113165.sigtab; is_pattern = _113165.is_pattern; instantiate_targs = _113165.instantiate_targs; instantiate_vargs = _113165.instantiate_vargs; effects = _113165.effects; generalize = _113165.generalize; letrecs = _113165.letrecs; top_level = _113165.top_level; check_uvars = _113165.check_uvars; use_eq = _113165.use_eq; is_iface = _113165.is_iface; admit = _113165.admit; default_effects = _113165.default_effects}) s))

let push_local_binding = (fun env b -> (let _113169 = env
in {solver = _113169.solver; range = _113169.range; curmodule = _113169.curmodule; gamma = (b)::env.gamma; modules = _113169.modules; expected_typ = _113169.expected_typ; level = _113169.level; sigtab = _113169.sigtab; is_pattern = _113169.is_pattern; instantiate_targs = _113169.instantiate_targs; instantiate_vargs = _113169.instantiate_vargs; effects = _113169.effects; generalize = _113169.generalize; letrecs = _113169.letrecs; top_level = _113169.top_level; check_uvars = _113169.check_uvars; use_eq = _113169.use_eq; is_iface = _113169.is_iface; admit = _113169.admit; default_effects = _113169.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = {Microsoft_FStar_Absyn_Syntax.uvars_k = (Microsoft_FStar_Absyn_Syntax.new_uv_set ()); Microsoft_FStar_Absyn_Syntax.uvars_t = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ()); Microsoft_FStar_Absyn_Syntax.uvars_e = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())}
in (let ext = (fun out uvs -> (let _113176 = out
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

let push_module = (fun env m -> (let _113209 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _113211 = env
in {solver = _113211.solver; range = _113211.range; curmodule = _113211.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _113211.level; sigtab = _113211.sigtab; is_pattern = _113211.is_pattern; instantiate_targs = _113211.instantiate_targs; instantiate_vargs = _113211.instantiate_vargs; effects = _113211.effects; generalize = _113211.generalize; letrecs = _113211.letrecs; top_level = _113211.top_level; check_uvars = _113211.check_uvars; use_eq = _113211.use_eq; is_iface = _113211.is_iface; admit = _113211.admit; default_effects = _113211.default_effects})))

let set_expected_typ = (fun env t -> (let _113215 = env
in {solver = _113215.solver; range = _113215.range; curmodule = _113215.curmodule; gamma = _113215.gamma; modules = _113215.modules; expected_typ = Some (t); level = _113215.level; sigtab = _113215.sigtab; is_pattern = _113215.is_pattern; instantiate_targs = _113215.instantiate_targs; instantiate_vargs = _113215.instantiate_vargs; effects = _113215.effects; generalize = _113215.generalize; letrecs = _113215.letrecs; top_level = _113215.top_level; check_uvars = _113215.check_uvars; use_eq = false; is_iface = _113215.is_iface; admit = _113215.admit; default_effects = _113215.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> ((let _113222 = env
in {solver = _113222.solver; range = _113222.range; curmodule = _113222.curmodule; gamma = _113222.gamma; modules = _113222.modules; expected_typ = None; level = _113222.level; sigtab = _113222.sigtab; is_pattern = _113222.is_pattern; instantiate_targs = _113222.instantiate_targs; instantiate_vargs = _113222.instantiate_vargs; effects = _113222.effects; generalize = _113222.generalize; letrecs = _113222.letrecs; top_level = _113222.top_level; check_uvars = _113222.check_uvars; use_eq = false; is_iface = _113222.is_iface; admit = _113222.admit; default_effects = _113222.default_effects}), (expected_typ env)))

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

let lidents = (fun env -> (let keys = (Support.List.fold_left (fun keys _112317 -> (match (_112317) with
| Binding_sig (s) -> begin
(Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt s) keys)
end
| _ -> begin
keys
end)) [] env.gamma)
in (Support.Microsoft.FStar.Util.smap_fold (sigtab env) (fun _113268 v keys -> (Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt v) keys)) keys)))




