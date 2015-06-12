
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
in (let _112712 = (Support.List.iter (fun se -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun l -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (signature_to_sigtables (Support.List.collect (fun _112718 -> (match (_112718) with
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

let bound_vars = (fun env -> ((Support.List.collect (fun _112681 -> (match (_112681) with
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

let new_sigtab = (fun _112785 -> (match (_112785) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (Support.List.hd env.sigtab))

let push = (fun env msg -> (let _112789 = (env.solver.push msg)
in (let _112791 = env
in {solver = _112791.solver; range = _112791.range; curmodule = _112791.curmodule; gamma = _112791.gamma; modules = _112791.modules; expected_typ = _112791.expected_typ; level = _112791.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _112791.is_pattern; instantiate_targs = _112791.instantiate_targs; instantiate_vargs = _112791.instantiate_vargs; effects = _112791.effects; generalize = _112791.generalize; letrecs = _112791.letrecs; top_level = _112791.top_level; check_uvars = _112791.check_uvars; use_eq = _112791.use_eq; is_iface = _112791.is_iface; admit = _112791.admit; default_effects = _112791.default_effects})))

let mark = (fun env -> (let _112794 = (env.solver.mark "USER MARK")
in (let _112796 = env
in {solver = _112796.solver; range = _112796.range; curmodule = _112796.curmodule; gamma = _112796.gamma; modules = _112796.modules; expected_typ = _112796.expected_typ; level = _112796.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _112796.is_pattern; instantiate_targs = _112796.instantiate_targs; instantiate_vargs = _112796.instantiate_vargs; effects = _112796.effects; generalize = _112796.generalize; letrecs = _112796.letrecs; top_level = _112796.top_level; check_uvars = _112796.check_uvars; use_eq = _112796.use_eq; is_iface = _112796.is_iface; admit = _112796.admit; default_effects = _112796.default_effects})))

let commit_mark = (fun env -> (let _112799 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_::tl -> begin
(hd)::tl
end
| _ -> begin
(failwith "Impossible")
end)
in (let _112810 = env
in {solver = _112810.solver; range = _112810.range; curmodule = _112810.curmodule; gamma = _112810.gamma; modules = _112810.modules; expected_typ = _112810.expected_typ; level = _112810.level; sigtab = sigtab; is_pattern = _112810.is_pattern; instantiate_targs = _112810.instantiate_targs; instantiate_vargs = _112810.instantiate_vargs; effects = _112810.effects; generalize = _112810.generalize; letrecs = _112810.letrecs; top_level = _112810.top_level; check_uvars = _112810.check_uvars; use_eq = _112810.use_eq; is_iface = _112810.is_iface; admit = _112810.admit; default_effects = _112810.default_effects}))))

let reset_mark = (fun env -> (let _112813 = (env.solver.reset_mark "USER MARK")
in (let _112815 = env
in {solver = _112815.solver; range = _112815.range; curmodule = _112815.curmodule; gamma = _112815.gamma; modules = _112815.modules; expected_typ = _112815.expected_typ; level = _112815.level; sigtab = (Support.List.tl env.sigtab); is_pattern = _112815.is_pattern; instantiate_targs = _112815.instantiate_targs; instantiate_vargs = _112815.instantiate_vargs; effects = _112815.effects; generalize = _112815.generalize; letrecs = _112815.letrecs; top_level = _112815.top_level; check_uvars = _112815.check_uvars; use_eq = _112815.use_eq; is_iface = _112815.is_iface; admit = _112815.admit; default_effects = _112815.default_effects})))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(failwith "Too many pops")
end
| _::tl -> begin
(let _112827 = (env.solver.pop msg)
in (let _112829 = env
in {solver = _112829.solver; range = _112829.range; curmodule = _112829.curmodule; gamma = _112829.gamma; modules = _112829.modules; expected_typ = _112829.expected_typ; level = _112829.level; sigtab = tl; is_pattern = _112829.is_pattern; instantiate_targs = _112829.instantiate_targs; instantiate_vargs = _112829.instantiate_vargs; effects = _112829.effects; generalize = _112829.generalize; letrecs = _112829.letrecs; top_level = _112829.top_level; check_uvars = _112829.check_uvars; use_eq = _112829.use_eq; is_iface = _112829.is_iface; admit = _112829.admit; default_effects = _112829.default_effects}))
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
(match (((Support.Microsoft.FStar.Util.find_opt (fun _112858 -> (match (_112858) with
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

let default_effect = (fun env l -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun _112917 -> (match (_112917) with
| (l', m) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun _112682 -> (match (_112682) with
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
(let _112936 = env
in {solver = _112936.solver; range = _112936.range; curmodule = _112936.curmodule; gamma = _112936.gamma; modules = _112936.modules; expected_typ = _112936.expected_typ; level = _112936.level; sigtab = _112936.sigtab; is_pattern = _112936.is_pattern; instantiate_targs = _112936.instantiate_targs; instantiate_vargs = _112936.instantiate_vargs; effects = _112936.effects; generalize = _112936.generalize; letrecs = _112936.letrecs; top_level = _112936.top_level; check_uvars = _112936.check_uvars; use_eq = _112936.use_eq; is_iface = _112936.is_iface; admit = _112936.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
(let effects = (let _112943 = env.effects
in {decls = (ne)::env.effects.decls; order = _112943.order; joins = _112943.joins})
in (let _112946 = env
in {solver = _112946.solver; range = _112946.range; curmodule = _112946.curmodule; gamma = _112946.gamma; modules = _112946.modules; expected_typ = _112946.expected_typ; level = _112946.level; sigtab = _112946.sigtab; is_pattern = _112946.is_pattern; instantiate_targs = _112946.instantiate_targs; instantiate_vargs = _112946.instantiate_vargs; effects = effects; generalize = _112946.generalize; letrecs = _112946.letrecs; top_level = _112946.top_level; check_uvars = _112946.check_uvars; use_eq = _112946.use_eq; is_iface = _112946.is_iface; admit = _112946.admit; default_effects = _112946.default_effects}))
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
in (let find_edge = (fun order _112978 -> (match (_112978) with
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
in (let effects = (let _113022 = env.effects
in {decls = _113022.decls; order = order; joins = joins})
in (let _113025 = env
in {solver = _113025.solver; range = _113025.range; curmodule = _113025.curmodule; gamma = _113025.gamma; modules = _113025.modules; expected_typ = _113025.expected_typ; level = _113025.level; sigtab = _113025.sigtab; is_pattern = _113025.is_pattern; instantiate_targs = _113025.instantiate_targs; instantiate_vargs = _113025.instantiate_vargs; effects = effects; generalize = _113025.generalize; letrecs = _113025.letrecs; top_level = _113025.top_level; check_uvars = _113025.check_uvars; use_eq = _113025.use_eq; is_iface = _113025.is_iface; admit = _113025.admit; default_effects = _113025.default_effects})))))))))))))
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
((Support.List.collect (fun _112683 -> (match (_112683) with
| Binding_sig (se) -> begin
(se)::[]
end
| _ -> begin
[]
end))) env.gamma)
end else begin
m.Microsoft_FStar_Absyn_Syntax.exports
end
in (let _113054 = (add_sigelts env sigs)
in (let _113056 = env
in {solver = _113056.solver; range = _113056.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _113056.expected_typ; level = _113056.level; sigtab = _113056.sigtab; is_pattern = _113056.is_pattern; instantiate_targs = _113056.instantiate_targs; instantiate_vargs = _113056.instantiate_vargs; effects = _113056.effects; generalize = _113056.generalize; letrecs = _113056.letrecs; top_level = _113056.top_level; check_uvars = _113056.check_uvars; use_eq = _113056.use_eq; is_iface = _113056.is_iface; admit = _113056.admit; default_effects = _113056.default_effects}))))

let set_level = (fun env level -> (let _113060 = env
in {solver = _113060.solver; range = _113060.range; curmodule = _113060.curmodule; gamma = _113060.gamma; modules = _113060.modules; expected_typ = _113060.expected_typ; level = level; sigtab = _113060.sigtab; is_pattern = _113060.is_pattern; instantiate_targs = _113060.instantiate_targs; instantiate_vargs = _113060.instantiate_vargs; effects = _113060.effects; generalize = _113060.generalize; letrecs = _113060.letrecs; top_level = _113060.top_level; check_uvars = _113060.check_uvars; use_eq = _113060.use_eq; is_iface = _113060.is_iface; admit = _113060.admit; default_effects = _113060.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _113068 = env
in {solver = _113068.solver; range = _113068.range; curmodule = lid; gamma = _113068.gamma; modules = _113068.modules; expected_typ = _113068.expected_typ; level = _113068.level; sigtab = _113068.sigtab; is_pattern = _113068.is_pattern; instantiate_targs = _113068.instantiate_targs; instantiate_vargs = _113068.instantiate_vargs; effects = _113068.effects; generalize = _113068.generalize; letrecs = _113068.letrecs; top_level = _113068.top_level; check_uvars = _113068.check_uvars; use_eq = _113068.use_eq; is_iface = _113068.is_iface; admit = _113068.admit; default_effects = _113068.default_effects}))

let set_range = (fun e r -> if (r = Microsoft_FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _113072 = e
in {solver = _113072.solver; range = r; curmodule = _113072.curmodule; gamma = _113072.gamma; modules = _113072.modules; expected_typ = _113072.expected_typ; level = _113072.level; sigtab = _113072.sigtab; is_pattern = _113072.is_pattern; instantiate_targs = _113072.instantiate_targs; instantiate_vargs = _113072.instantiate_vargs; effects = _113072.effects; generalize = _113072.generalize; letrecs = _113072.letrecs; top_level = _113072.top_level; check_uvars = _113072.check_uvars; use_eq = _113072.use_eq; is_iface = _113072.is_iface; admit = _113072.admit; default_effects = _113072.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (Support.Microsoft.FStar.Util.smap_try_find (sigtab env) (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)))

let lookup_bvvdef = (fun env bvvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _112684 -> (match (_112684) with
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
(Support.Microsoft.FStar.Util.find_map env.gamma (fun _112685 -> (match (_112685) with
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

let lookup_projector = (fun env lid i -> (let fail = (fun _113180 -> (match (_113180) with
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

let lookup_lid = (fun env lid -> (let not_found = (fun _113226 -> (match (_113226) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))
in (let mapper = (fun _112687 -> (match (_112687) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, (_, t, _)::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, lbs), _, _, _))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun _112686 -> (match (_112686) with
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
(let _113301 = t
in {Microsoft_FStar_Absyn_Syntax.n = _113301.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _113301.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid); Microsoft_FStar_Absyn_Syntax.fvs = _113301.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _113301.Microsoft_FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)))) -> begin
((Support.Microsoft.FStar.Util.for_some (fun _112688 -> (match (_112688) with
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
(Support.Microsoft.FStar.Util.for_some (fun _112689 -> (match (_112689) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _112690 -> (match (_112690) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _112691 -> (match (_112691) with
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

let lookup_btvdef = (fun env btvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _112692 -> (match (_112692) with
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
(Support.Microsoft.FStar.Util.for_some (fun _112693 -> (match (_112693) with
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

let push_sigelt = (fun env s -> (build_lattice (let _113542 = env
in {solver = _113542.solver; range = _113542.range; curmodule = _113542.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _113542.modules; expected_typ = _113542.expected_typ; level = _113542.level; sigtab = _113542.sigtab; is_pattern = _113542.is_pattern; instantiate_targs = _113542.instantiate_targs; instantiate_vargs = _113542.instantiate_vargs; effects = _113542.effects; generalize = _113542.generalize; letrecs = _113542.letrecs; top_level = _113542.top_level; check_uvars = _113542.check_uvars; use_eq = _113542.use_eq; is_iface = _113542.is_iface; admit = _113542.admit; default_effects = _113542.default_effects}) s))

let push_local_binding = (fun env b -> (let _113546 = env
in {solver = _113546.solver; range = _113546.range; curmodule = _113546.curmodule; gamma = (b)::env.gamma; modules = _113546.modules; expected_typ = _113546.expected_typ; level = _113546.level; sigtab = _113546.sigtab; is_pattern = _113546.is_pattern; instantiate_targs = _113546.instantiate_targs; instantiate_vargs = _113546.instantiate_vargs; effects = _113546.effects; generalize = _113546.generalize; letrecs = _113546.letrecs; top_level = _113546.top_level; check_uvars = _113546.check_uvars; use_eq = _113546.use_eq; is_iface = _113546.is_iface; admit = _113546.admit; default_effects = _113546.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = {Microsoft_FStar_Absyn_Syntax.uvars_k = (Microsoft_FStar_Absyn_Syntax.new_uv_set ()); Microsoft_FStar_Absyn_Syntax.uvars_t = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ()); Microsoft_FStar_Absyn_Syntax.uvars_e = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())}
in (let ext = (fun out uvs -> (let _113553 = out
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

let push_module = (fun env m -> (let _113586 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _113588 = env
in {solver = _113588.solver; range = _113588.range; curmodule = _113588.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _113588.level; sigtab = _113588.sigtab; is_pattern = _113588.is_pattern; instantiate_targs = _113588.instantiate_targs; instantiate_vargs = _113588.instantiate_vargs; effects = _113588.effects; generalize = _113588.generalize; letrecs = _113588.letrecs; top_level = _113588.top_level; check_uvars = _113588.check_uvars; use_eq = _113588.use_eq; is_iface = _113588.is_iface; admit = _113588.admit; default_effects = _113588.default_effects})))

let set_expected_typ = (fun env t -> (let _113592 = env
in {solver = _113592.solver; range = _113592.range; curmodule = _113592.curmodule; gamma = _113592.gamma; modules = _113592.modules; expected_typ = Some (t); level = _113592.level; sigtab = _113592.sigtab; is_pattern = _113592.is_pattern; instantiate_targs = _113592.instantiate_targs; instantiate_vargs = _113592.instantiate_vargs; effects = _113592.effects; generalize = _113592.generalize; letrecs = _113592.letrecs; top_level = _113592.top_level; check_uvars = _113592.check_uvars; use_eq = false; is_iface = _113592.is_iface; admit = _113592.admit; default_effects = _113592.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> ((let _113599 = env
in {solver = _113599.solver; range = _113599.range; curmodule = _113599.curmodule; gamma = _113599.gamma; modules = _113599.modules; expected_typ = None; level = _113599.level; sigtab = _113599.sigtab; is_pattern = _113599.is_pattern; instantiate_targs = _113599.instantiate_targs; instantiate_vargs = _113599.instantiate_vargs; effects = _113599.effects; generalize = _113599.generalize; letrecs = _113599.letrecs; top_level = _113599.top_level; check_uvars = _113599.check_uvars; use_eq = false; is_iface = _113599.is_iface; admit = _113599.admit; default_effects = _113599.default_effects}), (expected_typ env)))

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

let lidents = (fun env -> (let keys = (Support.List.fold_left (fun keys _112694 -> (match (_112694) with
| Binding_sig (s) -> begin
(Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt s) keys)
end
| _ -> begin
keys
end)) [] env.gamma)
in (Support.Microsoft.FStar.Util.smap_fold (sigtab env) (fun _113645 v keys -> (Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt v) keys)) keys)))




