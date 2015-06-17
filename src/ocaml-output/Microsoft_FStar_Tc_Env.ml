
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
in (let _112753 = (Support.List.iter (fun se -> (let lids = (Microsoft_FStar_Absyn_Util.lids_of_sigelt se)
in (Support.List.iter (fun l -> (Support.Microsoft.FStar.Util.smap_add ht l.Microsoft_FStar_Absyn_Syntax.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (signature_to_sigtables (Support.List.collect (fun _112759 -> (match (_112759) with
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

let bound_vars = (fun env -> ((Support.List.collect (fun _112722 -> (match (_112722) with
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

let new_sigtab = (fun _112826 -> (match (_112826) with
| () -> begin
(Support.Microsoft.FStar.Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (Support.List.hd env.sigtab))

let push = (fun env msg -> (let _112830 = (env.solver.push msg)
in (let _112832 = env
in {solver = _112832.solver; range = _112832.range; curmodule = _112832.curmodule; gamma = _112832.gamma; modules = _112832.modules; expected_typ = _112832.expected_typ; level = _112832.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _112832.is_pattern; instantiate_targs = _112832.instantiate_targs; instantiate_vargs = _112832.instantiate_vargs; effects = _112832.effects; generalize = _112832.generalize; letrecs = _112832.letrecs; top_level = _112832.top_level; check_uvars = _112832.check_uvars; use_eq = _112832.use_eq; is_iface = _112832.is_iface; admit = _112832.admit; default_effects = _112832.default_effects})))

let mark = (fun env -> (let _112835 = (env.solver.mark "USER MARK")
in (let _112837 = env
in {solver = _112837.solver; range = _112837.range; curmodule = _112837.curmodule; gamma = _112837.gamma; modules = _112837.modules; expected_typ = _112837.expected_typ; level = _112837.level; sigtab = ((Support.Microsoft.FStar.Util.smap_copy (sigtab env)))::env.sigtab; is_pattern = _112837.is_pattern; instantiate_targs = _112837.instantiate_targs; instantiate_vargs = _112837.instantiate_vargs; effects = _112837.effects; generalize = _112837.generalize; letrecs = _112837.letrecs; top_level = _112837.top_level; check_uvars = _112837.check_uvars; use_eq = _112837.use_eq; is_iface = _112837.is_iface; admit = _112837.admit; default_effects = _112837.default_effects})))

let commit_mark = (fun env -> (let _112840 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_::tl -> begin
(hd)::tl
end
| _ -> begin
(failwith "Impossible")
end)
in (let _112851 = env
in {solver = _112851.solver; range = _112851.range; curmodule = _112851.curmodule; gamma = _112851.gamma; modules = _112851.modules; expected_typ = _112851.expected_typ; level = _112851.level; sigtab = sigtab; is_pattern = _112851.is_pattern; instantiate_targs = _112851.instantiate_targs; instantiate_vargs = _112851.instantiate_vargs; effects = _112851.effects; generalize = _112851.generalize; letrecs = _112851.letrecs; top_level = _112851.top_level; check_uvars = _112851.check_uvars; use_eq = _112851.use_eq; is_iface = _112851.is_iface; admit = _112851.admit; default_effects = _112851.default_effects}))))

let reset_mark = (fun env -> (let _112854 = (env.solver.reset_mark "USER MARK")
in (let _112856 = env
in {solver = _112856.solver; range = _112856.range; curmodule = _112856.curmodule; gamma = _112856.gamma; modules = _112856.modules; expected_typ = _112856.expected_typ; level = _112856.level; sigtab = (Support.List.tl env.sigtab); is_pattern = _112856.is_pattern; instantiate_targs = _112856.instantiate_targs; instantiate_vargs = _112856.instantiate_vargs; effects = _112856.effects; generalize = _112856.generalize; letrecs = _112856.letrecs; top_level = _112856.top_level; check_uvars = _112856.check_uvars; use_eq = _112856.use_eq; is_iface = _112856.is_iface; admit = _112856.admit; default_effects = _112856.default_effects})))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(failwith "Too many pops")
end
| _::tl -> begin
(let _112868 = (env.solver.pop msg)
in (let _112870 = env
in {solver = _112870.solver; range = _112870.range; curmodule = _112870.curmodule; gamma = _112870.gamma; modules = _112870.modules; expected_typ = _112870.expected_typ; level = _112870.level; sigtab = tl; is_pattern = _112870.is_pattern; instantiate_targs = _112870.instantiate_targs; instantiate_vargs = _112870.instantiate_vargs; effects = _112870.effects; generalize = _112870.generalize; letrecs = _112870.letrecs; top_level = _112870.top_level; check_uvars = _112870.check_uvars; use_eq = _112870.use_eq; is_iface = _112870.is_iface; admit = _112870.admit; default_effects = _112870.default_effects}))
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
(match (((Support.Microsoft.FStar.Util.find_opt (fun _112899 -> (match (_112899) with
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

let default_effect = (fun env l -> (Support.Microsoft.FStar.Util.find_map env.default_effects (fun _112958 -> (match (_112958) with
| (l', m) -> begin
if (Microsoft_FStar_Absyn_Syntax.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, _, c, quals, r)) -> begin
(match ((Support.Microsoft.FStar.Util.find_map quals (fun _112723 -> (match (_112723) with
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
(let _112977 = env
in {solver = _112977.solver; range = _112977.range; curmodule = _112977.curmodule; gamma = _112977.gamma; modules = _112977.modules; expected_typ = _112977.expected_typ; level = _112977.level; sigtab = _112977.sigtab; is_pattern = _112977.is_pattern; instantiate_targs = _112977.instantiate_targs; instantiate_vargs = _112977.instantiate_vargs; effects = _112977.effects; generalize = _112977.generalize; letrecs = _112977.letrecs; top_level = _112977.top_level; check_uvars = _112977.check_uvars; use_eq = _112977.use_eq; is_iface = _112977.is_iface; admit = _112977.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((ne, _)) -> begin
(let effects = (let _112984 = env.effects
in {decls = (ne)::env.effects.decls; order = _112984.order; joins = _112984.joins})
in (let _112987 = env
in {solver = _112987.solver; range = _112987.range; curmodule = _112987.curmodule; gamma = _112987.gamma; modules = _112987.modules; expected_typ = _112987.expected_typ; level = _112987.level; sigtab = _112987.sigtab; is_pattern = _112987.is_pattern; instantiate_targs = _112987.instantiate_targs; instantiate_vargs = _112987.instantiate_vargs; effects = effects; generalize = _112987.generalize; letrecs = _112987.letrecs; top_level = _112987.top_level; check_uvars = _112987.check_uvars; use_eq = _112987.use_eq; is_iface = _112987.is_iface; admit = _112987.admit; default_effects = _112987.default_effects}))
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
in (let find_edge = (fun order _113019 -> (match (_113019) with
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
in (let effects = (let _113063 = env.effects
in {decls = _113063.decls; order = order; joins = joins})
in (let _113066 = env
in {solver = _113066.solver; range = _113066.range; curmodule = _113066.curmodule; gamma = _113066.gamma; modules = _113066.modules; expected_typ = _113066.expected_typ; level = _113066.level; sigtab = _113066.sigtab; is_pattern = _113066.is_pattern; instantiate_targs = _113066.instantiate_targs; instantiate_vargs = _113066.instantiate_vargs; effects = effects; generalize = _113066.generalize; letrecs = _113066.letrecs; top_level = _113066.top_level; check_uvars = _113066.check_uvars; use_eq = _113066.use_eq; is_iface = _113066.is_iface; admit = _113066.admit; default_effects = _113066.default_effects})))))))))))))
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
((Support.List.collect (fun _112724 -> (match (_112724) with
| Binding_sig (se) -> begin
(se)::[]
end
| _ -> begin
[]
end))) env.gamma)
end else begin
m.Microsoft_FStar_Absyn_Syntax.exports
end
in (let _113095 = (add_sigelts env sigs)
in (let _113097 = env
in {solver = _113097.solver; range = _113097.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _113097.expected_typ; level = _113097.level; sigtab = _113097.sigtab; is_pattern = _113097.is_pattern; instantiate_targs = _113097.instantiate_targs; instantiate_vargs = _113097.instantiate_vargs; effects = _113097.effects; generalize = _113097.generalize; letrecs = _113097.letrecs; top_level = _113097.top_level; check_uvars = _113097.check_uvars; use_eq = _113097.use_eq; is_iface = _113097.is_iface; admit = _113097.admit; default_effects = _113097.default_effects}))))

let set_level = (fun env level -> (let _113101 = env
in {solver = _113101.solver; range = _113101.range; curmodule = _113101.curmodule; gamma = _113101.gamma; modules = _113101.modules; expected_typ = _113101.expected_typ; level = level; sigtab = _113101.sigtab; is_pattern = _113101.is_pattern; instantiate_targs = _113101.instantiate_targs; instantiate_vargs = _113101.instantiate_vargs; effects = _113101.effects; generalize = _113101.generalize; letrecs = _113101.letrecs; top_level = _113101.top_level; check_uvars = _113101.check_uvars; use_eq = _113101.use_eq; is_iface = _113101.is_iface; admit = _113101.admit; default_effects = _113101.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _113109 = env
in {solver = _113109.solver; range = _113109.range; curmodule = lid; gamma = _113109.gamma; modules = _113109.modules; expected_typ = _113109.expected_typ; level = _113109.level; sigtab = _113109.sigtab; is_pattern = _113109.is_pattern; instantiate_targs = _113109.instantiate_targs; instantiate_vargs = _113109.instantiate_vargs; effects = _113109.effects; generalize = _113109.generalize; letrecs = _113109.letrecs; top_level = _113109.top_level; check_uvars = _113109.check_uvars; use_eq = _113109.use_eq; is_iface = _113109.is_iface; admit = _113109.admit; default_effects = _113109.default_effects}))

let set_range = (fun e r -> if (r = Microsoft_FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _113113 = e
in {solver = _113113.solver; range = r; curmodule = _113113.curmodule; gamma = _113113.gamma; modules = _113113.modules; expected_typ = _113113.expected_typ; level = _113113.level; sigtab = _113113.sigtab; is_pattern = _113113.is_pattern; instantiate_targs = _113113.instantiate_targs; instantiate_vargs = _113113.instantiate_vargs; effects = _113113.effects; generalize = _113113.generalize; letrecs = _113113.letrecs; top_level = _113113.top_level; check_uvars = _113113.check_uvars; use_eq = _113113.use_eq; is_iface = _113113.is_iface; admit = _113113.admit; default_effects = _113113.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (Support.Microsoft.FStar.Util.smap_try_find (sigtab env) (Microsoft_FStar_Absyn_Syntax.text_of_lid lid)))

let lookup_bvvdef = (fun env bvvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _112725 -> (match (_112725) with
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
(Support.Microsoft.FStar.Util.find_map env.gamma (fun _112726 -> (match (_112726) with
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

let lookup_projector = (fun env lid i -> (let fail = (fun _113221 -> (match (_113221) with
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

let lookup_lid = (fun env lid -> (let not_found = (fun _113267 -> (match (_113267) with
| () -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Error (((name_not_found lid), (Microsoft_FStar_Absyn_Syntax.range_of_lid lid)))))
end))
in (let mapper = (fun _112728 -> (match (_112728) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, t, _, _, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, t, _, _)))) | (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, (_, t, _)::[]), _, _, _)))) -> begin
Some (t)
end
| Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_let (((_, lbs), _, _, _))) -> begin
(Support.Microsoft.FStar.Util.find_map lbs (fun _112727 -> (match (_112727) with
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
(let _113342 = t
in {Microsoft_FStar_Absyn_Syntax.n = _113342.Microsoft_FStar_Absyn_Syntax.n; Microsoft_FStar_Absyn_Syntax.tk = _113342.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = (Microsoft_FStar_Absyn_Syntax.range_of_lid lid); Microsoft_FStar_Absyn_Syntax.fvs = _113342.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _113342.Microsoft_FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (Support.Microsoft.FStar.Util.Inr (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, quals, _)))) -> begin
((Support.Microsoft.FStar.Util.for_some (fun _112729 -> (match (_112729) with
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
(Support.Microsoft.FStar.Util.for_some (fun _112730 -> (match (_112730) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _112731 -> (match (_112731) with
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
if ((Support.Microsoft.FStar.Util.for_some (fun _112732 -> (match (_112732) with
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

let lookup_btvdef = (fun env btvd -> (Support.Microsoft.FStar.Util.find_map env.gamma (fun _112733 -> (match (_112733) with
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
(Support.Microsoft.FStar.Util.for_some (fun _112734 -> (match (_112734) with
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

let push_sigelt = (fun env s -> (build_lattice (let _113583 = env
in {solver = _113583.solver; range = _113583.range; curmodule = _113583.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _113583.modules; expected_typ = _113583.expected_typ; level = _113583.level; sigtab = _113583.sigtab; is_pattern = _113583.is_pattern; instantiate_targs = _113583.instantiate_targs; instantiate_vargs = _113583.instantiate_vargs; effects = _113583.effects; generalize = _113583.generalize; letrecs = _113583.letrecs; top_level = _113583.top_level; check_uvars = _113583.check_uvars; use_eq = _113583.use_eq; is_iface = _113583.is_iface; admit = _113583.admit; default_effects = _113583.default_effects}) s))

let push_local_binding = (fun env b -> (let _113587 = env
in {solver = _113587.solver; range = _113587.range; curmodule = _113587.curmodule; gamma = (b)::env.gamma; modules = _113587.modules; expected_typ = _113587.expected_typ; level = _113587.level; sigtab = _113587.sigtab; is_pattern = _113587.is_pattern; instantiate_targs = _113587.instantiate_targs; instantiate_vargs = _113587.instantiate_vargs; effects = _113587.effects; generalize = _113587.generalize; letrecs = _113587.letrecs; top_level = _113587.top_level; check_uvars = _113587.check_uvars; use_eq = _113587.use_eq; is_iface = _113587.is_iface; admit = _113587.admit; default_effects = _113587.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = {Microsoft_FStar_Absyn_Syntax.uvars_k = (Microsoft_FStar_Absyn_Syntax.new_uv_set ()); Microsoft_FStar_Absyn_Syntax.uvars_t = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ()); Microsoft_FStar_Absyn_Syntax.uvars_e = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())}
in (let ext = (fun out uvs -> (let _113594 = out
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

let push_module = (fun env m -> (let _113627 = (add_sigelts env m.Microsoft_FStar_Absyn_Syntax.exports)
in (let _113629 = env
in {solver = _113629.solver; range = _113629.range; curmodule = _113629.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _113629.level; sigtab = _113629.sigtab; is_pattern = _113629.is_pattern; instantiate_targs = _113629.instantiate_targs; instantiate_vargs = _113629.instantiate_vargs; effects = _113629.effects; generalize = _113629.generalize; letrecs = _113629.letrecs; top_level = _113629.top_level; check_uvars = _113629.check_uvars; use_eq = _113629.use_eq; is_iface = _113629.is_iface; admit = _113629.admit; default_effects = _113629.default_effects})))

let set_expected_typ = (fun env t -> (let _113633 = env
in {solver = _113633.solver; range = _113633.range; curmodule = _113633.curmodule; gamma = _113633.gamma; modules = _113633.modules; expected_typ = Some (t); level = _113633.level; sigtab = _113633.sigtab; is_pattern = _113633.is_pattern; instantiate_targs = _113633.instantiate_targs; instantiate_vargs = _113633.instantiate_vargs; effects = _113633.effects; generalize = _113633.generalize; letrecs = _113633.letrecs; top_level = _113633.top_level; check_uvars = _113633.check_uvars; use_eq = false; is_iface = _113633.is_iface; admit = _113633.admit; default_effects = _113633.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> ((let _113640 = env
in {solver = _113640.solver; range = _113640.range; curmodule = _113640.curmodule; gamma = _113640.gamma; modules = _113640.modules; expected_typ = None; level = _113640.level; sigtab = _113640.sigtab; is_pattern = _113640.is_pattern; instantiate_targs = _113640.instantiate_targs; instantiate_vargs = _113640.instantiate_vargs; effects = _113640.effects; generalize = _113640.generalize; letrecs = _113640.letrecs; top_level = _113640.top_level; check_uvars = _113640.check_uvars; use_eq = false; is_iface = _113640.is_iface; admit = _113640.admit; default_effects = _113640.default_effects}), (expected_typ env)))

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

let lidents = (fun env -> (let keys = (Support.List.fold_left (fun keys _112735 -> (match (_112735) with
| Binding_sig (s) -> begin
(Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt s) keys)
end
| _ -> begin
keys
end)) [] env.gamma)
in (Support.Microsoft.FStar.Util.smap_fold (sigtab env) (fun _113686 v keys -> (Support.List.append (Microsoft_FStar_Absyn_Util.lids_of_sigelt v) keys)) keys)))




