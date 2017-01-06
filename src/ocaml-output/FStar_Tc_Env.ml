
open Prims

type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ)
| Binding_typ of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd)
| Binding_lid of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)
| Binding_sig of FStar_Absyn_Syntax.sigelt


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_typ = (fun _discr_ -> (match (_discr_) with
| Binding_typ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_lid = (fun _discr_ -> (match (_discr_) with
| Binding_lid (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_sig = (fun _discr_ -> (match (_discr_) with
| Binding_sig (_) -> begin
true
end
| _ -> begin
false
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_42_16) -> begin
_42_16
end))


let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_42_19) -> begin
_42_19
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_42_22) -> begin
_42_22
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_42_25) -> begin
_42_25
end))


type sigtable =
FStar_Absyn_Syntax.sigelt FStar_Util.smap


let default_table_size : Prims.int = (Prims.parse_int "200")


let strlid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  Prims.string Prims.option = (fun se -> (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
Some ((FStar_Ident.text_of_lid l))
end))


let signature_to_sigtables : FStar_Absyn_Syntax.sigelt Prims.list  ->  FStar_Absyn_Syntax.sigelt FStar_Util.smap = (fun s -> (

let ht = (FStar_Util.smap_create default_table_size)
in (

let _42_35 = (FStar_List.iter (fun se -> (

let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))


let modules_to_sigtables = (fun mods -> (let _141_65 = (FStar_List.collect (fun _42_41 -> (match (_42_41) with
| (_42_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _141_65)))


type level =
| Expr
| Type
| Kind


let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr (_) -> begin
true
end
| _ -> begin
false
end))


let is_Type = (fun _discr_ -> (match (_discr_) with
| Type (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind (_) -> begin
true
end
| _ -> begin
false
end))


type mlift =
FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ


type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}


let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkedge"))))


type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkeffects"))))


type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mksolver_t"))))


let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _42_1 -> (match (_42_1) with
| Binding_typ (a, k) -> begin
(let _141_291 = (FStar_All.pipe_left (fun _141_290 -> FStar_Util.Inl (_141_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_141_291)::[])
end
| Binding_var (x, t) -> begin
(let _141_293 = (FStar_All.pipe_left (fun _141_292 -> FStar_Util.Inr (_141_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_141_293)::[])
end
| Binding_lid (_42_96) -> begin
[]
end
| Binding_sig (_42_99) -> begin
[]
end)))))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let new_sigtab = (fun _42_106 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _42_110 = (env.solver.push msg)
in (

let _42_112 = env
in (let _141_312 = (let _141_311 = (let _141_310 = (sigtab env)
in (FStar_Util.smap_copy _141_310))
in (_141_311)::env.sigtab)
in {solver = _42_112.solver; range = _42_112.range; curmodule = _42_112.curmodule; gamma = _42_112.gamma; modules = _42_112.modules; expected_typ = _42_112.expected_typ; level = _42_112.level; sigtab = _141_312; is_pattern = _42_112.is_pattern; instantiate_targs = _42_112.instantiate_targs; instantiate_vargs = _42_112.instantiate_vargs; effects = _42_112.effects; generalize = _42_112.generalize; letrecs = _42_112.letrecs; top_level = _42_112.top_level; check_uvars = _42_112.check_uvars; use_eq = _42_112.use_eq; is_iface = _42_112.is_iface; admit = _42_112.admit; default_effects = _42_112.default_effects}))))


let mark : env  ->  env = (fun env -> (

let _42_115 = (env.solver.mark "USER MARK")
in (

let _42_117 = env
in (let _141_317 = (let _141_316 = (let _141_315 = (sigtab env)
in (FStar_Util.smap_copy _141_315))
in (_141_316)::env.sigtab)
in {solver = _42_117.solver; range = _42_117.range; curmodule = _42_117.curmodule; gamma = _42_117.gamma; modules = _42_117.modules; expected_typ = _42_117.expected_typ; level = _42_117.level; sigtab = _141_317; is_pattern = _42_117.is_pattern; instantiate_targs = _42_117.instantiate_targs; instantiate_vargs = _42_117.instantiate_vargs; effects = _42_117.effects; generalize = _42_117.generalize; letrecs = _42_117.letrecs; top_level = _42_117.top_level; check_uvars = _42_117.check_uvars; use_eq = _42_117.use_eq; is_iface = _42_117.is_iface; admit = _42_117.admit; default_effects = _42_117.default_effects}))))


let commit_mark : env  ->  env = (fun env -> (

let _42_120 = (env.solver.commit_mark "USER MARK")
in (

let sigtab = (match (env.sigtab) with
| (hd)::(_42_124)::tl -> begin
(hd)::tl
end
| _42_129 -> begin
(failwith "Impossible")
end)
in (

let _42_131 = env
in {solver = _42_131.solver; range = _42_131.range; curmodule = _42_131.curmodule; gamma = _42_131.gamma; modules = _42_131.modules; expected_typ = _42_131.expected_typ; level = _42_131.level; sigtab = sigtab; is_pattern = _42_131.is_pattern; instantiate_targs = _42_131.instantiate_targs; instantiate_vargs = _42_131.instantiate_vargs; effects = _42_131.effects; generalize = _42_131.generalize; letrecs = _42_131.letrecs; top_level = _42_131.top_level; check_uvars = _42_131.check_uvars; use_eq = _42_131.use_eq; is_iface = _42_131.is_iface; admit = _42_131.admit; default_effects = _42_131.default_effects}))))


let reset_mark : env  ->  env = (fun env -> (

let _42_134 = (env.solver.reset_mark "USER MARK")
in (

let _42_136 = env
in (let _141_322 = (FStar_List.tl env.sigtab)
in {solver = _42_136.solver; range = _42_136.range; curmodule = _42_136.curmodule; gamma = _42_136.gamma; modules = _42_136.modules; expected_typ = _42_136.expected_typ; level = _42_136.level; sigtab = _141_322; is_pattern = _42_136.is_pattern; instantiate_targs = _42_136.instantiate_targs; instantiate_vargs = _42_136.instantiate_vargs; effects = _42_136.effects; generalize = _42_136.generalize; letrecs = _42_136.letrecs; top_level = _42_136.top_level; check_uvars = _42_136.check_uvars; use_eq = _42_136.use_eq; is_iface = _42_136.is_iface; admit = _42_136.admit; default_effects = _42_136.default_effects}))))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | ((_)::[]) -> begin
(failwith "Too many pops")
end
| (_42_146)::tl -> begin
(

let _42_148 = (env.solver.pop msg)
in (

let _42_150 = env
in {solver = _42_150.solver; range = _42_150.range; curmodule = _42_150.curmodule; gamma = _42_150.gamma; modules = _42_150.modules; expected_typ = _42_150.expected_typ; level = _42_150.level; sigtab = tl; is_pattern = _42_150.is_pattern; instantiate_targs = _42_150.instantiate_targs; instantiate_vargs = _42_150.instantiate_vargs; effects = _42_150.effects; generalize = _42_150.generalize; letrecs = _42_150.letrecs; top_level = _42_150.top_level; check_uvars = _42_150.check_uvars; use_eq = _42_150.use_eq; is_iface = _42_150.is_iface; admit = _42_150.admit; default_effects = _42_150.default_effects}))
end))


let initial_env : solver_t  ->  FStar_Ident.lident  ->  env = (fun solver module_lid -> (let _141_332 = (let _141_331 = (new_sigtab ())
in (_141_331)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _141_332; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))


let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found = (fun v -> (let _141_341 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _141_341)))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _141_348 = (let _141_347 = (let _141_346 = (name_not_found l)
in ((_141_346), ((FStar_Ident.range_of_lid l))))
in FStar_Absyn_Syntax.Error (_141_347))
in (Prims.raise _141_348))
end
| Some (md) -> begin
md
end))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _42_179 -> (match (_42_179) with
| (m1, m2, _42_174, _42_176, _42_178) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _141_404 = (let _141_403 = (let _141_402 = (let _141_401 = (FStar_Absyn_Print.sli l1)
in (let _141_400 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _141_401 _141_400)))
in ((_141_402), (env.range)))
in FStar_Absyn_Syntax.Error (_141_403))
in (Prims.raise _141_404))
end
| Some (_42_182, _42_184, m3, j1, j2) -> begin
((m3), (j1), (j2))
end)
end)


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)


let wp_sig_aux : FStar_Absyn_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _141_419 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith _141_419))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (((FStar_Util.Inl (a), _42_215))::((FStar_Util.Inl (wp), _42_210))::((FStar_Util.Inl (wlp), _42_205))::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _42_225; FStar_Absyn_Syntax.pos = _42_223; FStar_Absyn_Syntax.fvs = _42_221; FStar_Absyn_Syntax.uvs = _42_219}) -> begin
((a), (wp.FStar_Absyn_Syntax.sort))
end
| _42_231 -> begin
(failwith "Impossible")
end)
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))


let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _42_238 -> (match (_42_238) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))


let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _42_243, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _42_2 -> (match (_42_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _42_253 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(

let _42_257 = env
in {solver = _42_257.solver; range = _42_257.range; curmodule = _42_257.curmodule; gamma = _42_257.gamma; modules = _42_257.modules; expected_typ = _42_257.expected_typ; level = _42_257.level; sigtab = _42_257.sigtab; is_pattern = _42_257.is_pattern; instantiate_targs = _42_257.instantiate_targs; instantiate_vargs = _42_257.instantiate_vargs; effects = _42_257.effects; generalize = _42_257.generalize; letrecs = _42_257.letrecs; top_level = _42_257.top_level; check_uvars = _42_257.check_uvars; use_eq = _42_257.use_eq; is_iface = _42_257.is_iface; admit = _42_257.admit; default_effects = (((e), (l)))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _42_261) -> begin
(

let effects = (

let _42_264 = env.effects
in {decls = (ne)::env.effects.decls; order = _42_264.order; joins = _42_264.joins})
in (

let _42_267 = env
in {solver = _42_267.solver; range = _42_267.range; curmodule = _42_267.curmodule; gamma = _42_267.gamma; modules = _42_267.modules; expected_typ = _42_267.expected_typ; level = _42_267.level; sigtab = _42_267.sigtab; is_pattern = _42_267.is_pattern; instantiate_targs = _42_267.instantiate_targs; instantiate_vargs = _42_267.instantiate_vargs; effects = effects; generalize = _42_267.generalize; letrecs = _42_267.letrecs; top_level = _42_267.top_level; check_uvars = _42_267.check_uvars; use_eq = _42_267.use_eq; is_iface = _42_267.is_iface; admit = _42_267.admit; default_effects = _42_267.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _42_271) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _141_440 = (e1.mlift r wp1)
in (e2.mlift r _141_440)))})
in (

let mk_lift = (fun lift_t r wp1 -> (let _141_451 = (let _141_450 = (let _141_449 = (FStar_Absyn_Syntax.targ r)
in (let _141_448 = (let _141_447 = (FStar_Absyn_Syntax.targ wp1)
in (_141_447)::[])
in (_141_449)::_141_448))
in ((lift_t), (_141_450)))
in (FStar_Absyn_Syntax.mk_Typ_app _141_451 None wp1.FStar_Absyn_Syntax.pos)))
in (

let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _141_468 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _141_468 FStar_Absyn_Syntax.mk_Kind_type))
in (

let wp = (let _141_469 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _141_469 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _141_470 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _141_470)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (

let find_edge = (fun order _42_299 -> (match (_42_299) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _141_476 -> Some (_141_476)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _141_484 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _141_483 = (find_edge order ((i), (k)))
in (let _141_482 = (find_edge order ((k), (j)))
in ((_141_483), (_141_482))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _42_311 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _141_484))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _141_492 = (find_edge order ((i), (k)))
in (let _141_491 = (find_edge order ((j), (k)))
in ((_141_492), (_141_491))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _42_328, _42_330) -> begin
if ((let _141_493 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _141_493)) && (not ((let _141_494 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _141_494))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _42_334 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let _42_343 = env.effects
in {decls = _42_343.decls; order = order; joins = joins})
in (

let _42_346 = env
in {solver = _42_346.solver; range = _42_346.range; curmodule = _42_346.curmodule; gamma = _42_346.gamma; modules = _42_346.modules; expected_typ = _42_346.expected_typ; level = _42_346.level; sigtab = _42_346.sigtab; is_pattern = _42_346.is_pattern; instantiate_targs = _42_346.instantiate_targs; instantiate_vargs = _42_346.instantiate_vargs; effects = effects; generalize = _42_346.generalize; letrecs = _42_346.letrecs; top_level = _42_346.top_level; check_uvars = _42_346.check_uvars; use_eq = _42_346.use_eq; is_iface = _42_346.is_iface; admit = _42_346.admit; default_effects = _42_346.default_effects})))))))))))))
end
| _42_349 -> begin
env
end))


let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _42_354, _42_356, _42_358) -> begin
(add_sigelts env ses)
end
| _42_362 -> begin
(

let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _141_502 = (sigtab env)
in (FStar_Util.smap_add _141_502 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let empty_lid : FStar_Absyn_Syntax.lident = (let _141_506 = (let _141_505 = (FStar_Absyn_Syntax.id_of_text "")
in (_141_505)::[])
in (FStar_Absyn_Syntax.lid_of_ids _141_506))


let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _42_3 -> (match (_42_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _42_373 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (

let _42_375 = (add_sigelts env sigs)
in (

let _42_377 = env
in {solver = _42_377.solver; range = _42_377.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _42_377.expected_typ; level = _42_377.level; sigtab = _42_377.sigtab; is_pattern = _42_377.is_pattern; instantiate_targs = _42_377.instantiate_targs; instantiate_vargs = _42_377.instantiate_vargs; effects = _42_377.effects; generalize = _42_377.generalize; letrecs = _42_377.letrecs; top_level = _42_377.top_level; check_uvars = _42_377.check_uvars; use_eq = _42_377.use_eq; is_iface = _42_377.is_iface; admit = _42_377.admit; default_effects = _42_377.default_effects}))))


let set_level : env  ->  level  ->  env = (fun env level -> (

let _42_381 = env
in {solver = _42_381.solver; range = _42_381.range; curmodule = _42_381.curmodule; gamma = _42_381.gamma; modules = _42_381.modules; expected_typ = _42_381.expected_typ; level = level; sigtab = _42_381.sigtab; is_pattern = _42_381.is_pattern; instantiate_targs = _42_381.instantiate_targs; instantiate_vargs = _42_381.instantiate_vargs; effects = _42_381.effects; generalize = _42_381.generalize; letrecs = _42_381.letrecs; top_level = _42_381.top_level; check_uvars = _42_381.check_uvars; use_eq = _42_381.use_eq; is_iface = _42_381.is_iface; admit = _42_381.admit; default_effects = _42_381.default_effects}))


let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))


let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _42_389 = env
in {solver = _42_389.solver; range = _42_389.range; curmodule = lid; gamma = _42_389.gamma; modules = _42_389.modules; expected_typ = _42_389.expected_typ; level = _42_389.level; sigtab = _42_389.sigtab; is_pattern = _42_389.is_pattern; instantiate_targs = _42_389.instantiate_targs; instantiate_vargs = _42_389.instantiate_vargs; effects = _42_389.effects; generalize = _42_389.generalize; letrecs = _42_389.letrecs; top_level = _42_389.top_level; check_uvars = _42_389.check_uvars; use_eq = _42_389.use_eq; is_iface = _42_389.is_iface; admit = _42_389.admit; default_effects = _42_389.default_effects}))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(

let _42_393 = e
in {solver = _42_393.solver; range = r; curmodule = _42_393.curmodule; gamma = _42_393.gamma; modules = _42_393.modules; expected_typ = _42_393.expected_typ; level = _42_393.level; sigtab = _42_393.sigtab; is_pattern = _42_393.is_pattern; instantiate_targs = _42_393.instantiate_targs; instantiate_vargs = _42_393.instantiate_vargs; effects = _42_393.effects; generalize = _42_393.generalize; letrecs = _42_393.letrecs; top_level = _42_393.top_level; check_uvars = _42_393.check_uvars; use_eq = _42_393.use_eq; is_iface = _42_393.is_iface; admit = _42_393.admit; default_effects = _42_393.default_effects})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _141_538 = (sigtab env)
in (FStar_Util.smap_try_find _141_538 (FStar_Ident.text_of_lid lid))))


let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _42_4 -> (match (_42_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _42_406 -> begin
None
end))))


let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _141_550 = (let _141_549 = (let _141_548 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in ((_141_548), ((FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v))))
in FStar_Absyn_Syntax.Error (_141_549))
in (Prims.raise _141_550))
end
| Some (t) -> begin
t
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
true
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l -> (match (((c), (l))) with
| ([], _42_422) -> begin
true
end
| (_42_425, []) -> begin
false
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _42_436 -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))


let lookup_qname : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.sigelt) FStar_Util.either Prims.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let found = if cur_mod then begin
(FStar_Util.find_map env.gamma (fun _42_5 -> (match (_42_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _42_447, _42_449, _42_451)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _141_565 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _141_565 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
Some (FStar_Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(

let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr (s))
end else begin
None
end)
end
| _42_460 -> begin
None
end)))
end else begin
None
end
in if (FStar_Util.is_some found) then begin
found
end else begin
if ((not (cur_mod)) || (has_interface env env.curmodule)) then begin
(match ((find_in_sigtab env lid)) with
| Some (se) -> begin
Some (FStar_Util.Inr (se))
end
| None -> begin
None
end)
end else begin
None
end
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_42_468, t, (_42_471, tps, _42_474), _42_477, _42_479, _42_481))) -> begin
(let _141_571 = (FStar_List.map (fun _42_489 -> (match (_42_489) with
| (x, _42_488) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _141_571 t))
end
| _42_491 -> begin
(let _141_574 = (let _141_573 = (let _141_572 = (name_not_found lid)
in ((_141_572), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_141_573))
in (Prims.raise _141_574))
end))


let lookup_kind_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _42_498))) -> begin
((l), (binders), (k))
end
| _42_504 -> begin
(let _141_581 = (let _141_580 = (let _141_579 = (name_not_found lid)
in ((_141_579), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_141_580))
in (Prims.raise _141_581))
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _42_509 -> (match (()) with
| () -> begin
(let _141_592 = (let _141_591 = (FStar_Util.string_of_int i)
in (let _141_590 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _141_591 _141_590)))
in (failwith _141_592))
end))
in (

let t = (lookup_datacon env lid)
in (match ((let _141_593 = (FStar_Absyn_Util.compress_typ t)
in _141_593.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _42_513) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _141_594 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _141_594 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _141_595 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _141_595 Prims.fst))
end))
end
end
| _42_522 -> begin
(fail ())
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_42_526, t, q, _42_530))) -> begin
Some (((t), (q)))
end
| _42_536 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_42_540, t, _42_543, _42_545))) -> begin
t
end
| _42_551 -> begin
(let _141_606 = (let _141_605 = (let _141_604 = (name_not_found lid)
in ((_141_604), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_141_605))
in (Prims.raise _141_606))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (

let not_found = (fun _42_555 -> (match (()) with
| () -> begin
(let _141_615 = (let _141_614 = (let _141_613 = (name_not_found lid)
in ((_141_613), ((FStar_Ident.range_of_lid lid))))
in FStar_Absyn_Syntax.Error (_141_614))
in (Prims.raise _141_615))
end))
in (

let mapper = (fun _42_6 -> (match (_42_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_42_558, t, (_42_561, tps, _42_564), _42_567, _42_569, _42_571)) -> begin
(let _141_620 = (let _141_619 = (FStar_List.map (fun _42_578 -> (match (_42_578) with
| (x, _42_577) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _141_619 t))
in Some (_141_620))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _42_585)) -> begin
if (in_cur_mod env l) then begin
if ((FStar_All.pipe_right qs (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.is_iface) then begin
Some (t)
end else begin
None
end
end else begin
Some (t)
end
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_42_590, ({FStar_Absyn_Syntax.lbname = _42_597; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _42_594; FStar_Absyn_Syntax.lbdef = _42_592})::[]), _42_602, _42_604, _42_606)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_42_611, lbs), _42_615, _42_617, _42_619)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_42_625) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (lid') -> begin
if (FStar_Ident.lid_equals lid lid') then begin
Some (lb.FStar_Absyn_Syntax.lbtyp)
end else begin
None
end
end)))
end
| t -> begin
None
end))
in (match ((let _141_622 = (lookup_qname env lid)
in (FStar_Util.bind_opt _141_622 mapper))) with
| Some (t) -> begin
(

let _42_633 = t
in (let _141_623 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _42_633.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _42_633.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _141_623; FStar_Absyn_Syntax.fvs = _42_633.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _42_633.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_42_639, _42_641, quals, _42_644))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_7 -> (match (_42_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _42_652 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_42_654, t, _42_657, _42_659, _42_661, _42_663))) -> begin
true
end
| _42_669 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_42_673, _42_675, _42_677, _42_679, _42_681, tags, _42_684))) -> begin
(FStar_Util.for_some (fun _42_8 -> (match (_42_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _42_697 -> begin
false
end)) tags)
end
| _42_699 -> begin
false
end))


let lookup_datacons_of_typ : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_42_703, _42_705, _42_707, _42_709, datas, _42_712, _42_714))) -> begin
(let _141_640 = (FStar_List.map (fun l -> (let _141_639 = (lookup_lid env l)
in ((l), (_141_639)))) datas)
in Some (_141_640))
end
| _42_721 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _42_729))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_9 -> (match (_42_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _42_737 -> begin
false
end)))) then begin
None
end else begin
Some (((binders), (c)))
end
end
| _42_739 -> begin
None
end))


let lookup_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _42_745, t, quals, _42_749))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _42_10 -> (match (_42_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _42_757 -> begin
false
end)))) then begin
None
end else begin
(

let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _141_651 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (lid)))))
in Some (_141_651)))
end
end
| _42_760 -> begin
None
end))


let lookup_opaque_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _42_766, t, quals, _42_770))) -> begin
(

let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _141_656 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (lid)))))
in Some (_141_656)))
end
| _42_777 -> begin
None
end))


let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _42_11 -> (match (_42_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _42_786 -> begin
None
end))))


let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _141_668 = (let _141_667 = (let _141_666 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in ((_141_666), ((FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v))))
in FStar_Absyn_Syntax.Error (_141_667))
in (Prims.raise _141_668))
end
| Some (k) -> begin
k
end))


let lookup_typ_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _42_820 -> begin
(let _141_675 = (let _141_674 = (let _141_673 = (name_not_found ftv)
in ((_141_673), ((FStar_Ident.range_of_lid ftv))))
in FStar_Absyn_Syntax.Error (_141_674))
in (Prims.raise _141_675))
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _42_12 -> (match (_42_12) with
| FStar_Absyn_Syntax.Projector (_42_852) -> begin
true
end
| _42_855 -> begin
false
end)) quals)
end
| _42_857 -> begin
false
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _42_862))) -> begin
(let _141_686 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _141_686 (fun _141_685 -> Some (_141_685))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _42_870, _42_872, _42_874))) -> begin
(let _141_688 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _141_688 (fun _141_687 -> Some (_141_687))))
end
| _42_880 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _141_695 = (let _141_694 = (let _141_693 = (name_not_found ftv)
in ((_141_693), ((FStar_Ident.range_of_lid ftv))))
in FStar_Absyn_Syntax.Error (_141_694))
in (Prims.raise _141_695))
end
| Some (k) -> begin
k
end))


let lookup_operator : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ = (fun env opname -> (

let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (build_lattice (

let _42_891 = env
in {solver = _42_891.solver; range = _42_891.range; curmodule = _42_891.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _42_891.modules; expected_typ = _42_891.expected_typ; level = _42_891.level; sigtab = _42_891.sigtab; is_pattern = _42_891.is_pattern; instantiate_targs = _42_891.instantiate_targs; instantiate_vargs = _42_891.instantiate_vargs; effects = _42_891.effects; generalize = _42_891.generalize; letrecs = _42_891.letrecs; top_level = _42_891.top_level; check_uvars = _42_891.check_uvars; use_eq = _42_891.use_eq; is_iface = _42_891.is_iface; admit = _42_891.admit; default_effects = _42_891.default_effects}) s))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _42_895 = env
in {solver = _42_895.solver; range = _42_895.range; curmodule = _42_895.curmodule; gamma = (b)::env.gamma; modules = _42_895.modules; expected_typ = _42_895.expected_typ; level = _42_895.level; sigtab = _42_895.sigtab; is_pattern = _42_895.is_pattern; instantiate_targs = _42_895.instantiate_targs; instantiate_vargs = _42_895.instantiate_vargs; effects = _42_895.effects; generalize = _42_895.generalize; letrecs = _42_895.letrecs; top_level = _42_895.top_level; check_uvars = _42_895.check_uvars; use_eq = _42_895.use_eq; is_iface = _42_895.is_iface; admit = _42_895.admit; default_effects = _42_895.default_effects}))


let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (

let no_uvs = (let _141_712 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _141_711 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _141_710 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _141_712; FStar_Absyn_Syntax.uvars_t = _141_711; FStar_Absyn_Syntax.uvars_e = _141_710})))
in (

let ext = (fun out uvs -> (

let _42_902 = out
in (let _141_719 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _141_718 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _141_717 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _141_719; FStar_Absyn_Syntax.uvars_t = _141_718; FStar_Absyn_Syntax.uvars_e = _141_717})))))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| ((Binding_lid (_, t))::tl) | ((Binding_var (_, t))::tl) -> begin
(let _141_725 = (let _141_724 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _141_724))
in (aux _141_725 tl))
end
| (Binding_typ (_42_922, k))::tl -> begin
(let _141_727 = (let _141_726 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _141_726))
in (aux _141_727 tl))
end
| (Binding_sig (_42_930))::_42_928 -> begin
out
end))
in (aux no_uvs env.gamma)))))


let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (

let _42_935 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (

let _42_937 = env
in {solver = _42_937.solver; range = _42_937.range; curmodule = _42_937.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _42_937.level; sigtab = _42_937.sigtab; is_pattern = _42_937.is_pattern; instantiate_targs = _42_937.instantiate_targs; instantiate_vargs = _42_937.instantiate_vargs; effects = _42_937.effects; generalize = _42_937.generalize; letrecs = _42_937.letrecs; top_level = _42_937.top_level; check_uvars = _42_937.check_uvars; use_eq = _42_937.use_eq; is_iface = _42_937.is_iface; admit = _42_937.admit; default_effects = _42_937.default_effects})))


let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _42_962; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _42_958; FStar_Absyn_Syntax.pos = _42_956; FStar_Absyn_Syntax.fvs = _42_954; FStar_Absyn_Syntax.uvs = _42_952}; FStar_Absyn_Syntax.p = _42_950}); FStar_Absyn_Syntax.tk = _42_948; FStar_Absyn_Syntax.pos = _42_946; FStar_Absyn_Syntax.fvs = _42_944; FStar_Absyn_Syntax.uvs = _42_942} -> begin
(let _141_737 = (let _141_736 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _141_736))
in (failwith _141_737))
end
| _42_967 -> begin
(

let _42_968 = env
in {solver = _42_968.solver; range = _42_968.range; curmodule = _42_968.curmodule; gamma = _42_968.gamma; modules = _42_968.modules; expected_typ = Some (t); level = _42_968.level; sigtab = _42_968.sigtab; is_pattern = _42_968.is_pattern; instantiate_targs = _42_968.instantiate_targs; instantiate_vargs = _42_968.instantiate_vargs; effects = _42_968.effects; generalize = _42_968.generalize; letrecs = _42_968.letrecs; top_level = _42_968.top_level; check_uvars = _42_968.check_uvars; use_eq = false; is_iface = _42_968.is_iface; admit = _42_968.admit; default_effects = _42_968.default_effects})
end))


let expected_typ : env  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _141_742 = (expected_typ env)
in (((

let _42_975 = env
in {solver = _42_975.solver; range = _42_975.range; curmodule = _42_975.curmodule; gamma = _42_975.gamma; modules = _42_975.modules; expected_typ = None; level = _42_975.level; sigtab = _42_975.sigtab; is_pattern = _42_975.is_pattern; instantiate_targs = _42_975.instantiate_targs; instantiate_vargs = _42_975.instantiate_vargs; effects = _42_975.effects; generalize = _42_975.generalize; letrecs = _42_975.letrecs; top_level = _42_975.top_level; check_uvars = _42_975.check_uvars; use_eq = false; is_iface = _42_975.is_iface; admit = _42_975.admit; default_effects = _42_975.default_effects})), (_141_742))))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let binding_of_binder : FStar_Absyn_Syntax.binder  ->  binding = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ (((a.FStar_Absyn_Syntax.v), (a.FStar_Absyn_Syntax.sort)))
end
| FStar_Util.Inr (x) -> begin
Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))
end))


let binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _141_760 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_141_760)::out)
end
| Binding_typ (a, k) -> begin
(let _141_761 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_141_761)::out)
end
| _42_999 -> begin
out
end)) [] env.gamma))


let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_42_1004) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _141_766 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_141_766)::out)
end
| _42_1011 -> begin
out
end)) [] env.gamma))


let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _141_770 = (let _141_769 = (binders env)
in (FStar_All.pipe_right _141_769 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _141_770)))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _42_13 -> (match (_42_13) with
| Binding_sig (s) -> begin
(let _141_775 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _141_775 keys))
end
| _42_1019 -> begin
keys
end)) [] env.gamma)
in (let _141_780 = (sigtab env)
in (FStar_Util.smap_fold _141_780 (fun _42_1021 v keys -> (let _141_779 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _141_779 keys))) keys))))




