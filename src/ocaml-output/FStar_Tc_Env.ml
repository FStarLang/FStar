
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
| Binding_var (_43_3) -> begin
_43_3
end))


let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_43_6) -> begin
_43_6
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_43_9) -> begin
_43_9
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_43_12) -> begin
_43_12
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

let _43_22 = (FStar_List.iter (fun se -> (

let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))


let modules_to_sigtables = (fun mods -> (let _144_65 = (FStar_List.collect (fun _43_28 -> (match (_43_28) with
| (_43_26, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _144_65)))


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


let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___102 -> (match (uu___102) with
| Binding_typ (a, k) -> begin
(let _144_291 = (FStar_All.pipe_left (fun _144_290 -> FStar_Util.Inl (_144_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_144_291)::[])
end
| Binding_var (x, t) -> begin
(let _144_293 = (FStar_All.pipe_left (fun _144_292 -> FStar_Util.Inr (_144_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_144_293)::[])
end
| Binding_lid (_43_83) -> begin
[]
end
| Binding_sig (_43_86) -> begin
[]
end)))))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let new_sigtab = (fun _43_93 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _43_97 = (env.solver.push msg)
in (

let _43_99 = env
in (let _144_312 = (let _144_311 = (let _144_310 = (sigtab env)
in (FStar_Util.smap_copy _144_310))
in (_144_311)::env.sigtab)
in {solver = _43_99.solver; range = _43_99.range; curmodule = _43_99.curmodule; gamma = _43_99.gamma; modules = _43_99.modules; expected_typ = _43_99.expected_typ; level = _43_99.level; sigtab = _144_312; is_pattern = _43_99.is_pattern; instantiate_targs = _43_99.instantiate_targs; instantiate_vargs = _43_99.instantiate_vargs; effects = _43_99.effects; generalize = _43_99.generalize; letrecs = _43_99.letrecs; top_level = _43_99.top_level; check_uvars = _43_99.check_uvars; use_eq = _43_99.use_eq; is_iface = _43_99.is_iface; admit = _43_99.admit; default_effects = _43_99.default_effects}))))


let mark : env  ->  env = (fun env -> (

let _43_102 = (env.solver.mark "USER MARK")
in (

let _43_104 = env
in (let _144_317 = (let _144_316 = (let _144_315 = (sigtab env)
in (FStar_Util.smap_copy _144_315))
in (_144_316)::env.sigtab)
in {solver = _43_104.solver; range = _43_104.range; curmodule = _43_104.curmodule; gamma = _43_104.gamma; modules = _43_104.modules; expected_typ = _43_104.expected_typ; level = _43_104.level; sigtab = _144_317; is_pattern = _43_104.is_pattern; instantiate_targs = _43_104.instantiate_targs; instantiate_vargs = _43_104.instantiate_vargs; effects = _43_104.effects; generalize = _43_104.generalize; letrecs = _43_104.letrecs; top_level = _43_104.top_level; check_uvars = _43_104.check_uvars; use_eq = _43_104.use_eq; is_iface = _43_104.is_iface; admit = _43_104.admit; default_effects = _43_104.default_effects}))))


let commit_mark : env  ->  env = (fun env -> (

let _43_107 = (env.solver.commit_mark "USER MARK")
in (

let sigtab = (match (env.sigtab) with
| (hd)::(_43_111)::tl -> begin
(hd)::tl
end
| _43_116 -> begin
(failwith "Impossible")
end)
in (

let _43_118 = env
in {solver = _43_118.solver; range = _43_118.range; curmodule = _43_118.curmodule; gamma = _43_118.gamma; modules = _43_118.modules; expected_typ = _43_118.expected_typ; level = _43_118.level; sigtab = sigtab; is_pattern = _43_118.is_pattern; instantiate_targs = _43_118.instantiate_targs; instantiate_vargs = _43_118.instantiate_vargs; effects = _43_118.effects; generalize = _43_118.generalize; letrecs = _43_118.letrecs; top_level = _43_118.top_level; check_uvars = _43_118.check_uvars; use_eq = _43_118.use_eq; is_iface = _43_118.is_iface; admit = _43_118.admit; default_effects = _43_118.default_effects}))))


let reset_mark : env  ->  env = (fun env -> (

let _43_121 = (env.solver.reset_mark "USER MARK")
in (

let _43_123 = env
in (let _144_322 = (FStar_List.tl env.sigtab)
in {solver = _43_123.solver; range = _43_123.range; curmodule = _43_123.curmodule; gamma = _43_123.gamma; modules = _43_123.modules; expected_typ = _43_123.expected_typ; level = _43_123.level; sigtab = _144_322; is_pattern = _43_123.is_pattern; instantiate_targs = _43_123.instantiate_targs; instantiate_vargs = _43_123.instantiate_vargs; effects = _43_123.effects; generalize = _43_123.generalize; letrecs = _43_123.letrecs; top_level = _43_123.top_level; check_uvars = _43_123.check_uvars; use_eq = _43_123.use_eq; is_iface = _43_123.is_iface; admit = _43_123.admit; default_effects = _43_123.default_effects}))))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | ((_)::[]) -> begin
(failwith "Too many pops")
end
| (_43_133)::tl -> begin
(

let _43_135 = (env.solver.pop msg)
in (

let _43_137 = env
in {solver = _43_137.solver; range = _43_137.range; curmodule = _43_137.curmodule; gamma = _43_137.gamma; modules = _43_137.modules; expected_typ = _43_137.expected_typ; level = _43_137.level; sigtab = tl; is_pattern = _43_137.is_pattern; instantiate_targs = _43_137.instantiate_targs; instantiate_vargs = _43_137.instantiate_vargs; effects = _43_137.effects; generalize = _43_137.generalize; letrecs = _43_137.letrecs; top_level = _43_137.top_level; check_uvars = _43_137.check_uvars; use_eq = _43_137.use_eq; is_iface = _43_137.is_iface; admit = _43_137.admit; default_effects = _43_137.default_effects}))
end))


let initial_env : solver_t  ->  FStar_Ident.lident  ->  env = (fun solver module_lid -> (let _144_332 = (let _144_331 = (new_sigtab ())
in (_144_331)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _144_332; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))


let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found = (fun v -> (let _144_341 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _144_341)))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _144_348 = (let _144_347 = (let _144_346 = (name_not_found l)
in ((_144_346), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (_144_347))
in (Prims.raise _144_348))
end
| Some (md) -> begin
md
end))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
((l1), ((fun t wp -> wp)), ((fun t wp -> wp)))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _43_166 -> (match (_43_166) with
| (m1, m2, _43_161, _43_163, _43_165) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _144_404 = (let _144_403 = (let _144_402 = (let _144_401 = (FStar_Absyn_Print.sli l1)
in (let _144_400 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _144_401 _144_400)))
in ((_144_402), (env.range)))
in FStar_Errors.Error (_144_403))
in (Prims.raise _144_404))
end
| Some (_43_169, _43_171, m3, j1, j2) -> begin
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
(let _144_419 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith _144_419))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (((FStar_Util.Inl (a), _43_202))::((FStar_Util.Inl (wp), _43_197))::((FStar_Util.Inl (wlp), _43_192))::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _43_212; FStar_Absyn_Syntax.pos = _43_210; FStar_Absyn_Syntax.fvs = _43_208; FStar_Absyn_Syntax.uvs = _43_206}) -> begin
((a), (wp.FStar_Absyn_Syntax.sort))
end
| _43_218 -> begin
(failwith "Impossible")
end)
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))


let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _43_225 -> (match (_43_225) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))


let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _43_230, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun uu___103 -> (match (uu___103) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _43_240 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(

let _43_244 = env
in {solver = _43_244.solver; range = _43_244.range; curmodule = _43_244.curmodule; gamma = _43_244.gamma; modules = _43_244.modules; expected_typ = _43_244.expected_typ; level = _43_244.level; sigtab = _43_244.sigtab; is_pattern = _43_244.is_pattern; instantiate_targs = _43_244.instantiate_targs; instantiate_vargs = _43_244.instantiate_vargs; effects = _43_244.effects; generalize = _43_244.generalize; letrecs = _43_244.letrecs; top_level = _43_244.top_level; check_uvars = _43_244.check_uvars; use_eq = _43_244.use_eq; is_iface = _43_244.is_iface; admit = _43_244.admit; default_effects = (((e), (l)))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _43_248) -> begin
(

let effects = (

let _43_251 = env.effects
in {decls = (ne)::env.effects.decls; order = _43_251.order; joins = _43_251.joins})
in (

let _43_254 = env
in {solver = _43_254.solver; range = _43_254.range; curmodule = _43_254.curmodule; gamma = _43_254.gamma; modules = _43_254.modules; expected_typ = _43_254.expected_typ; level = _43_254.level; sigtab = _43_254.sigtab; is_pattern = _43_254.is_pattern; instantiate_targs = _43_254.instantiate_targs; instantiate_vargs = _43_254.instantiate_vargs; effects = effects; generalize = _43_254.generalize; letrecs = _43_254.letrecs; top_level = _43_254.top_level; check_uvars = _43_254.check_uvars; use_eq = _43_254.use_eq; is_iface = _43_254.is_iface; admit = _43_254.admit; default_effects = _43_254.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _43_258) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _144_440 = (e1.mlift r wp1)
in (e2.mlift r _144_440)))})
in (

let mk_lift = (fun lift_t r wp1 -> (let _144_451 = (let _144_450 = (let _144_449 = (FStar_Absyn_Syntax.targ r)
in (let _144_448 = (let _144_447 = (FStar_Absyn_Syntax.targ wp1)
in (_144_447)::[])
in (_144_449)::_144_448))
in ((lift_t), (_144_450)))
in (FStar_Absyn_Syntax.mk_Typ_app _144_451 None wp1.FStar_Absyn_Syntax.pos)))
in (

let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _144_468 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _144_468 FStar_Absyn_Syntax.mk_Kind_type))
in (

let wp = (let _144_469 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _144_469 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _144_470 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _144_470)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (

let find_edge = (fun order _43_286 -> (match (_43_286) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _144_476 -> Some (_144_476)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _144_484 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _144_483 = (find_edge order ((i), (k)))
in (let _144_482 = (find_edge order ((k), (j)))
in ((_144_483), (_144_482))))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _43_298 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _144_484))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _144_492 = (find_edge order ((i), (k)))
in (let _144_491 = (find_edge order ((j), (k)))
in ((_144_492), (_144_491))))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some (((k), (ik), (jk)))
end
| Some (ub, _43_315, _43_317) -> begin
if ((let _144_493 = (find_edge order ((k), (ub)))
in (FStar_Util.is_some _144_493)) && (not ((let _144_494 = (find_edge order ((ub), (k)))
in (FStar_Util.is_some _144_494))))) then begin
Some (((k), (ik), (jk)))
end else begin
bopt
end
end)
end
| _43_321 -> begin
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

let _43_330 = env.effects
in {decls = _43_330.decls; order = order; joins = joins})
in (

let _43_333 = env
in {solver = _43_333.solver; range = _43_333.range; curmodule = _43_333.curmodule; gamma = _43_333.gamma; modules = _43_333.modules; expected_typ = _43_333.expected_typ; level = _43_333.level; sigtab = _43_333.sigtab; is_pattern = _43_333.is_pattern; instantiate_targs = _43_333.instantiate_targs; instantiate_vargs = _43_333.instantiate_vargs; effects = effects; generalize = _43_333.generalize; letrecs = _43_333.letrecs; top_level = _43_333.top_level; check_uvars = _43_333.check_uvars; use_eq = _43_333.use_eq; is_iface = _43_333.is_iface; admit = _43_333.admit; default_effects = _43_333.default_effects})))))))))))))
end
| _43_336 -> begin
env
end))


let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _43_341, _43_343, _43_345) -> begin
(add_sigelts env ses)
end
| _43_349 -> begin
(

let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _144_502 = (sigtab env)
in (FStar_Util.smap_add _144_502 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let empty_lid : FStar_Absyn_Syntax.lident = (let _144_506 = (let _144_505 = (FStar_Absyn_Syntax.id_of_text "")
in (_144_505)::[])
in (FStar_Absyn_Syntax.lid_of_ids _144_506))


let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___104 -> (match (uu___104) with
| Binding_sig (se) -> begin
(se)::[]
end
| _43_360 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (

let _43_362 = (add_sigelts env sigs)
in (

let _43_364 = env
in {solver = _43_364.solver; range = _43_364.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _43_364.expected_typ; level = _43_364.level; sigtab = _43_364.sigtab; is_pattern = _43_364.is_pattern; instantiate_targs = _43_364.instantiate_targs; instantiate_vargs = _43_364.instantiate_vargs; effects = _43_364.effects; generalize = _43_364.generalize; letrecs = _43_364.letrecs; top_level = _43_364.top_level; check_uvars = _43_364.check_uvars; use_eq = _43_364.use_eq; is_iface = _43_364.is_iface; admit = _43_364.admit; default_effects = _43_364.default_effects}))))


let set_level : env  ->  level  ->  env = (fun env level -> (

let _43_368 = env
in {solver = _43_368.solver; range = _43_368.range; curmodule = _43_368.curmodule; gamma = _43_368.gamma; modules = _43_368.modules; expected_typ = _43_368.expected_typ; level = level; sigtab = _43_368.sigtab; is_pattern = _43_368.is_pattern; instantiate_targs = _43_368.instantiate_targs; instantiate_vargs = _43_368.instantiate_vargs; effects = _43_368.effects; generalize = _43_368.generalize; letrecs = _43_368.letrecs; top_level = _43_368.top_level; check_uvars = _43_368.check_uvars; use_eq = _43_368.use_eq; is_iface = _43_368.is_iface; admit = _43_368.admit; default_effects = _43_368.default_effects}))


let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))


let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _43_376 = env
in {solver = _43_376.solver; range = _43_376.range; curmodule = lid; gamma = _43_376.gamma; modules = _43_376.modules; expected_typ = _43_376.expected_typ; level = _43_376.level; sigtab = _43_376.sigtab; is_pattern = _43_376.is_pattern; instantiate_targs = _43_376.instantiate_targs; instantiate_vargs = _43_376.instantiate_vargs; effects = _43_376.effects; generalize = _43_376.generalize; letrecs = _43_376.letrecs; top_level = _43_376.top_level; check_uvars = _43_376.check_uvars; use_eq = _43_376.use_eq; is_iface = _43_376.is_iface; admit = _43_376.admit; default_effects = _43_376.default_effects}))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(

let _43_380 = e
in {solver = _43_380.solver; range = r; curmodule = _43_380.curmodule; gamma = _43_380.gamma; modules = _43_380.modules; expected_typ = _43_380.expected_typ; level = _43_380.level; sigtab = _43_380.sigtab; is_pattern = _43_380.is_pattern; instantiate_targs = _43_380.instantiate_targs; instantiate_vargs = _43_380.instantiate_vargs; effects = _43_380.effects; generalize = _43_380.generalize; letrecs = _43_380.letrecs; top_level = _43_380.top_level; check_uvars = _43_380.check_uvars; use_eq = _43_380.use_eq; is_iface = _43_380.is_iface; admit = _43_380.admit; default_effects = _43_380.default_effects})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _144_538 = (sigtab env)
in (FStar_Util.smap_try_find _144_538 (FStar_Ident.text_of_lid lid))))


let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun uu___105 -> (match (uu___105) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _43_393 -> begin
None
end))))


let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _144_550 = (let _144_549 = (let _144_548 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in ((_144_548), ((FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v))))
in FStar_Errors.Error (_144_549))
in (Prims.raise _144_550))
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
| ([], _43_409) -> begin
true
end
| (_43_412, []) -> begin
false
end
| ((hd)::tl, (hd')::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _43_423 -> begin
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
(FStar_Util.find_map env.gamma (fun uu___106 -> (match (uu___106) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _43_434, _43_436, _43_438)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _144_565 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _144_565 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
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
| _43_447 -> begin
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
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_43_455, t, (_43_458, tps, _43_461), _43_464, _43_466, _43_468))) -> begin
(let _144_571 = (FStar_List.map (fun _43_476 -> (match (_43_476) with
| (x, _43_475) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _144_571 t))
end
| _43_478 -> begin
(let _144_574 = (let _144_573 = (let _144_572 = (name_not_found lid)
in ((_144_572), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_144_573))
in (Prims.raise _144_574))
end))


let lookup_kind_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _43_485))) -> begin
((l), (binders), (k))
end
| _43_491 -> begin
(let _144_581 = (let _144_580 = (let _144_579 = (name_not_found lid)
in ((_144_579), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_144_580))
in (Prims.raise _144_581))
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _43_496 -> (match (()) with
| () -> begin
(let _144_592 = (let _144_591 = (FStar_Util.string_of_int i)
in (let _144_590 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _144_591 _144_590)))
in (failwith _144_592))
end))
in (

let t = (lookup_datacon env lid)
in (match ((let _144_593 = (FStar_Absyn_Util.compress_typ t)
in _144_593.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _43_500) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _144_594 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _144_594 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _144_595 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _144_595 Prims.fst))
end))
end
end
| _43_509 -> begin
(fail ())
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_43_513, t, q, _43_517))) -> begin
Some (((t), (q)))
end
| _43_523 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_43_527, t, _43_530, _43_532))) -> begin
t
end
| _43_538 -> begin
(let _144_606 = (let _144_605 = (let _144_604 = (name_not_found lid)
in ((_144_604), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_144_605))
in (Prims.raise _144_606))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (

let not_found = (fun _43_542 -> (match (()) with
| () -> begin
(let _144_615 = (let _144_614 = (let _144_613 = (name_not_found lid)
in ((_144_613), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (_144_614))
in (Prims.raise _144_615))
end))
in (

let mapper = (fun uu___107 -> (match (uu___107) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_43_545, t, (_43_548, tps, _43_551), _43_554, _43_556, _43_558)) -> begin
(let _144_620 = (let _144_619 = (FStar_List.map (fun _43_565 -> (match (_43_565) with
| (x, _43_564) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _144_619 t))
in Some (_144_620))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _43_572)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_43_577, ({FStar_Absyn_Syntax.lbname = _43_584; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _43_581; FStar_Absyn_Syntax.lbdef = _43_579})::[]), _43_589, _43_591, _43_593)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_43_598, lbs), _43_602, _43_604, _43_606)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_43_612) -> begin
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
in (match ((let _144_622 = (lookup_qname env lid)
in (FStar_Util.bind_opt _144_622 mapper))) with
| Some (t) -> begin
(

let _43_620 = t
in (let _144_623 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _43_620.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _43_620.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _144_623; FStar_Absyn_Syntax.fvs = _43_620.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _43_620.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_43_626, _43_628, quals, _43_631))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___108 -> (match (uu___108) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _43_639 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_43_641, t, _43_644, _43_646, _43_648, _43_650))) -> begin
true
end
| _43_656 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_43_660, _43_662, _43_664, _43_666, _43_668, tags, _43_671))) -> begin
(FStar_Util.for_some (fun uu___109 -> (match (uu___109) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _43_684 -> begin
false
end)) tags)
end
| _43_686 -> begin
false
end))


let lookup_datacons_of_typ : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_43_690, _43_692, _43_694, _43_696, datas, _43_699, _43_701))) -> begin
(let _144_640 = (FStar_List.map (fun l -> (let _144_639 = (lookup_lid env l)
in ((l), (_144_639)))) datas)
in Some (_144_640))
end
| _43_708 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _43_716))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___110 -> (match (uu___110) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _43_724 -> begin
false
end)))) then begin
None
end else begin
Some (((binders), (c)))
end
end
| _43_726 -> begin
None
end))


let lookup_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _43_732, t, quals, _43_736))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___111 -> (match (uu___111) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _43_744 -> begin
false
end)))) then begin
None
end else begin
(

let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _144_651 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (lid)))))
in Some (_144_651)))
end
end
| _43_747 -> begin
None
end))


let lookup_opaque_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _43_753, t, quals, _43_757))) -> begin
(

let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _144_656 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named (((t), (lid)))))
in Some (_144_656)))
end
| _43_764 -> begin
None
end))


let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun uu___112 -> (match (uu___112) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _43_773 -> begin
None
end))))


let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _144_668 = (let _144_667 = (let _144_666 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in ((_144_666), ((FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v))))
in FStar_Errors.Error (_144_667))
in (Prims.raise _144_668))
end
| Some (k) -> begin
k
end))


let lookup_typ_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _43_807 -> begin
(let _144_675 = (let _144_674 = (let _144_673 = (name_not_found ftv)
in ((_144_673), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (_144_674))
in (Prims.raise _144_675))
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun uu___113 -> (match (uu___113) with
| FStar_Absyn_Syntax.Projector (_43_839) -> begin
true
end
| _43_842 -> begin
false
end)) quals)
end
| _43_844 -> begin
false
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _43_849))) -> begin
(let _144_686 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _144_686 (fun _144_685 -> Some (_144_685))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _43_857, _43_859, _43_861))) -> begin
(let _144_688 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _144_688 (fun _144_687 -> Some (_144_687))))
end
| _43_867 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _144_695 = (let _144_694 = (let _144_693 = (name_not_found ftv)
in ((_144_693), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (_144_694))
in (Prims.raise _144_695))
end
| Some (k) -> begin
k
end))


let lookup_operator : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ = (fun env opname -> (

let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (build_lattice (

let _43_878 = env
in {solver = _43_878.solver; range = _43_878.range; curmodule = _43_878.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _43_878.modules; expected_typ = _43_878.expected_typ; level = _43_878.level; sigtab = _43_878.sigtab; is_pattern = _43_878.is_pattern; instantiate_targs = _43_878.instantiate_targs; instantiate_vargs = _43_878.instantiate_vargs; effects = _43_878.effects; generalize = _43_878.generalize; letrecs = _43_878.letrecs; top_level = _43_878.top_level; check_uvars = _43_878.check_uvars; use_eq = _43_878.use_eq; is_iface = _43_878.is_iface; admit = _43_878.admit; default_effects = _43_878.default_effects}) s))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _43_882 = env
in {solver = _43_882.solver; range = _43_882.range; curmodule = _43_882.curmodule; gamma = (b)::env.gamma; modules = _43_882.modules; expected_typ = _43_882.expected_typ; level = _43_882.level; sigtab = _43_882.sigtab; is_pattern = _43_882.is_pattern; instantiate_targs = _43_882.instantiate_targs; instantiate_vargs = _43_882.instantiate_vargs; effects = _43_882.effects; generalize = _43_882.generalize; letrecs = _43_882.letrecs; top_level = _43_882.top_level; check_uvars = _43_882.check_uvars; use_eq = _43_882.use_eq; is_iface = _43_882.is_iface; admit = _43_882.admit; default_effects = _43_882.default_effects}))


let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (

let no_uvs = (let _144_712 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _144_711 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _144_710 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _144_712; FStar_Absyn_Syntax.uvars_t = _144_711; FStar_Absyn_Syntax.uvars_e = _144_710})))
in (

let ext = (fun out uvs -> (

let _43_889 = out
in (let _144_719 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _144_718 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _144_717 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _144_719; FStar_Absyn_Syntax.uvars_t = _144_718; FStar_Absyn_Syntax.uvars_e = _144_717})))))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| ((Binding_lid (_, t))::tl) | ((Binding_var (_, t))::tl) -> begin
(let _144_725 = (let _144_724 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _144_724))
in (aux _144_725 tl))
end
| (Binding_typ (_43_909, k))::tl -> begin
(let _144_727 = (let _144_726 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _144_726))
in (aux _144_727 tl))
end
| (Binding_sig (_43_917))::_43_915 -> begin
out
end))
in (aux no_uvs env.gamma)))))


let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (

let _43_922 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (

let _43_924 = env
in {solver = _43_924.solver; range = _43_924.range; curmodule = _43_924.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _43_924.level; sigtab = _43_924.sigtab; is_pattern = _43_924.is_pattern; instantiate_targs = _43_924.instantiate_targs; instantiate_vargs = _43_924.instantiate_vargs; effects = _43_924.effects; generalize = _43_924.generalize; letrecs = _43_924.letrecs; top_level = _43_924.top_level; check_uvars = _43_924.check_uvars; use_eq = _43_924.use_eq; is_iface = _43_924.is_iface; admit = _43_924.admit; default_effects = _43_924.default_effects})))


let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _43_949; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _43_945; FStar_Absyn_Syntax.pos = _43_943; FStar_Absyn_Syntax.fvs = _43_941; FStar_Absyn_Syntax.uvs = _43_939}; FStar_Absyn_Syntax.p = _43_937}); FStar_Absyn_Syntax.tk = _43_935; FStar_Absyn_Syntax.pos = _43_933; FStar_Absyn_Syntax.fvs = _43_931; FStar_Absyn_Syntax.uvs = _43_929} -> begin
(let _144_737 = (let _144_736 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _144_736))
in (failwith _144_737))
end
| _43_954 -> begin
(

let _43_955 = env
in {solver = _43_955.solver; range = _43_955.range; curmodule = _43_955.curmodule; gamma = _43_955.gamma; modules = _43_955.modules; expected_typ = Some (t); level = _43_955.level; sigtab = _43_955.sigtab; is_pattern = _43_955.is_pattern; instantiate_targs = _43_955.instantiate_targs; instantiate_vargs = _43_955.instantiate_vargs; effects = _43_955.effects; generalize = _43_955.generalize; letrecs = _43_955.letrecs; top_level = _43_955.top_level; check_uvars = _43_955.check_uvars; use_eq = false; is_iface = _43_955.is_iface; admit = _43_955.admit; default_effects = _43_955.default_effects})
end))


let expected_typ : env  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _144_742 = (expected_typ env)
in (((

let _43_962 = env
in {solver = _43_962.solver; range = _43_962.range; curmodule = _43_962.curmodule; gamma = _43_962.gamma; modules = _43_962.modules; expected_typ = None; level = _43_962.level; sigtab = _43_962.sigtab; is_pattern = _43_962.is_pattern; instantiate_targs = _43_962.instantiate_targs; instantiate_vargs = _43_962.instantiate_vargs; effects = _43_962.effects; generalize = _43_962.generalize; letrecs = _43_962.letrecs; top_level = _43_962.top_level; check_uvars = _43_962.check_uvars; use_eq = false; is_iface = _43_962.is_iface; admit = _43_962.admit; default_effects = _43_962.default_effects})), (_144_742))))


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
(let _144_760 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_144_760)::out)
end
| Binding_typ (a, k) -> begin
(let _144_761 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_144_761)::out)
end
| _43_986 -> begin
out
end)) [] env.gamma))


let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_43_991) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _144_766 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_144_766)::out)
end
| _43_998 -> begin
out
end)) [] env.gamma))


let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _144_770 = (let _144_769 = (binders env)
in (FStar_All.pipe_right _144_769 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _144_770)))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___114 -> (match (uu___114) with
| Binding_sig (s) -> begin
(let _144_775 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _144_775 keys))
end
| _43_1006 -> begin
keys
end)) [] env.gamma)
in (let _144_780 = (sigtab env)
in (FStar_Util.smap_fold _144_780 (fun _43_1008 v keys -> (let _144_779 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _144_779 keys))) keys))))




