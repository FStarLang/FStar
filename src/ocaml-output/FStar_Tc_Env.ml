
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
| Binding_var (_40_16) -> begin
_40_16
end))


let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_40_19) -> begin
_40_19
end))


let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_40_22) -> begin
_40_22
end))


let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_40_25) -> begin
_40_25
end))


type sigtable =
FStar_Absyn_Syntax.sigelt FStar_Util.smap


let default_table_size : Prims.int = 200


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

let _40_35 = (FStar_List.iter (fun se -> (

let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))


let modules_to_sigtables = (fun mods -> (let _129_65 = (FStar_List.collect (fun _40_41 -> (match (_40_41) with
| (_40_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _129_65)))


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


let is_Mkedge : edge  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))


type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let is_Mkeffects : effects  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))


type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mksolver_t : solver_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))


let bound_vars : env  ->  (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _40_1 -> (match (_40_1) with
| Binding_typ (a, k) -> begin
(let _129_291 = (FStar_All.pipe_left (fun _129_290 -> FStar_Util.Inl (_129_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_129_291)::[])
end
| Binding_var (x, t) -> begin
(let _129_293 = (FStar_All.pipe_left (fun _129_292 -> FStar_Util.Inr (_129_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_129_293)::[])
end
| Binding_lid (_40_96) -> begin
[]
end
| Binding_sig (_40_99) -> begin
[]
end)))))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> ((let _129_304 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _129_304 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))) && (FStar_Options.debug_level_geq l)))


let show : env  ->  Prims.bool = (fun env -> (let _129_308 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _129_308 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))))


let new_sigtab = (fun _40_109 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))


let sigtab : env  ->  sigtable = (fun env -> (FStar_List.hd env.sigtab))


let push : env  ->  Prims.string  ->  env = (fun env msg -> (

let _40_113 = (env.solver.push msg)
in (

let _40_115 = env
in (let _129_318 = (let _129_317 = (let _129_316 = (sigtab env)
in (FStar_Util.smap_copy _129_316))
in (_129_317)::env.sigtab)
in {solver = _40_115.solver; range = _40_115.range; curmodule = _40_115.curmodule; gamma = _40_115.gamma; modules = _40_115.modules; expected_typ = _40_115.expected_typ; level = _40_115.level; sigtab = _129_318; is_pattern = _40_115.is_pattern; instantiate_targs = _40_115.instantiate_targs; instantiate_vargs = _40_115.instantiate_vargs; effects = _40_115.effects; generalize = _40_115.generalize; letrecs = _40_115.letrecs; top_level = _40_115.top_level; check_uvars = _40_115.check_uvars; use_eq = _40_115.use_eq; is_iface = _40_115.is_iface; admit = _40_115.admit; default_effects = _40_115.default_effects}))))


let mark : env  ->  env = (fun env -> (

let _40_118 = (env.solver.mark "USER MARK")
in (

let _40_120 = env
in (let _129_323 = (let _129_322 = (let _129_321 = (sigtab env)
in (FStar_Util.smap_copy _129_321))
in (_129_322)::env.sigtab)
in {solver = _40_120.solver; range = _40_120.range; curmodule = _40_120.curmodule; gamma = _40_120.gamma; modules = _40_120.modules; expected_typ = _40_120.expected_typ; level = _40_120.level; sigtab = _129_323; is_pattern = _40_120.is_pattern; instantiate_targs = _40_120.instantiate_targs; instantiate_vargs = _40_120.instantiate_vargs; effects = _40_120.effects; generalize = _40_120.generalize; letrecs = _40_120.letrecs; top_level = _40_120.top_level; check_uvars = _40_120.check_uvars; use_eq = _40_120.use_eq; is_iface = _40_120.is_iface; admit = _40_120.admit; default_effects = _40_120.default_effects}))))


let commit_mark : env  ->  env = (fun env -> (

let _40_123 = (env.solver.commit_mark "USER MARK")
in (

let sigtab = (match (env.sigtab) with
| hd::_40_127::tl -> begin
(hd)::tl
end
| _40_132 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _40_134 = env
in {solver = _40_134.solver; range = _40_134.range; curmodule = _40_134.curmodule; gamma = _40_134.gamma; modules = _40_134.modules; expected_typ = _40_134.expected_typ; level = _40_134.level; sigtab = sigtab; is_pattern = _40_134.is_pattern; instantiate_targs = _40_134.instantiate_targs; instantiate_vargs = _40_134.instantiate_vargs; effects = _40_134.effects; generalize = _40_134.generalize; letrecs = _40_134.letrecs; top_level = _40_134.top_level; check_uvars = _40_134.check_uvars; use_eq = _40_134.use_eq; is_iface = _40_134.is_iface; admit = _40_134.admit; default_effects = _40_134.default_effects}))))


let reset_mark : env  ->  env = (fun env -> (

let _40_137 = (env.solver.reset_mark "USER MARK")
in (

let _40_139 = env
in (let _129_328 = (FStar_List.tl env.sigtab)
in {solver = _40_139.solver; range = _40_139.range; curmodule = _40_139.curmodule; gamma = _40_139.gamma; modules = _40_139.modules; expected_typ = _40_139.expected_typ; level = _40_139.level; sigtab = _129_328; is_pattern = _40_139.is_pattern; instantiate_targs = _40_139.instantiate_targs; instantiate_vargs = _40_139.instantiate_vargs; effects = _40_139.effects; generalize = _40_139.generalize; letrecs = _40_139.letrecs; top_level = _40_139.top_level; check_uvars = _40_139.check_uvars; use_eq = _40_139.use_eq; is_iface = _40_139.is_iface; admit = _40_139.admit; default_effects = _40_139.default_effects}))))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _40_149::tl -> begin
(

let _40_151 = (env.solver.pop msg)
in (

let _40_153 = env
in {solver = _40_153.solver; range = _40_153.range; curmodule = _40_153.curmodule; gamma = _40_153.gamma; modules = _40_153.modules; expected_typ = _40_153.expected_typ; level = _40_153.level; sigtab = tl; is_pattern = _40_153.is_pattern; instantiate_targs = _40_153.instantiate_targs; instantiate_vargs = _40_153.instantiate_vargs; effects = _40_153.effects; generalize = _40_153.generalize; letrecs = _40_153.letrecs; top_level = _40_153.top_level; check_uvars = _40_153.check_uvars; use_eq = _40_153.use_eq; is_iface = _40_153.is_iface; admit = _40_153.admit; default_effects = _40_153.default_effects}))
end))


let initial_env : solver_t  ->  FStar_Ident.lident  ->  env = (fun solver module_lid -> (let _129_338 = (let _129_337 = (new_sigtab ())
in (_129_337)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _129_338; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl Prims.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))


let name_not_found : FStar_Absyn_Syntax.lident  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found = (fun v -> (let _129_347 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _129_347)))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.eff_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _129_354 = (let _129_353 = (let _129_352 = (name_not_found l)
in (_129_352, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_129_353))
in (Prims.raise _129_354))
end
| Some (md) -> begin
md
end))


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _40_182 -> (match (_40_182) with
| (m1, m2, _40_177, _40_179, _40_181) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _129_410 = (let _129_409 = (let _129_408 = (let _129_407 = (FStar_Absyn_Print.sli l1)
in (let _129_406 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _129_407 _129_406)))
in (_129_408, env.range))
in FStar_Absyn_Syntax.Error (_129_409))
in (Prims.raise _129_410))
end
| Some (_40_185, _40_187, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end)


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge Prims.option = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)


let wp_sig_aux : FStar_Absyn_Syntax.eff_decl Prims.list  ->  FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _129_425 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _129_425))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _40_218)::(FStar_Util.Inl (wp), _40_213)::(FStar_Util.Inl (wlp), _40_208)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _40_228; FStar_Absyn_Syntax.pos = _40_226; FStar_Absyn_Syntax.fvs = _40_224; FStar_Absyn_Syntax.uvs = _40_222}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _40_234 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.btvar * FStar_Absyn_Syntax.knd) = (fun env m -> (wp_sig_aux env.effects.decls m))


let default_effect : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun env l -> (FStar_Util.find_map env.default_effects (fun _40_241 -> (match (_40_241) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))


let build_lattice : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _40_246, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _40_2 -> (match (_40_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _40_256 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(

let _40_260 = env
in {solver = _40_260.solver; range = _40_260.range; curmodule = _40_260.curmodule; gamma = _40_260.gamma; modules = _40_260.modules; expected_typ = _40_260.expected_typ; level = _40_260.level; sigtab = _40_260.sigtab; is_pattern = _40_260.is_pattern; instantiate_targs = _40_260.instantiate_targs; instantiate_vargs = _40_260.instantiate_vargs; effects = _40_260.effects; generalize = _40_260.generalize; letrecs = _40_260.letrecs; top_level = _40_260.top_level; check_uvars = _40_260.check_uvars; use_eq = _40_260.use_eq; is_iface = _40_260.is_iface; admit = _40_260.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _40_264) -> begin
(

let effects = (

let _40_267 = env.effects
in {decls = (ne)::env.effects.decls; order = _40_267.order; joins = _40_267.joins})
in (

let _40_270 = env
in {solver = _40_270.solver; range = _40_270.range; curmodule = _40_270.curmodule; gamma = _40_270.gamma; modules = _40_270.modules; expected_typ = _40_270.expected_typ; level = _40_270.level; sigtab = _40_270.sigtab; is_pattern = _40_270.is_pattern; instantiate_targs = _40_270.instantiate_targs; instantiate_vargs = _40_270.instantiate_vargs; effects = effects; generalize = _40_270.generalize; letrecs = _40_270.letrecs; top_level = _40_270.top_level; check_uvars = _40_270.check_uvars; use_eq = _40_270.use_eq; is_iface = _40_270.is_iface; admit = _40_270.admit; default_effects = _40_270.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _40_274) -> begin
(

let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _129_446 = (e1.mlift r wp1)
in (e2.mlift r _129_446)))})
in (

let mk_lift = (fun lift_t r wp1 -> (let _129_457 = (let _129_456 = (let _129_455 = (FStar_Absyn_Syntax.targ r)
in (let _129_454 = (let _129_453 = (FStar_Absyn_Syntax.targ wp1)
in (_129_453)::[])
in (_129_455)::_129_454))
in (lift_t, _129_456))
in (FStar_Absyn_Syntax.mk_Typ_app _129_457 None wp1.FStar_Absyn_Syntax.pos)))
in (

let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (

let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (

let print_mlift = (fun l -> (

let arg = (let _129_474 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _129_474 FStar_Absyn_Syntax.mk_Kind_type))
in (

let wp = (let _129_475 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _129_475 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _129_476 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _129_476)))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (

let find_edge = (fun order _40_302 -> (match (_40_302) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _129_482 -> Some (_129_482)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (

let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _129_490 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _129_489 = (find_edge order (i, k))
in (let _129_488 = (find_edge order (k, j))
in (_129_489, _129_488)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _40_314 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _129_490))) order))
in (

let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _129_498 = (find_edge order (i, k))
in (let _129_497 = (find_edge order (j, k))
in (_129_498, _129_497)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _40_331, _40_333) -> begin
if ((let _129_499 = (find_edge order (k, ub))
in (FStar_Util.is_some _129_499)) && (not ((let _129_500 = (find_edge order (ub, k))
in (FStar_Util.is_some _129_500))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _40_337 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (

let effects = (

let _40_346 = env.effects
in {decls = _40_346.decls; order = order; joins = joins})
in (

let _40_349 = env
in {solver = _40_349.solver; range = _40_349.range; curmodule = _40_349.curmodule; gamma = _40_349.gamma; modules = _40_349.modules; expected_typ = _40_349.expected_typ; level = _40_349.level; sigtab = _40_349.sigtab; is_pattern = _40_349.is_pattern; instantiate_targs = _40_349.instantiate_targs; instantiate_vargs = _40_349.instantiate_vargs; effects = effects; generalize = _40_349.generalize; letrecs = _40_349.letrecs; top_level = _40_349.top_level; check_uvars = _40_349.check_uvars; use_eq = _40_349.use_eq; is_iface = _40_349.is_iface; admit = _40_349.admit; default_effects = _40_349.default_effects})))))))))))))
end
| _40_352 -> begin
env
end))


let rec add_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _40_357, _40_359, _40_361) -> begin
(add_sigelts env ses)
end
| _40_365 -> begin
(

let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _129_508 = (sigtab env)
in (FStar_Util.smap_add _129_508 l.FStar_Ident.str se))) lids))
end))
and add_sigelts : env  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let empty_lid : FStar_Absyn_Syntax.lident = (let _129_512 = (let _129_511 = (FStar_Absyn_Syntax.id_of_text "")
in (_129_511)::[])
in (FStar_Absyn_Syntax.lid_of_ids _129_512))


let finish_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (

let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _40_3 -> (match (_40_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _40_376 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (

let _40_378 = (add_sigelts env sigs)
in (

let _40_380 = env
in {solver = _40_380.solver; range = _40_380.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _40_380.expected_typ; level = _40_380.level; sigtab = _40_380.sigtab; is_pattern = _40_380.is_pattern; instantiate_targs = _40_380.instantiate_targs; instantiate_vargs = _40_380.instantiate_vargs; effects = _40_380.effects; generalize = _40_380.generalize; letrecs = _40_380.letrecs; top_level = _40_380.top_level; check_uvars = _40_380.check_uvars; use_eq = _40_380.use_eq; is_iface = _40_380.is_iface; admit = _40_380.admit; default_effects = _40_380.default_effects}))))


let set_level : env  ->  level  ->  env = (fun env level -> (

let _40_384 = env
in {solver = _40_384.solver; range = _40_384.range; curmodule = _40_384.curmodule; gamma = _40_384.gamma; modules = _40_384.modules; expected_typ = _40_384.expected_typ; level = level; sigtab = _40_384.sigtab; is_pattern = _40_384.is_pattern; instantiate_targs = _40_384.instantiate_targs; instantiate_vargs = _40_384.instantiate_vargs; effects = _40_384.effects; generalize = _40_384.generalize; letrecs = _40_384.letrecs; top_level = _40_384.top_level; check_uvars = _40_384.check_uvars; use_eq = _40_384.use_eq; is_iface = _40_384.is_iface; admit = _40_384.admit; default_effects = _40_384.default_effects}))


let is_level : env  ->  level  ->  Prims.bool = (fun env level -> (env.level = level))


let modules : env  ->  FStar_Absyn_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let _40_392 = env
in {solver = _40_392.solver; range = _40_392.range; curmodule = lid; gamma = _40_392.gamma; modules = _40_392.modules; expected_typ = _40_392.expected_typ; level = _40_392.level; sigtab = _40_392.sigtab; is_pattern = _40_392.is_pattern; instantiate_targs = _40_392.instantiate_targs; instantiate_vargs = _40_392.instantiate_vargs; effects = _40_392.effects; generalize = _40_392.generalize; letrecs = _40_392.letrecs; top_level = _40_392.top_level; check_uvars = _40_392.check_uvars; use_eq = _40_392.use_eq; is_iface = _40_392.is_iface; admit = _40_392.admit; default_effects = _40_392.default_effects}))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(

let _40_396 = e
in {solver = _40_396.solver; range = r; curmodule = _40_396.curmodule; gamma = _40_396.gamma; modules = _40_396.modules; expected_typ = _40_396.expected_typ; level = _40_396.level; sigtab = _40_396.sigtab; is_pattern = _40_396.is_pattern; instantiate_targs = _40_396.instantiate_targs; instantiate_vargs = _40_396.instantiate_vargs; effects = _40_396.effects; generalize = _40_396.generalize; letrecs = _40_396.letrecs; top_level = _40_396.top_level; check_uvars = _40_396.check_uvars; use_eq = _40_396.use_eq; is_iface = _40_396.is_iface; admit = _40_396.admit; default_effects = _40_396.default_effects})
end)


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.sigelt Prims.option = (fun env lid -> (let _129_544 = (sigtab env)
in (FStar_Util.smap_try_find _129_544 (FStar_Ident.text_of_lid lid))))


let lookup_bvvdef : env  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _40_4 -> (match (_40_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _40_409 -> begin
None
end))))


let lookup_bvar : env  ->  FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _129_556 = (let _129_555 = (let _129_554 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in (_129_554, (FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_129_555))
in (Prims.raise _129_556))
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

let rec aux = (fun c l -> (match ((c, l)) with
| ([], _40_425) -> begin
true
end
| (_40_428, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _40_439 -> begin
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
(FStar_Util.find_map env.gamma (fun _40_5 -> (match (_40_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _40_450, _40_452, _40_454)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _129_571 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _129_571 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
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
| _40_463 -> begin
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
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_40_471, t, (_40_474, tps, _40_477), _40_480, _40_482, _40_484))) -> begin
(let _129_577 = (FStar_List.map (fun _40_492 -> (match (_40_492) with
| (x, _40_491) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _129_577 t))
end
| _40_494 -> begin
(let _129_580 = (let _129_579 = (let _129_578 = (name_not_found lid)
in (_129_578, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_129_579))
in (Prims.raise _129_580))
end))


let lookup_kind_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.knd) = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _40_501))) -> begin
(l, binders, k)
end
| _40_507 -> begin
(let _129_587 = (let _129_586 = (let _129_585 = (name_not_found lid)
in (_129_585, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_129_586))
in (Prims.raise _129_587))
end))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun _40_512 -> (match (()) with
| () -> begin
(let _129_598 = (let _129_597 = (FStar_Util.string_of_int i)
in (let _129_596 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _129_597 _129_596)))
in (FStar_All.failwith _129_598))
end))
in (

let t = (lookup_datacon env lid)
in (match ((let _129_599 = (FStar_Absyn_Util.compress_typ t)
in _129_599.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _40_516) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _129_600 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _129_600 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _129_601 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _129_601 Prims.fst))
end))
end
end
| _40_525 -> begin
(fail ())
end))))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.qualifier Prims.list) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_40_529, t, q, _40_533))) -> begin
Some ((t, q))
end
| _40_539 -> begin
None
end))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_40_543, t, _40_546, _40_548))) -> begin
t
end
| _40_554 -> begin
(let _129_612 = (let _129_611 = (let _129_610 = (name_not_found lid)
in (_129_610, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_129_611))
in (Prims.raise _129_612))
end))


let lookup_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ = (fun env lid -> (

let not_found = (fun _40_558 -> (match (()) with
| () -> begin
(let _129_621 = (let _129_620 = (let _129_619 = (name_not_found lid)
in (_129_619, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_129_620))
in (Prims.raise _129_621))
end))
in (

let mapper = (fun _40_6 -> (match (_40_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_40_561, t, (_40_564, tps, _40_567), _40_570, _40_572, _40_574)) -> begin
(let _129_626 = (let _129_625 = (FStar_List.map (fun _40_581 -> (match (_40_581) with
| (x, _40_580) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _129_625 t))
in Some (_129_626))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _40_588)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_40_593, {FStar_Absyn_Syntax.lbname = _40_600; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _40_597; FStar_Absyn_Syntax.lbdef = _40_595}::[]), _40_605, _40_607, _40_609)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_40_614, lbs), _40_618, _40_620, _40_622)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_40_628) -> begin
(FStar_All.failwith "impossible")
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
in (match ((let _129_628 = (lookup_qname env lid)
in (FStar_Util.bind_opt _129_628 mapper))) with
| Some (t) -> begin
(

let _40_636 = t
in (let _129_629 = (FStar_Absyn_Syntax.range_of_lid lid)
in {FStar_Absyn_Syntax.n = _40_636.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _40_636.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _129_629; FStar_Absyn_Syntax.fvs = _40_636.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _40_636.FStar_Absyn_Syntax.uvs}))
end
| None -> begin
(not_found ())
end))))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_40_642, _40_644, quals, _40_647))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _40_7 -> (match (_40_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _40_655 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_40_657, t, _40_660, _40_662, _40_664, _40_666))) -> begin
true
end
| _40_672 -> begin
false
end))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_40_676, _40_678, _40_680, _40_682, _40_684, tags, _40_687))) -> begin
(FStar_Util.for_some (fun _40_8 -> (match (_40_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _40_700 -> begin
false
end)) tags)
end
| _40_702 -> begin
false
end))


let lookup_datacons_of_typ : env  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) Prims.list Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_40_706, _40_708, _40_710, _40_712, datas, _40_715, _40_717))) -> begin
(let _129_646 = (FStar_List.map (fun l -> (let _129_645 = (lookup_lid env l)
in (l, _129_645))) datas)
in Some (_129_646))
end
| _40_724 -> begin
None
end))


let lookup_effect_abbrev : env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _40_732))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _40_9 -> (match (_40_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _40_740 -> begin
false
end)))) then begin
None
end else begin
Some ((binders, c))
end
end
| _40_742 -> begin
None
end))


let lookup_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _40_748, t, quals, _40_752))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _40_10 -> (match (_40_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _40_760 -> begin
false
end)))) then begin
None
end else begin
(

let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _129_657 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_129_657)))
end
end
| _40_763 -> begin
None
end))


let lookup_opaque_typ_abbrev : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _40_769, t, quals, _40_773))) -> begin
(

let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _129_662 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_129_662)))
end
| _40_780 -> begin
None
end))


let lookup_btvdef : env  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _40_11 -> (match (_40_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _40_789 -> begin
None
end))))


let lookup_btvar : env  ->  FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.knd = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _129_674 = (let _129_673 = (let _129_672 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_129_672, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_129_673))
in (Prims.raise _129_674))
end
| Some (k) -> begin
k
end))


let lookup_typ_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _40_823 -> begin
(let _129_681 = (let _129_680 = (let _129_679 = (name_not_found ftv)
in (_129_679, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_129_680))
in (Prims.raise _129_681))
end))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _40_12 -> (match (_40_12) with
| FStar_Absyn_Syntax.Projector (_40_855) -> begin
true
end
| _40_858 -> begin
false
end)) quals)
end
| _40_860 -> begin
false
end))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd Prims.option = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _40_865))) -> begin
(let _129_692 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _129_692 (fun _129_691 -> Some (_129_691))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _40_873, _40_875, _40_877))) -> begin
(let _129_694 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _129_694 (fun _129_693 -> Some (_129_693))))
end
| _40_883 -> begin
None
end))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.knd = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _129_701 = (let _129_700 = (let _129_699 = (name_not_found ftv)
in (_129_699, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_129_700))
in (Prims.raise _129_701))
end
| Some (k) -> begin
k
end))


let lookup_operator : env  ->  FStar_Ident.ident  ->  FStar_Absyn_Syntax.typ = (fun env opname -> (

let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))


let push_sigelt : env  ->  FStar_Absyn_Syntax.sigelt  ->  env = (fun env s -> (build_lattice (

let _40_894 = env
in {solver = _40_894.solver; range = _40_894.range; curmodule = _40_894.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _40_894.modules; expected_typ = _40_894.expected_typ; level = _40_894.level; sigtab = _40_894.sigtab; is_pattern = _40_894.is_pattern; instantiate_targs = _40_894.instantiate_targs; instantiate_vargs = _40_894.instantiate_vargs; effects = _40_894.effects; generalize = _40_894.generalize; letrecs = _40_894.letrecs; top_level = _40_894.top_level; check_uvars = _40_894.check_uvars; use_eq = _40_894.use_eq; is_iface = _40_894.is_iface; admit = _40_894.admit; default_effects = _40_894.default_effects}) s))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let _40_898 = env
in {solver = _40_898.solver; range = _40_898.range; curmodule = _40_898.curmodule; gamma = (b)::env.gamma; modules = _40_898.modules; expected_typ = _40_898.expected_typ; level = _40_898.level; sigtab = _40_898.sigtab; is_pattern = _40_898.is_pattern; instantiate_targs = _40_898.instantiate_targs; instantiate_vargs = _40_898.instantiate_vargs; effects = _40_898.effects; generalize = _40_898.generalize; letrecs = _40_898.letrecs; top_level = _40_898.top_level; check_uvars = _40_898.check_uvars; use_eq = _40_898.use_eq; is_iface = _40_898.is_iface; admit = _40_898.admit; default_effects = _40_898.default_effects}))


let uvars_in_env : env  ->  FStar_Absyn_Syntax.uvars = (fun env -> (

let no_uvs = (let _129_718 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _129_717 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _129_716 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _129_718; FStar_Absyn_Syntax.uvars_t = _129_717; FStar_Absyn_Syntax.uvars_e = _129_716})))
in (

let ext = (fun out uvs -> (

let _40_905 = out
in (let _129_725 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _129_724 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _129_723 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _129_725; FStar_Absyn_Syntax.uvars_t = _129_724; FStar_Absyn_Syntax.uvars_e = _129_723})))))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _129_731 = (let _129_730 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _129_730))
in (aux _129_731 tl))
end
| Binding_typ (_40_925, k)::tl -> begin
(let _129_733 = (let _129_732 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _129_732))
in (aux _129_733 tl))
end
| Binding_sig (_40_933)::_40_931 -> begin
out
end))
in (aux no_uvs env.gamma)))))


let push_module : env  ->  FStar_Absyn_Syntax.modul  ->  env = (fun env m -> (

let _40_938 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (

let _40_940 = env
in {solver = _40_940.solver; range = _40_940.range; curmodule = _40_940.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _40_940.level; sigtab = _40_940.sigtab; is_pattern = _40_940.is_pattern; instantiate_targs = _40_940.instantiate_targs; instantiate_vargs = _40_940.instantiate_vargs; effects = _40_940.effects; generalize = _40_940.generalize; letrecs = _40_940.letrecs; top_level = _40_940.top_level; check_uvars = _40_940.check_uvars; use_eq = _40_940.use_eq; is_iface = _40_940.is_iface; admit = _40_940.admit; default_effects = _40_940.default_effects})))


let set_expected_typ : env  ->  FStar_Absyn_Syntax.typ  ->  env = (fun env t -> (match (t) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const ({FStar_Absyn_Syntax.v = _40_965; FStar_Absyn_Syntax.sort = {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_unknown; FStar_Absyn_Syntax.tk = _40_961; FStar_Absyn_Syntax.pos = _40_959; FStar_Absyn_Syntax.fvs = _40_957; FStar_Absyn_Syntax.uvs = _40_955}; FStar_Absyn_Syntax.p = _40_953}); FStar_Absyn_Syntax.tk = _40_951; FStar_Absyn_Syntax.pos = _40_949; FStar_Absyn_Syntax.fvs = _40_947; FStar_Absyn_Syntax.uvs = _40_945} -> begin
(let _129_743 = (let _129_742 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "Setting expected type to %s with kind unknown" _129_742))
in (FStar_All.failwith _129_743))
end
| _40_970 -> begin
(

let _40_971 = env
in {solver = _40_971.solver; range = _40_971.range; curmodule = _40_971.curmodule; gamma = _40_971.gamma; modules = _40_971.modules; expected_typ = Some (t); level = _40_971.level; sigtab = _40_971.sigtab; is_pattern = _40_971.is_pattern; instantiate_targs = _40_971.instantiate_targs; instantiate_vargs = _40_971.instantiate_vargs; effects = _40_971.effects; generalize = _40_971.generalize; letrecs = _40_971.letrecs; top_level = _40_971.top_level; check_uvars = _40_971.check_uvars; use_eq = false; is_iface = _40_971.is_iface; admit = _40_971.admit; default_effects = _40_971.default_effects})
end))


let expected_typ : env  ->  FStar_Absyn_Syntax.typ Prims.option = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Absyn_Syntax.typ Prims.option) = (fun env -> (let _129_748 = (expected_typ env)
in ((

let _40_978 = env
in {solver = _40_978.solver; range = _40_978.range; curmodule = _40_978.curmodule; gamma = _40_978.gamma; modules = _40_978.modules; expected_typ = None; level = _40_978.level; sigtab = _40_978.sigtab; is_pattern = _40_978.is_pattern; instantiate_targs = _40_978.instantiate_targs; instantiate_vargs = _40_978.instantiate_vargs; effects = _40_978.effects; generalize = _40_978.generalize; letrecs = _40_978.letrecs; top_level = _40_978.top_level; check_uvars = _40_978.check_uvars; use_eq = false; is_iface = _40_978.is_iface; admit = _40_978.admit; default_effects = _40_978.default_effects}), _129_748)))


let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))


let binding_of_binder : FStar_Absyn_Syntax.binder  ->  binding = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
end))


let binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _129_766 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_129_766)::out)
end
| Binding_typ (a, k) -> begin
(let _129_767 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_129_767)::out)
end
| _40_1002 -> begin
out
end)) [] env.gamma))


let t_binders : env  ->  FStar_Absyn_Syntax.binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_40_1007) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _129_772 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_129_772)::out)
end
| _40_1014 -> begin
out
end)) [] env.gamma))


let idents : env  ->  FStar_Absyn_Syntax.freevars = (fun env -> (let _129_776 = (let _129_775 = (binders env)
in (FStar_All.pipe_right _129_775 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _129_776)))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys _40_13 -> (match (_40_13) with
| Binding_sig (s) -> begin
(let _129_781 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _129_781 keys))
end
| _40_1022 -> begin
keys
end)) [] env.gamma)
in (let _129_786 = (sigtab env)
in (FStar_Util.smap_fold _129_786 (fun _40_1024 v keys -> (let _129_785 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _129_785 keys))) keys))))




