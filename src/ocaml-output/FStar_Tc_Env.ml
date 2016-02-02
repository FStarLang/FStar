
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
| Binding_var (_43_16) -> begin
_43_16
end))

let ___Binding_typ____0 = (fun projectee -> (match (projectee) with
| Binding_typ (_43_19) -> begin
_43_19
end))

let ___Binding_lid____0 = (fun projectee -> (match (projectee) with
| Binding_lid (_43_22) -> begin
_43_22
end))

let ___Binding_sig____0 = (fun projectee -> (match (projectee) with
| Binding_sig (_43_25) -> begin
_43_25
end))

type sigtable =
FStar_Absyn_Syntax.sigelt FStar_Util.smap

let default_table_size = 200

let strlid_of_sigelt = (fun se -> (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
None
end
| Some (l) -> begin
Some ((FStar_Ident.text_of_lid l))
end))

let signature_to_sigtables = (fun s -> (let ht = (FStar_Util.smap_create default_table_size)
in (let _43_35 = (FStar_List.iter (fun se -> (let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (FStar_Util.smap_add ht l.FStar_Ident.str se)) lids))) s)
in ht)))

let modules_to_sigtables = (fun mods -> (let _96_65 = (FStar_List.collect (fun _43_41 -> (match (_43_41) with
| (_43_39, m) -> begin
m.FStar_Absyn_Syntax.declarations
end)) mods)
in (signature_to_sigtables _96_65)))

type level =
| Expr
| Type
| Kind

let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type = (fun _discr_ -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

type mlift =
FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}

let is_Mkedge = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkedge"))))

type effects =
{decls : FStar_Absyn_Syntax.eff_decl Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}

let is_Mkeffects = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkeffects"))))

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; modules : FStar_Absyn_Syntax.modul Prims.list; expected_typ : FStar_Absyn_Syntax.typ Prims.option; level : level; sigtab : sigtable Prims.list; is_pattern : Prims.bool; instantiate_targs : Prims.bool; instantiate_vargs : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; default_effects : (FStar_Ident.lident * FStar_Ident.lident) Prims.list} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; mark : Prims.string  ->  Prims.unit; reset_mark : Prims.string  ->  Prims.unit; commit_mark : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit; solve : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit; is_trivial : env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkenv = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))

let is_Mksolver_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mksolver_t"))))

let bound_vars = (fun env -> (FStar_All.pipe_right env.gamma (FStar_List.collect (fun _43_1 -> (match (_43_1) with
| Binding_typ (a, k) -> begin
(let _96_291 = (FStar_All.pipe_left (fun _96_290 -> FStar_Util.Inl (_96_290)) (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_96_291)::[])
end
| Binding_var (x, t) -> begin
(let _96_293 = (FStar_All.pipe_left (fun _96_292 -> FStar_Util.Inr (_96_292)) (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_96_293)::[])
end
| Binding_lid (_43_95) -> begin
[]
end
| Binding_sig (_43_98) -> begin
[]
end)))))

let has_interface = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Absyn_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name l))))))

let debug = (fun env l -> ((let _96_304 = (FStar_ST.read FStar_Options.debug)
in (FStar_All.pipe_right _96_304 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))) && (FStar_Options.debug_level_geq l)))

let show = (fun env -> (let _96_308 = (FStar_ST.read FStar_Options.show_signatures)
in (FStar_All.pipe_right _96_308 (FStar_Util.for_some (fun x -> (env.curmodule.FStar_Ident.str = x))))))

let new_sigtab = (fun _43_108 -> (match (()) with
| () -> begin
(FStar_Util.smap_create default_table_size)
end))

let sigtab = (fun env -> (FStar_List.hd env.sigtab))

let push = (fun env msg -> (let _43_112 = (env.solver.push msg)
in (let _43_114 = env
in (let _96_318 = (let _96_317 = (let _96_316 = (sigtab env)
in (FStar_Util.smap_copy _96_316))
in (_96_317)::env.sigtab)
in {solver = _43_114.solver; range = _43_114.range; curmodule = _43_114.curmodule; gamma = _43_114.gamma; modules = _43_114.modules; expected_typ = _43_114.expected_typ; level = _43_114.level; sigtab = _96_318; is_pattern = _43_114.is_pattern; instantiate_targs = _43_114.instantiate_targs; instantiate_vargs = _43_114.instantiate_vargs; effects = _43_114.effects; generalize = _43_114.generalize; letrecs = _43_114.letrecs; top_level = _43_114.top_level; check_uvars = _43_114.check_uvars; use_eq = _43_114.use_eq; is_iface = _43_114.is_iface; admit = _43_114.admit; default_effects = _43_114.default_effects}))))

let mark = (fun env -> (let _43_117 = (env.solver.mark "USER MARK")
in (let _43_119 = env
in (let _96_323 = (let _96_322 = (let _96_321 = (sigtab env)
in (FStar_Util.smap_copy _96_321))
in (_96_322)::env.sigtab)
in {solver = _43_119.solver; range = _43_119.range; curmodule = _43_119.curmodule; gamma = _43_119.gamma; modules = _43_119.modules; expected_typ = _43_119.expected_typ; level = _43_119.level; sigtab = _96_323; is_pattern = _43_119.is_pattern; instantiate_targs = _43_119.instantiate_targs; instantiate_vargs = _43_119.instantiate_vargs; effects = _43_119.effects; generalize = _43_119.generalize; letrecs = _43_119.letrecs; top_level = _43_119.top_level; check_uvars = _43_119.check_uvars; use_eq = _43_119.use_eq; is_iface = _43_119.is_iface; admit = _43_119.admit; default_effects = _43_119.default_effects}))))

let commit_mark = (fun env -> (let _43_122 = (env.solver.commit_mark "USER MARK")
in (let sigtab = (match (env.sigtab) with
| hd::_43_126::tl -> begin
(hd)::tl
end
| _43_131 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _43_133 = env
in {solver = _43_133.solver; range = _43_133.range; curmodule = _43_133.curmodule; gamma = _43_133.gamma; modules = _43_133.modules; expected_typ = _43_133.expected_typ; level = _43_133.level; sigtab = sigtab; is_pattern = _43_133.is_pattern; instantiate_targs = _43_133.instantiate_targs; instantiate_vargs = _43_133.instantiate_vargs; effects = _43_133.effects; generalize = _43_133.generalize; letrecs = _43_133.letrecs; top_level = _43_133.top_level; check_uvars = _43_133.check_uvars; use_eq = _43_133.use_eq; is_iface = _43_133.is_iface; admit = _43_133.admit; default_effects = _43_133.default_effects}))))

let reset_mark = (fun env -> (let _43_136 = (env.solver.reset_mark "USER MARK")
in (let _43_138 = env
in (let _96_328 = (FStar_List.tl env.sigtab)
in {solver = _43_138.solver; range = _43_138.range; curmodule = _43_138.curmodule; gamma = _43_138.gamma; modules = _43_138.modules; expected_typ = _43_138.expected_typ; level = _43_138.level; sigtab = _96_328; is_pattern = _43_138.is_pattern; instantiate_targs = _43_138.instantiate_targs; instantiate_vargs = _43_138.instantiate_vargs; effects = _43_138.effects; generalize = _43_138.generalize; letrecs = _43_138.letrecs; top_level = _43_138.top_level; check_uvars = _43_138.check_uvars; use_eq = _43_138.use_eq; is_iface = _43_138.is_iface; admit = _43_138.admit; default_effects = _43_138.default_effects}))))

let pop = (fun env msg -> (match (env.sigtab) with
| ([]) | (_::[]) -> begin
(FStar_All.failwith "Too many pops")
end
| _43_148::tl -> begin
(let _43_150 = (env.solver.pop msg)
in (let _43_152 = env
in {solver = _43_152.solver; range = _43_152.range; curmodule = _43_152.curmodule; gamma = _43_152.gamma; modules = _43_152.modules; expected_typ = _43_152.expected_typ; level = _43_152.level; sigtab = tl; is_pattern = _43_152.is_pattern; instantiate_targs = _43_152.instantiate_targs; instantiate_vargs = _43_152.instantiate_vargs; effects = _43_152.effects; generalize = _43_152.generalize; letrecs = _43_152.letrecs; top_level = _43_152.top_level; check_uvars = _43_152.check_uvars; use_eq = _43_152.use_eq; is_iface = _43_152.is_iface; admit = _43_152.admit; default_effects = _43_152.default_effects}))
end))

let initial_env = (fun solver module_lid -> (let _96_338 = (let _96_337 = (new_sigtab ())
in (_96_337)::[])
in {solver = solver; range = FStar_Absyn_Syntax.dummyRange; curmodule = module_lid; gamma = []; modules = []; expected_typ = None; level = Expr; sigtab = _96_338; is_pattern = false; instantiate_targs = true; instantiate_vargs = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = true; check_uvars = false; use_eq = false; is_iface = false; admit = false; default_effects = []}))

let effect_decl_opt = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname l)))))

let name_not_found = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))

let variable_not_found = (fun v -> (let _96_347 = (FStar_Absyn_Print.strBvd v)
in (FStar_Util.format1 "Variable \"%s\" not found" _96_347)))

let get_effect_decl = (fun env l -> (match ((effect_decl_opt env l)) with
| None -> begin
(let _96_354 = (let _96_353 = (let _96_352 = (name_not_found l)
in (_96_352, (FStar_Ident.range_of_lid l)))
in FStar_Absyn_Syntax.Error (_96_353))
in (Prims.raise _96_354))
end
| Some (md) -> begin
md
end))

let join = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
(l1, (fun t wp -> wp), (fun t wp -> wp))
end else begin
(match ((FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun _43_181 -> (match (_43_181) with
| (m1, m2, _43_176, _43_178, _43_180) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))) with
| None -> begin
(let _96_410 = (let _96_409 = (let _96_408 = (let _96_407 = (FStar_Absyn_Print.sli l1)
in (let _96_406 = (FStar_Absyn_Print.sli l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" _96_407 _96_406)))
in (_96_408, env.range))
in FStar_Absyn_Syntax.Error (_96_409))
in (Prims.raise _96_410))
end
| Some (_43_184, _43_186, m3, j1, j2) -> begin
(m3, j1, j2)
end)
end)

let monad_leq = (fun env l1 l2 -> if (FStar_Ident.lid_equals l1 l2) then begin
Some ({msource = l1; mtarget = l2; mlift = (fun t wp -> wp)})
end else begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end)

let wp_sig_aux = (fun decls m -> (match ((FStar_All.pipe_right decls (FStar_Util.find_opt (fun d -> (FStar_Ident.lid_equals d.FStar_Absyn_Syntax.mname m))))) with
| None -> begin
(let _96_425 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (FStar_All.failwith _96_425))
end
| Some (md) -> begin
(match (md.FStar_Absyn_Syntax.signature.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow ((FStar_Util.Inl (a), _43_217)::(FStar_Util.Inl (wp), _43_212)::(FStar_Util.Inl (wlp), _43_207)::[], {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Kind_effect; FStar_Absyn_Syntax.tk = _43_227; FStar_Absyn_Syntax.pos = _43_225; FStar_Absyn_Syntax.fvs = _43_223; FStar_Absyn_Syntax.uvs = _43_221}) -> begin
(a, wp.FStar_Absyn_Syntax.sort)
end
| _43_233 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let wp_signature = (fun env m -> (wp_sig_aux env.effects.decls m))

let default_effect = (fun env l -> (FStar_Util.find_map env.default_effects (fun _43_240 -> (match (_43_240) with
| (l', m) -> begin
if (FStar_Ident.lid_equals l l') then begin
Some (m)
end else begin
None
end
end))))

let build_lattice = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_effect_abbrev (l, _43_245, c, quals, r) -> begin
(match ((FStar_Util.find_map quals (fun _43_2 -> (match (_43_2) with
| FStar_Absyn_Syntax.DefaultEffect (n) -> begin
n
end
| _43_255 -> begin
None
end)))) with
| None -> begin
env
end
| Some (e) -> begin
(let _43_259 = env
in {solver = _43_259.solver; range = _43_259.range; curmodule = _43_259.curmodule; gamma = _43_259.gamma; modules = _43_259.modules; expected_typ = _43_259.expected_typ; level = _43_259.level; sigtab = _43_259.sigtab; is_pattern = _43_259.is_pattern; instantiate_targs = _43_259.instantiate_targs; instantiate_vargs = _43_259.instantiate_vargs; effects = _43_259.effects; generalize = _43_259.generalize; letrecs = _43_259.letrecs; top_level = _43_259.top_level; check_uvars = _43_259.check_uvars; use_eq = _43_259.use_eq; is_iface = _43_259.is_iface; admit = _43_259.admit; default_effects = ((e, l))::env.default_effects})
end)
end
| FStar_Absyn_Syntax.Sig_new_effect (ne, _43_263) -> begin
(let effects = (let _43_266 = env.effects
in {decls = (ne)::env.effects.decls; order = _43_266.order; joins = _43_266.joins})
in (let _43_269 = env
in {solver = _43_269.solver; range = _43_269.range; curmodule = _43_269.curmodule; gamma = _43_269.gamma; modules = _43_269.modules; expected_typ = _43_269.expected_typ; level = _43_269.level; sigtab = _43_269.sigtab; is_pattern = _43_269.is_pattern; instantiate_targs = _43_269.instantiate_targs; instantiate_vargs = _43_269.instantiate_vargs; effects = effects; generalize = _43_269.generalize; letrecs = _43_269.letrecs; top_level = _43_269.top_level; check_uvars = _43_269.check_uvars; use_eq = _43_269.use_eq; is_iface = _43_269.is_iface; admit = _43_269.admit; default_effects = _43_269.default_effects}))
end
| FStar_Absyn_Syntax.Sig_sub_effect (sub, _43_273) -> begin
(let compose_edges = (fun e1 e2 -> {msource = e1.msource; mtarget = e2.mtarget; mlift = (fun r wp1 -> (let _96_446 = (e1.mlift r wp1)
in (e2.mlift r _96_446)))})
in (let mk_lift = (fun lift_t r wp1 -> (FStar_Absyn_Syntax.mk_Typ_app (lift_t, ((FStar_Absyn_Syntax.targ r))::((FStar_Absyn_Syntax.targ wp1))::[]) None wp1.FStar_Absyn_Syntax.pos))
in (let edge = {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (mk_lift sub.FStar_Absyn_Syntax.lift)}
in (let id_edge = (fun l -> {msource = sub.FStar_Absyn_Syntax.source; mtarget = sub.FStar_Absyn_Syntax.target; mlift = (fun t wp -> wp)})
in (let print_mlift = (fun l -> (let arg = (let _96_469 = (FStar_Absyn_Syntax.lid_of_path (("ARG")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _96_469 FStar_Absyn_Syntax.mk_Kind_type))
in (let wp = (let _96_470 = (FStar_Absyn_Syntax.lid_of_path (("WP")::[]) FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Util.ftv _96_470 FStar_Absyn_Syntax.mk_Kind_unknown))
in (let _96_471 = (l arg wp)
in (FStar_Absyn_Print.typ_to_string _96_471)))))
in (let order = (edge)::env.effects.order
in (let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun e -> e.FStar_Absyn_Syntax.mname)))
in (let find_edge = (fun order _43_301 -> (match (_43_301) with
| (i, j) -> begin
if (FStar_Ident.lid_equals i j) then begin
(FStar_All.pipe_right (id_edge i) (fun _96_477 -> Some (_96_477)))
end else begin
(FStar_All.pipe_right order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end
end))
in (let order = (FStar_All.pipe_right ms (FStar_List.fold_left (fun order k -> (let _96_485 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> if (FStar_Ident.lid_equals i k) then begin
[]
end else begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> if (FStar_Ident.lid_equals j k) then begin
[]
end else begin
(match ((let _96_484 = (find_edge order (i, k))
in (let _96_483 = (find_edge order (k, j))
in (_96_484, _96_483)))) with
| (Some (e1), Some (e2)) -> begin
((compose_edges e1 e2))::[]
end
| _43_313 -> begin
[]
end)
end)))
end)))
in (FStar_List.append order _96_485))) order))
in (let order = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order)
in (let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (let join_opt = (FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (match ((let _96_493 = (find_edge order (i, k))
in (let _96_492 = (find_edge order (j, k))
in (_96_493, _96_492)))) with
| (Some (ik), Some (jk)) -> begin
(match (bopt) with
| None -> begin
Some ((k, ik, jk))
end
| Some (ub, _43_330, _43_332) -> begin
if ((let _96_494 = (find_edge order (k, ub))
in (FStar_Util.is_some _96_494)) && (not ((let _96_495 = (find_edge order (ub, k))
in (FStar_Util.is_some _96_495))))) then begin
Some ((k, ik, jk))
end else begin
bopt
end
end)
end
| _43_336 -> begin
bopt
end)) None))
in (match (join_opt) with
| None -> begin
[]
end
| Some (k, e1, e2) -> begin
((i, j, k, e1.mlift, e2.mlift))::[]
end))))))))
in (let effects = (let _43_345 = env.effects
in {decls = _43_345.decls; order = order; joins = joins})
in (let _43_348 = env
in {solver = _43_348.solver; range = _43_348.range; curmodule = _43_348.curmodule; gamma = _43_348.gamma; modules = _43_348.modules; expected_typ = _43_348.expected_typ; level = _43_348.level; sigtab = _43_348.sigtab; is_pattern = _43_348.is_pattern; instantiate_targs = _43_348.instantiate_targs; instantiate_vargs = _43_348.instantiate_vargs; effects = effects; generalize = _43_348.generalize; letrecs = _43_348.letrecs; top_level = _43_348.top_level; check_uvars = _43_348.check_uvars; use_eq = _43_348.use_eq; is_iface = _43_348.is_iface; admit = _43_348.admit; default_effects = _43_348.default_effects})))))))))))))
end
| _43_351 -> begin
env
end))

let rec add_sigelt = (fun env se -> (match (se) with
| FStar_Absyn_Syntax.Sig_bundle (ses, _43_356, _43_358, _43_360) -> begin
(add_sigelts env ses)
end
| _43_364 -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_List.iter (fun l -> (let _96_503 = (sigtab env)
in (FStar_Util.smap_add _96_503 l.FStar_Ident.str se))) lids))
end))
and add_sigelts = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))

let empty_lid = (FStar_Absyn_Syntax.lid_of_ids (((FStar_Absyn_Syntax.id_of_text ""))::[]))

let finish_module = (fun env m -> (let sigs = if (FStar_Ident.lid_equals m.FStar_Absyn_Syntax.name FStar_Absyn_Const.prims_lid) then begin
(FStar_All.pipe_right env.gamma (FStar_List.collect (fun _43_3 -> (match (_43_3) with
| Binding_sig (se) -> begin
(se)::[]
end
| _43_375 -> begin
[]
end))))
end else begin
m.FStar_Absyn_Syntax.exports
end
in (let _43_377 = (add_sigelts env sigs)
in (let _43_379 = env
in {solver = _43_379.solver; range = _43_379.range; curmodule = empty_lid; gamma = []; modules = (m)::env.modules; expected_typ = _43_379.expected_typ; level = _43_379.level; sigtab = _43_379.sigtab; is_pattern = _43_379.is_pattern; instantiate_targs = _43_379.instantiate_targs; instantiate_vargs = _43_379.instantiate_vargs; effects = _43_379.effects; generalize = _43_379.generalize; letrecs = _43_379.letrecs; top_level = _43_379.top_level; check_uvars = _43_379.check_uvars; use_eq = _43_379.use_eq; is_iface = _43_379.is_iface; admit = _43_379.admit; default_effects = _43_379.default_effects}))))

let set_level = (fun env level -> (let _43_383 = env
in {solver = _43_383.solver; range = _43_383.range; curmodule = _43_383.curmodule; gamma = _43_383.gamma; modules = _43_383.modules; expected_typ = _43_383.expected_typ; level = level; sigtab = _43_383.sigtab; is_pattern = _43_383.is_pattern; instantiate_targs = _43_383.instantiate_targs; instantiate_vargs = _43_383.instantiate_vargs; effects = _43_383.effects; generalize = _43_383.generalize; letrecs = _43_383.letrecs; top_level = _43_383.top_level; check_uvars = _43_383.check_uvars; use_eq = _43_383.use_eq; is_iface = _43_383.is_iface; admit = _43_383.admit; default_effects = _43_383.default_effects}))

let is_level = (fun env level -> (env.level = level))

let modules = (fun env -> env.modules)

let current_module = (fun env -> env.curmodule)

let set_current_module = (fun env lid -> (let _43_391 = env
in {solver = _43_391.solver; range = _43_391.range; curmodule = lid; gamma = _43_391.gamma; modules = _43_391.modules; expected_typ = _43_391.expected_typ; level = _43_391.level; sigtab = _43_391.sigtab; is_pattern = _43_391.is_pattern; instantiate_targs = _43_391.instantiate_targs; instantiate_vargs = _43_391.instantiate_vargs; effects = _43_391.effects; generalize = _43_391.generalize; letrecs = _43_391.letrecs; top_level = _43_391.top_level; check_uvars = _43_391.check_uvars; use_eq = _43_391.use_eq; is_iface = _43_391.is_iface; admit = _43_391.admit; default_effects = _43_391.default_effects}))

let set_range = (fun e r -> if (r = FStar_Absyn_Syntax.dummyRange) then begin
e
end else begin
(let _43_395 = e
in {solver = _43_395.solver; range = r; curmodule = _43_395.curmodule; gamma = _43_395.gamma; modules = _43_395.modules; expected_typ = _43_395.expected_typ; level = _43_395.level; sigtab = _43_395.sigtab; is_pattern = _43_395.is_pattern; instantiate_targs = _43_395.instantiate_targs; instantiate_vargs = _43_395.instantiate_vargs; effects = _43_395.effects; generalize = _43_395.generalize; letrecs = _43_395.letrecs; top_level = _43_395.top_level; check_uvars = _43_395.check_uvars; use_eq = _43_395.use_eq; is_iface = _43_395.is_iface; admit = _43_395.admit; default_effects = _43_395.default_effects})
end)

let get_range = (fun e -> e.range)

let find_in_sigtab = (fun env lid -> (let _96_537 = (sigtab env)
in (FStar_Util.smap_try_find _96_537 (FStar_Ident.text_of_lid lid))))

let lookup_bvvdef = (fun env bvvd -> (FStar_Util.find_map env.gamma (fun _43_4 -> (match (_43_4) with
| Binding_var (id, t) when (FStar_Absyn_Util.bvd_eq id bvvd) -> begin
Some (t)
end
| _43_408 -> begin
None
end))))

let lookup_bvar = (fun env bv -> (match ((lookup_bvvdef env bv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _96_549 = (let _96_548 = (let _96_547 = (variable_not_found bv.FStar_Absyn_Syntax.v)
in (_96_547, (FStar_Absyn_Util.range_of_bvd bv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_96_548))
in (Prims.raise _96_549))
end
| Some (t) -> begin
t
end))

let in_cur_mod = (fun env l -> (let cur = (current_module env)
in if (l.FStar_Ident.nsstr = cur.FStar_Ident.str) then begin
true
end else begin
if (FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str) then begin
(let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (let cur = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (let rec aux = (fun c l -> (match ((c, l)) with
| ([], _43_424) -> begin
true
end
| (_43_427, []) -> begin
false
end
| (hd::tl, hd'::tl') when (hd.FStar_Ident.idText = hd'.FStar_Ident.idText) -> begin
(aux tl tl')
end
| _43_438 -> begin
false
end))
in (aux cur lns))))
end else begin
false
end
end))

let lookup_qname = (fun env lid -> (let cur_mod = (in_cur_mod env lid)
in (let found = if cur_mod then begin
(FStar_Util.find_map env.gamma (fun _43_5 -> (match (_43_5) with
| Binding_lid (l, t) -> begin
if (FStar_Ident.lid_equals lid l) then begin
Some (FStar_Util.Inl (t))
end else begin
None
end
end
| Binding_sig (FStar_Absyn_Syntax.Sig_bundle (ses, _43_449, _43_451, _43_453)) -> begin
(FStar_Util.find_map ses (fun se -> if (let _96_564 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _96_564 (FStar_Util.for_some (FStar_Ident.lid_equals lid)))) then begin
Some (FStar_Util.Inr (se))
end else begin
None
end))
end
| Binding_sig (s) -> begin
(let lids = (FStar_Absyn_Util.lids_of_sigelt s)
in if (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals lid))) then begin
Some (FStar_Util.Inr (s))
end else begin
None
end)
end
| _43_462 -> begin
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

let lookup_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_43_470, t, (_43_473, tps, _43_476), _43_479, _43_481, _43_483))) -> begin
(let _96_570 = (FStar_List.map (fun _43_491 -> (match (_43_491) with
| (x, _43_490) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _96_570 t))
end
| _43_493 -> begin
(let _96_573 = (let _96_572 = (let _96_571 = (name_not_found lid)
in (_96_571, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_96_572))
in (Prims.raise _96_573))
end))

let lookup_kind_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_kind_abbrev (l, binders, k, _43_500))) -> begin
(l, binders, k)
end
| _43_506 -> begin
(let _96_580 = (let _96_579 = (let _96_578 = (name_not_found lid)
in (_96_578, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_96_579))
in (Prims.raise _96_580))
end))

let lookup_projector = (fun env lid i -> (let fail = (fun _43_511 -> (match (()) with
| () -> begin
(let _96_591 = (let _96_590 = (FStar_Util.string_of_int i)
in (let _96_589 = (FStar_Absyn_Print.sli lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" _96_590 _96_589)))
in (FStar_All.failwith _96_591))
end))
in (let t = (lookup_datacon env lid)
in (match ((let _96_592 = (FStar_Absyn_Util.compress_typ t)
in _96_592.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _43_515) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _96_593 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (FStar_All.pipe_right _96_593 Prims.fst))
end
| FStar_Util.Inr (x) -> begin
(let _96_594 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (FStar_All.pipe_right _96_594 Prims.fst))
end))
end
end
| _43_524 -> begin
(fail ())
end))))

let try_lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_43_528, t, q, _43_532))) -> begin
Some ((t, q))
end
| _43_538 -> begin
None
end))

let lookup_val_decl = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_43_542, t, _43_545, _43_547))) -> begin
t
end
| _43_553 -> begin
(let _96_605 = (let _96_604 = (let _96_603 = (name_not_found lid)
in (_96_603, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_96_604))
in (Prims.raise _96_605))
end))

let lookup_lid = (fun env lid -> (let not_found = (fun _43_557 -> (match (()) with
| () -> begin
(let _96_614 = (let _96_613 = (let _96_612 = (name_not_found lid)
in (_96_612, (FStar_Ident.range_of_lid lid)))
in FStar_Absyn_Syntax.Error (_96_613))
in (Prims.raise _96_614))
end))
in (let mapper = (fun _43_6 -> (match (_43_6) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_43_560, t, (_43_563, tps, _43_566), _43_569, _43_571, _43_573)) -> begin
(let _96_619 = (let _96_618 = (FStar_List.map (fun _43_580 -> (match (_43_580) with
| (x, _43_579) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _96_618 t))
in Some (_96_619))
end
| FStar_Util.Inl (t) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (l, t, qs, _43_587)) -> begin
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
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_43_592, {FStar_Absyn_Syntax.lbname = _43_599; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = _43_596; FStar_Absyn_Syntax.lbdef = _43_594}::[]), _43_604, _43_606, _43_608)) -> begin
Some (t)
end
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_let ((_43_613, lbs), _43_617, _43_619, _43_621)) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inl (_43_627) -> begin
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
in (match ((let _96_621 = (lookup_qname env lid)
in (FStar_Util.bind_opt _96_621 mapper))) with
| Some (t) -> begin
(let _43_635 = t
in {FStar_Absyn_Syntax.n = _43_635.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _43_635.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = (FStar_Absyn_Syntax.range_of_lid lid); FStar_Absyn_Syntax.fvs = _43_635.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _43_635.FStar_Absyn_Syntax.uvs})
end
| None -> begin
(not_found ())
end))))

let is_datacon = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_43_641, _43_643, quals, _43_646))) -> begin
(FStar_All.pipe_right quals (FStar_Util.for_some (fun _43_7 -> (match (_43_7) with
| FStar_Absyn_Syntax.Assumption -> begin
true
end
| _43_654 -> begin
false
end))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_datacon (_43_656, t, _43_659, _43_661, _43_663, _43_665))) -> begin
true
end
| _43_671 -> begin
false
end))

let is_record = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_43_675, _43_677, _43_679, _43_681, _43_683, tags, _43_686))) -> begin
(FStar_Util.for_some (fun _43_8 -> (match (_43_8) with
| (FStar_Absyn_Syntax.RecordType (_)) | (FStar_Absyn_Syntax.RecordConstructor (_)) -> begin
true
end
| _43_699 -> begin
false
end)) tags)
end
| _43_701 -> begin
false
end))

let lookup_datacons_of_typ = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_43_705, _43_707, _43_709, _43_711, datas, _43_714, _43_716))) -> begin
(let _96_638 = (FStar_List.map (fun l -> (let _96_637 = (lookup_lid env l)
in (l, _96_637))) datas)
in Some (_96_638))
end
| _43_723 -> begin
None
end))

let lookup_effect_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, c, quals, _43_731))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _43_9 -> (match (_43_9) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _43_739 -> begin
false
end)))) then begin
None
end else begin
Some ((binders, c))
end
end
| _43_741 -> begin
None
end))

let lookup_typ_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _43_747, t, quals, _43_751))) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _43_10 -> (match (_43_10) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _43_759 -> begin
false
end)))) then begin
None
end else begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _96_649 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_96_649)))
end
end
| _43_762 -> begin
None
end))

let lookup_opaque_typ_abbrev = (fun env lid -> (match ((lookup_qname env lid)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _43_768, t, quals, _43_772))) -> begin
(let t = (FStar_Absyn_Util.close_with_lam tps t)
in (let _96_654 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_named ((t, lid))))
in Some (_96_654)))
end
| _43_779 -> begin
None
end))

let lookup_btvdef = (fun env btvd -> (FStar_Util.find_map env.gamma (fun _43_11 -> (match (_43_11) with
| Binding_typ (id, k) when (FStar_Absyn_Util.bvd_eq id btvd) -> begin
Some (k)
end
| _43_788 -> begin
None
end))))

let lookup_btvar = (fun env btv -> (match ((lookup_btvdef env btv.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _96_666 = (let _96_665 = (let _96_664 = (variable_not_found btv.FStar_Absyn_Syntax.v)
in (_96_664, (FStar_Absyn_Util.range_of_bvd btv.FStar_Absyn_Syntax.v)))
in FStar_Absyn_Syntax.Error (_96_665))
in (Prims.raise _96_666))
end
| Some (k) -> begin
k
end))

let lookup_typ_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (lid, tps, k, _, _, _, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, k, _, _, _)))) -> begin
(FStar_Absyn_Util.close_kind tps k)
end
| _43_822 -> begin
(let _96_673 = (let _96_672 = (let _96_671 = (name_not_found ftv)
in (_96_671, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_96_672))
in (Prims.raise _96_673))
end))

let is_projector = (fun env l -> (match ((lookup_qname env l)) with
| (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, quals, _)))) | (Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_val_decl (_, _, quals, _)))) -> begin
(FStar_Util.for_some (fun _43_12 -> (match (_43_12) with
| FStar_Absyn_Syntax.Projector (_43_854) -> begin
true
end
| _43_857 -> begin
false
end)) quals)
end
| _43_859 -> begin
false
end))

let try_lookup_effect_lid = (fun env ftv -> (match ((lookup_qname env ftv)) with
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_new_effect (ne, _43_864))) -> begin
(let _96_684 = (FStar_Absyn_Util.close_kind ne.FStar_Absyn_Syntax.binders ne.FStar_Absyn_Syntax.signature)
in (FStar_All.pipe_right _96_684 (fun _96_683 -> Some (_96_683))))
end
| Some (FStar_Util.Inr (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, binders, _43_872, _43_874, _43_876))) -> begin
(let _96_686 = (FStar_Absyn_Util.close_kind binders FStar_Absyn_Syntax.mk_Kind_effect)
in (FStar_All.pipe_right _96_686 (fun _96_685 -> Some (_96_685))))
end
| _43_882 -> begin
None
end))

let lookup_effect_lid = (fun env ftv -> (match ((try_lookup_effect_lid env ftv)) with
| None -> begin
(let _96_693 = (let _96_692 = (let _96_691 = (name_not_found ftv)
in (_96_691, (FStar_Ident.range_of_lid ftv)))
in FStar_Absyn_Syntax.Error (_96_692))
in (Prims.raise _96_693))
end
| Some (k) -> begin
k
end))

let lookup_operator = (fun env opname -> (let primName = (FStar_Ident.lid_of_path (("Prims")::((Prims.strcat "_dummy_" opname.FStar_Ident.idText))::[]) FStar_Absyn_Syntax.dummyRange)
in (lookup_lid env primName)))

let push_sigelt = (fun env s -> (build_lattice (let _43_893 = env
in {solver = _43_893.solver; range = _43_893.range; curmodule = _43_893.curmodule; gamma = (Binding_sig (s))::env.gamma; modules = _43_893.modules; expected_typ = _43_893.expected_typ; level = _43_893.level; sigtab = _43_893.sigtab; is_pattern = _43_893.is_pattern; instantiate_targs = _43_893.instantiate_targs; instantiate_vargs = _43_893.instantiate_vargs; effects = _43_893.effects; generalize = _43_893.generalize; letrecs = _43_893.letrecs; top_level = _43_893.top_level; check_uvars = _43_893.check_uvars; use_eq = _43_893.use_eq; is_iface = _43_893.is_iface; admit = _43_893.admit; default_effects = _43_893.default_effects}) s))

let push_local_binding = (fun env b -> (let _43_897 = env
in {solver = _43_897.solver; range = _43_897.range; curmodule = _43_897.curmodule; gamma = (b)::env.gamma; modules = _43_897.modules; expected_typ = _43_897.expected_typ; level = _43_897.level; sigtab = _43_897.sigtab; is_pattern = _43_897.is_pattern; instantiate_targs = _43_897.instantiate_targs; instantiate_vargs = _43_897.instantiate_vargs; effects = _43_897.effects; generalize = _43_897.generalize; letrecs = _43_897.letrecs; top_level = _43_897.top_level; check_uvars = _43_897.check_uvars; use_eq = _43_897.use_eq; is_iface = _43_897.is_iface; admit = _43_897.admit; default_effects = _43_897.default_effects}))

let uvars_in_env = (fun env -> (let no_uvs = (let _96_710 = (FStar_Absyn_Syntax.new_uv_set ())
in (let _96_709 = (FStar_Absyn_Syntax.new_uvt_set ())
in (let _96_708 = (FStar_Absyn_Syntax.new_uvt_set ())
in {FStar_Absyn_Syntax.uvars_k = _96_710; FStar_Absyn_Syntax.uvars_t = _96_709; FStar_Absyn_Syntax.uvars_e = _96_708})))
in (let ext = (fun out uvs -> (let _43_904 = out
in (let _96_717 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_k uvs.FStar_Absyn_Syntax.uvars_k)
in (let _96_716 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_t uvs.FStar_Absyn_Syntax.uvars_t)
in (let _96_715 = (FStar_Util.set_union out.FStar_Absyn_Syntax.uvars_e uvs.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _96_717; FStar_Absyn_Syntax.uvars_t = _96_716; FStar_Absyn_Syntax.uvars_e = _96_715})))))
in (let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_lid (_, t)::tl) | (Binding_var (_, t)::tl) -> begin
(let _96_723 = (let _96_722 = (FStar_Absyn_Util.uvars_in_typ t)
in (ext out _96_722))
in (aux _96_723 tl))
end
| Binding_typ (_43_924, k)::tl -> begin
(let _96_725 = (let _96_724 = (FStar_Absyn_Util.uvars_in_kind k)
in (ext out _96_724))
in (aux _96_725 tl))
end
| Binding_sig (_43_932)::_43_930 -> begin
out
end))
in (aux no_uvs env.gamma)))))

let push_module = (fun env m -> (let _43_937 = (add_sigelts env m.FStar_Absyn_Syntax.exports)
in (let _43_939 = env
in {solver = _43_939.solver; range = _43_939.range; curmodule = _43_939.curmodule; gamma = []; modules = (m)::env.modules; expected_typ = None; level = _43_939.level; sigtab = _43_939.sigtab; is_pattern = _43_939.is_pattern; instantiate_targs = _43_939.instantiate_targs; instantiate_vargs = _43_939.instantiate_vargs; effects = _43_939.effects; generalize = _43_939.generalize; letrecs = _43_939.letrecs; top_level = _43_939.top_level; check_uvars = _43_939.check_uvars; use_eq = _43_939.use_eq; is_iface = _43_939.is_iface; admit = _43_939.admit; default_effects = _43_939.default_effects})))

let set_expected_typ = (fun env t -> (let _43_943 = env
in {solver = _43_943.solver; range = _43_943.range; curmodule = _43_943.curmodule; gamma = _43_943.gamma; modules = _43_943.modules; expected_typ = Some (t); level = _43_943.level; sigtab = _43_943.sigtab; is_pattern = _43_943.is_pattern; instantiate_targs = _43_943.instantiate_targs; instantiate_vargs = _43_943.instantiate_vargs; effects = _43_943.effects; generalize = _43_943.generalize; letrecs = _43_943.letrecs; top_level = _43_943.top_level; check_uvars = _43_943.check_uvars; use_eq = false; is_iface = _43_943.is_iface; admit = _43_943.admit; default_effects = _43_943.default_effects}))

let expected_typ = (fun env -> (match (env.expected_typ) with
| None -> begin
None
end
| Some (t) -> begin
Some (t)
end))

let clear_expected_typ = (fun env -> (let _96_738 = (expected_typ env)
in ((let _43_950 = env
in {solver = _43_950.solver; range = _43_950.range; curmodule = _43_950.curmodule; gamma = _43_950.gamma; modules = _43_950.modules; expected_typ = None; level = _43_950.level; sigtab = _43_950.sigtab; is_pattern = _43_950.is_pattern; instantiate_targs = _43_950.instantiate_targs; instantiate_vargs = _43_950.instantiate_vargs; effects = _43_950.effects; generalize = _43_950.generalize; letrecs = _43_950.letrecs; top_level = _43_950.top_level; check_uvars = _43_950.check_uvars; use_eq = false; is_iface = _43_950.is_iface; admit = _43_950.admit; default_effects = _43_950.default_effects}), _96_738)))

let fold_env = (fun env f a -> (FStar_List.fold_right (fun e a -> (f a e)) env.gamma a))

let binding_of_binder = (fun b -> (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
Binding_typ ((a.FStar_Absyn_Syntax.v, a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))
end))

let binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (x, t) -> begin
(let _96_756 = (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_96_756)::out)
end
| Binding_typ (a, k) -> begin
(let _96_757 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_96_757)::out)
end
| _43_974 -> begin
out
end)) [] env.gamma))

let t_binders = (fun env -> (FStar_List.fold_left (fun out b -> (match (b) with
| Binding_var (_43_979) -> begin
out
end
| Binding_typ (a, k) -> begin
(let _96_762 = (FStar_All.pipe_left FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_96_762)::out)
end
| _43_986 -> begin
out
end)) [] env.gamma))

let idents = (fun env -> (let _96_766 = (let _96_765 = (binders env)
in (FStar_All.pipe_right _96_765 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Syntax.freevars_of_list _96_766)))

let lidents = (fun env -> (let keys = (FStar_List.fold_left (fun keys _43_13 -> (match (_43_13) with
| Binding_sig (s) -> begin
(let _96_771 = (FStar_Absyn_Util.lids_of_sigelt s)
in (FStar_List.append _96_771 keys))
end
| _43_994 -> begin
keys
end)) [] env.gamma)
in (let _96_776 = (sigtab env)
in (FStar_Util.smap_fold _96_776 (fun _43_996 v keys -> (let _96_775 = (FStar_Absyn_Util.lids_of_sigelt v)
in (FStar_List.append _96_775 keys))) keys))))




