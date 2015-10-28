
open Prims
type other_info =
Prims.nat

type varname =
Prims.string

type const =
| C_prin of Prins.prin
| C_eprins of Prins.eprins
| C_unit of Prims.unit
| C_bool of Prims.bool
| C_opaque of Prims.unit * Obj.t

let is_C_prin = (fun _discr_ -> (match (_discr_) with
| C_prin (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_eprins = (fun _discr_ -> (match (_discr_) with
| C_eprins (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_unit = (fun _discr_ -> (match (_discr_) with
| C_unit (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_bool = (fun _discr_ -> (match (_discr_) with
| C_bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_C_opaque = (fun _discr_ -> (match (_discr_) with
| C_opaque (_) -> begin
true
end
| _ -> begin
false
end))

let ___C_prin___c = (fun projectee -> (match (projectee) with
| C_prin (_18_11) -> begin
_18_11
end))

let ___C_eprins___c = (fun projectee -> (match (projectee) with
| C_eprins (_18_14) -> begin
_18_14
end))

let ___C_unit___c = (fun projectee -> ())

let ___C_bool___c = (fun projectee -> (match (projectee) with
| C_bool (_18_20) -> begin
_18_20
end))

let ___C_opaque___c = (fun projectee -> (match (projectee) with
| C_opaque (_, _18_23) -> begin
(Obj.magic _18_23)
end))

type exp =
| E_aspar of exp * exp
| E_assec of exp * exp
| E_box of exp * exp
| E_unbox of exp
| E_mkwire of exp * exp
| E_projwire of exp * exp
| E_concatwire of exp * exp
| E_const of const
| E_var of varname
| E_let of varname * exp * exp
| E_abs of varname * exp
| E_fix of varname * varname * exp
| E_empabs of varname * exp
| E_app of exp * exp
| E_ffi of Prims.unit * Prims.unit * Prims.nat * Prims.string * Obj.t * exp Prims.list * Obj.t
| E_cond of exp * exp * exp

let is_E_aspar = (fun _discr_ -> (match (_discr_) with
| E_aspar (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_assec = (fun _discr_ -> (match (_discr_) with
| E_assec (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_box = (fun _discr_ -> (match (_discr_) with
| E_box (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_unbox = (fun _discr_ -> (match (_discr_) with
| E_unbox (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_mkwire = (fun _discr_ -> (match (_discr_) with
| E_mkwire (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_projwire = (fun _discr_ -> (match (_discr_) with
| E_projwire (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_concatwire = (fun _discr_ -> (match (_discr_) with
| E_concatwire (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_const = (fun _discr_ -> (match (_discr_) with
| E_const (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_var = (fun _discr_ -> (match (_discr_) with
| E_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_let = (fun _discr_ -> (match (_discr_) with
| E_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_abs = (fun _discr_ -> (match (_discr_) with
| E_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_fix = (fun _discr_ -> (match (_discr_) with
| E_fix (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_empabs = (fun _discr_ -> (match (_discr_) with
| E_empabs (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_app = (fun _discr_ -> (match (_discr_) with
| E_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_ffi = (fun _discr_ -> (match (_discr_) with
| E_ffi (_) -> begin
true
end
| _ -> begin
false
end))

let is_E_cond = (fun _discr_ -> (match (_discr_) with
| E_cond (_) -> begin
true
end
| _ -> begin
false
end))

let ___E_aspar___ps = (fun projectee -> (match (projectee) with
| E_aspar (_18_64, _18_65) -> begin
_18_64
end))

let ___E_aspar___e = (fun projectee -> (match (projectee) with
| E_aspar (_18_67, _18_66) -> begin
_18_66
end))

let ___E_assec___ps = (fun projectee -> (match (projectee) with
| E_assec (_18_70, _18_71) -> begin
_18_70
end))

let ___E_assec___e = (fun projectee -> (match (projectee) with
| E_assec (_18_73, _18_72) -> begin
_18_72
end))

let ___E_box___ps = (fun projectee -> (match (projectee) with
| E_box (_18_76, _18_77) -> begin
_18_76
end))

let ___E_box___e = (fun projectee -> (match (projectee) with
| E_box (_18_79, _18_78) -> begin
_18_78
end))

let ___E_unbox___e = (fun projectee -> (match (projectee) with
| E_unbox (_18_82) -> begin
_18_82
end))

let ___E_mkwire___e1 = (fun projectee -> (match (projectee) with
| E_mkwire (_18_85, _18_86) -> begin
_18_85
end))

let ___E_mkwire___e2 = (fun projectee -> (match (projectee) with
| E_mkwire (_18_88, _18_87) -> begin
_18_87
end))

let ___E_projwire___e1 = (fun projectee -> (match (projectee) with
| E_projwire (_18_91, _18_92) -> begin
_18_91
end))

let ___E_projwire___e2 = (fun projectee -> (match (projectee) with
| E_projwire (_18_94, _18_93) -> begin
_18_93
end))

let ___E_concatwire___e1 = (fun projectee -> (match (projectee) with
| E_concatwire (_18_97, _18_98) -> begin
_18_97
end))

let ___E_concatwire___e2 = (fun projectee -> (match (projectee) with
| E_concatwire (_18_100, _18_99) -> begin
_18_99
end))

let ___E_const___c = (fun projectee -> (match (projectee) with
| E_const (_18_103) -> begin
_18_103
end))

let ___E_var___x = (fun projectee -> (match (projectee) with
| E_var (_18_106) -> begin
_18_106
end))

let ___E_let___x = (fun projectee -> (match (projectee) with
| E_let (_18_109, _18_110, _18_111) -> begin
_18_109
end))

let ___E_let___e1 = (fun projectee -> (match (projectee) with
| E_let (_18_113, _18_112, _18_114) -> begin
_18_112
end))

let ___E_let___e2 = (fun projectee -> (match (projectee) with
| E_let (_18_116, _18_117, _18_115) -> begin
_18_115
end))

let ___E_abs___x = (fun projectee -> (match (projectee) with
| E_abs (_18_120, _18_121) -> begin
_18_120
end))

let ___E_abs___e = (fun projectee -> (match (projectee) with
| E_abs (_18_123, _18_122) -> begin
_18_122
end))

let ___E_fix___f = (fun projectee -> (match (projectee) with
| E_fix (_18_126, _18_127, _18_128) -> begin
_18_126
end))

let ___E_fix___x = (fun projectee -> (match (projectee) with
| E_fix (_18_130, _18_129, _18_131) -> begin
_18_129
end))

let ___E_fix___e = (fun projectee -> (match (projectee) with
| E_fix (_18_133, _18_134, _18_132) -> begin
_18_132
end))

let ___E_empabs___x = (fun projectee -> (match (projectee) with
| E_empabs (_18_137, _18_138) -> begin
_18_137
end))

let ___E_empabs___e = (fun projectee -> (match (projectee) with
| E_empabs (_18_140, _18_139) -> begin
_18_139
end))

let ___E_app___e1 = (fun projectee -> (match (projectee) with
| E_app (_18_143, _18_144) -> begin
_18_143
end))

let ___E_app___e2 = (fun projectee -> (match (projectee) with
| E_app (_18_146, _18_145) -> begin
_18_145
end))

let ___E_ffi___n = (fun projectee -> (match (projectee) with
| E_ffi (_, _, _18_149, _18_152, _18_153, _18_154, _18_155) -> begin
_18_149
end))

let ___E_ffi___fname = (fun projectee -> (match (projectee) with
| E_ffi (_, _, _18_159, _18_156, _18_160, _18_161, _18_162) -> begin
_18_156
end))

let ___E_ffi___fn = (fun projectee -> (match (projectee) with
| E_ffi (_, _, _18_166, _18_167, _18_163, _18_168, _18_169) -> begin
(Obj.magic _18_163)
end))

let ___E_ffi___args = (fun projectee -> (match (projectee) with
| E_ffi (_, _, _18_173, _18_174, _18_175, _18_170, _18_176) -> begin
_18_170
end))

let ___E_ffi___inj = (fun projectee -> (match (projectee) with
| E_ffi (_, _, _18_180, _18_181, _18_182, _18_183, _18_177) -> begin
(Obj.magic _18_177)
end))

let ___E_cond___e = (fun projectee -> (match (projectee) with
| E_cond (_18_186, _18_187, _18_188) -> begin
_18_186
end))

let ___E_cond___e1 = (fun projectee -> (match (projectee) with
| E_cond (_18_190, _18_189, _18_191) -> begin
_18_189
end))

let ___E_cond___e2 = (fun projectee -> (match (projectee) with
| E_cond (_18_193, _18_194, _18_192) -> begin
_18_192
end))

type canbox =
| Can_b
| Cannot_b

let is_Can_b = (fun _discr_ -> (match (_discr_) with
| Can_b -> begin
true
end
| _ -> begin
false
end))

let is_Cannot_b = (fun _discr_ -> (match (_discr_) with
| Cannot_b -> begin
true
end
| _ -> begin
false
end))

type canwire =
| Can_w
| Cannot_w

let is_Can_w = (fun _discr_ -> (match (_discr_) with
| Can_w -> begin
true
end
| _ -> begin
false
end))

let is_Cannot_w = (fun _discr_ -> (match (_discr_) with
| Cannot_w -> begin
true
end
| _ -> begin
false
end))

type v_meta =
| Meta of Prins.eprins * canbox * Prins.eprins * canwire

let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))

let ___Meta___bps = (fun projectee -> (match (projectee) with
| Meta (_18_200, _18_201, _18_202, _18_203) -> begin
_18_200
end))

let ___Meta___cb = (fun projectee -> (match (projectee) with
| Meta (_18_205, _18_204, _18_206, _18_207) -> begin
_18_204
end))

let ___Meta___wps = (fun projectee -> (match (projectee) with
| Meta (_18_209, _18_210, _18_208, _18_211) -> begin
_18_208
end))

let ___Meta___cw = (fun projectee -> (match (projectee) with
| Meta (_18_213, _18_214, _18_215, _18_212) -> begin
_18_212
end))

let is_meta_wireable = (fun _18_1 -> (match (_18_1) with
| Meta (ps, Can_b, ps', Can_w) -> begin
((ps = (FStar_OrdSet.empty ((fun _18_1 ps ps' -> Prins.p_cmp) _18_1 ps ps'))) && (ps' = (FStar_OrdSet.empty ((fun _18_1 ps ps' -> Prins.p_cmp) _18_1 ps ps'))))
end
| _18_224 -> begin
false
end))

let is_meta_boxable = (fun ps _18_2 -> (match (_18_2) with
| Meta (ps', Can_b, ps'', _18_230) -> begin
((FStar_OrdSet.subset ((fun ps _18_2 ps' ps'' _18_230 -> Prins.p_cmp) ps _18_2 ps' ps'' _18_230) ps' ps) && (FStar_OrdSet.subset ((fun ps _18_2 ps' ps'' _18_230 -> Prins.p_cmp) ps _18_2 ps' ps'' _18_230) ps'' ps))
end
| _18_236 -> begin
false
end))

type 'dummyV1 value =
| V_prin of Prins.prin
| V_eprins of Prins.eprins
| V_unit
| V_bool of Prims.bool
| V_opaque of Prims.unit * Obj.t * v_meta * (Prins.prin  ->  Obj.t  ->  Obj.t) * (Obj.t  ->  Obj.t  ->  Obj.t) * (Prins.prins  ->  Obj.t  ->  Obj.t)
| V_box of v_meta * Prins.prins * Prims.unit value
| V_wire of Prins.eprins * Prims.unit v_wire
| V_clos of env * varname * exp
| V_fix_clos of env * varname * varname * exp
| V_emp_clos of varname * exp
| V_emp 
 and dvalue =
| D_v of v_meta * Prims.unit value 
 and ' eps v_wire =
(Prins.prin, Prims.unit value, Prims.unit) FStar_OrdMap.ordmap 
 and env =
varname  ->  dvalue Prims.option

let is_V_prin = (fun _discr_ -> (match (_discr_) with
| V_prin (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_eprins = (fun _discr_ -> (match (_discr_) with
| V_eprins (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_unit = (fun _discr_ -> (match (_discr_) with
| V_unit -> begin
true
end
| _ -> begin
false
end))

let is_V_bool = (fun _discr_ -> (match (_discr_) with
| V_bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_opaque = (fun _discr_ -> (match (_discr_) with
| V_opaque (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_box = (fun _discr_ -> (match (_discr_) with
| V_box (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_wire = (fun _discr_ -> (match (_discr_) with
| V_wire (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_clos = (fun _discr_ -> (match (_discr_) with
| V_clos (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_fix_clos = (fun _discr_ -> (match (_discr_) with
| V_fix_clos (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_emp_clos = (fun _discr_ -> (match (_discr_) with
| V_emp_clos (_) -> begin
true
end
| _ -> begin
false
end))

let is_V_emp = (fun _discr_ -> (match (_discr_) with
| V_emp -> begin
true
end
| _ -> begin
false
end))

let is_D_v = (fun _discr_ -> (match (_discr_) with
| D_v (_) -> begin
true
end
| _ -> begin
false
end))

let ___V_prin___c = (fun _0 projectee -> (match (projectee) with
| V_prin (_18_268) -> begin
_18_268
end))

let ___V_eprins___c = (fun _0 projectee -> (match (projectee) with
| V_eprins (_18_271) -> begin
_18_271
end))

let ___V_bool___c = (fun _0 projectee -> (match (projectee) with
| V_bool (_18_274) -> begin
_18_274
end))

let ___V_opaque___v = (fun _0 projectee -> (match (projectee) with
| V_opaque (_, _18_277, _18_279, _18_280, _18_281, _18_282) -> begin
(Obj.magic _18_277)
end))

let ___V_opaque___meta = (fun _0 projectee -> (match (projectee) with
| V_opaque (_, _18_285, _18_283, _18_286, _18_287, _18_288) -> begin
_18_283
end))

let ___V_opaque___slice_fn = (fun _0 projectee -> (match (projectee) with
| V_opaque (_, _18_291, _18_292, _18_289, _18_293, _18_294) -> begin
(Obj.magic _18_289)
end))

let ___V_opaque___compose_fn = (fun _0 projectee -> (match (projectee) with
| V_opaque (_, _18_297, _18_298, _18_299, _18_295, _18_300) -> begin
(Obj.magic _18_295)
end))

let ___V_opaque___slice_fn_sps = (fun _0 projectee -> (match (projectee) with
| V_opaque (_, _18_303, _18_304, _18_305, _18_306, _18_301) -> begin
(Obj.magic _18_301)
end))

let ___V_box___meta = (fun _0 projectee -> (match (projectee) with
| V_box (_18_309, _18_310, _18_311) -> begin
_18_309
end))

let ___V_box___ps = (fun _0 projectee -> (match (projectee) with
| V_box (_18_313, _18_312, _18_314) -> begin
_18_312
end))

let ___V_box___v = (fun _0 projectee -> (match (projectee) with
| V_box (_18_316, _18_317, _18_315) -> begin
_18_315
end))

let ___V_wire___eps = (fun _0 projectee -> (match (projectee) with
| V_wire (_18_320, _18_321) -> begin
_18_320
end))

let ___V_wire___m = (fun _0 projectee -> (match (projectee) with
| V_wire (_18_323, _18_322) -> begin
_18_322
end))

let ___V_clos___en = (fun _0 projectee -> (match (projectee) with
| V_clos (_18_326, _18_327, _18_328) -> begin
_18_326
end))

let ___V_clos___x = (fun _0 projectee -> (match (projectee) with
| V_clos (_18_330, _18_329, _18_331) -> begin
_18_329
end))

let ___V_clos___e = (fun _0 projectee -> (match (projectee) with
| V_clos (_18_333, _18_334, _18_332) -> begin
_18_332
end))

let ___V_fix_clos___en = (fun _0 projectee -> (match (projectee) with
| V_fix_clos (_18_337, _18_338, _18_339, _18_340) -> begin
_18_337
end))

let ___V_fix_clos___f = (fun _0 projectee -> (match (projectee) with
| V_fix_clos (_18_342, _18_341, _18_343, _18_344) -> begin
_18_341
end))

let ___V_fix_clos___x = (fun _0 projectee -> (match (projectee) with
| V_fix_clos (_18_346, _18_347, _18_345, _18_348) -> begin
_18_345
end))

let ___V_fix_clos___e = (fun _0 projectee -> (match (projectee) with
| V_fix_clos (_18_350, _18_351, _18_352, _18_349) -> begin
_18_349
end))

let ___V_emp_clos___x = (fun _0 projectee -> (match (projectee) with
| V_emp_clos (_18_355, _18_356) -> begin
_18_355
end))

let ___V_emp_clos___e = (fun _0 projectee -> (match (projectee) with
| V_emp_clos (_18_358, _18_357) -> begin
_18_357
end))

let ___D_v___meta = (fun projectee -> (match (projectee) with
| D_v (_18_360, _18_361) -> begin
_18_360
end))

let ___D_v___v = (fun projectee -> (match (projectee) with
| D_v (_18_363, _18_362) -> begin
_18_362
end))

let preceds_axiom = (Obj.magic (fun en x -> (FStar_All.failwith "Not yet implemented:preceds_axiom")))

type telt =
| Tr_val of v_meta * Prims.unit value
| Tr_scope of Prins.prins * telt Prims.list

let is_Tr_val = (fun _discr_ -> (match (_discr_) with
| Tr_val (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tr_scope = (fun _discr_ -> (match (_discr_) with
| Tr_scope (_) -> begin
true
end
| _ -> begin
false
end))

let ___Tr_val___meta = (fun projectee -> (match (projectee) with
| Tr_val (_18_372, _18_373) -> begin
_18_372
end))

let ___Tr_val___v = (fun projectee -> (match (projectee) with
| Tr_val (_18_375, _18_374) -> begin
_18_374
end))

let ___Tr_scope___ps = (fun projectee -> (match (projectee) with
| Tr_scope (_18_378, _18_379) -> begin
_18_378
end))

let ___Tr_scope___tr = (fun projectee -> (match (projectee) with
| Tr_scope (_18_381, _18_380) -> begin
_18_380
end))

type trace =
telt Prims.list

let rec vals_trace_h = (fun tr -> (match (tr) with
| [] -> begin
true
end
| Tr_val (_18_12378, _18_386)::tl -> begin
(vals_trace_h tl)
end
| _18_390 -> begin
false
end))

let vals_trace = (Obj.magic (fun tr -> (Obj.magic ())))

type redex =
| R_aspar of v_meta * Prins.prins * Prims.unit value
| R_assec of v_meta * Prins.prins * Prims.unit value
| R_box of v_meta * Prins.prins * Prims.unit value
| R_unbox of v_meta * Prims.unit value
| R_mkwire of v_meta * Prins.prins * Prims.unit value
| R_projwire of v_meta * Prins.prin * Prims.unit value
| R_concatwire of v_meta * v_meta * Prims.unit value * Prims.unit value
| R_let of v_meta * varname * Prims.unit value * exp
| R_app of v_meta * v_meta * Prims.unit value * Prims.unit value
| R_ffi of Prims.unit * Prims.unit * Prims.nat * Obj.t * dvalue Prims.list * Obj.t
| R_cond of v_meta * Prims.unit value * exp * exp

let is_R_aspar = (fun _discr_ -> (match (_discr_) with
| R_aspar (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_assec = (fun _discr_ -> (match (_discr_) with
| R_assec (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_box = (fun _discr_ -> (match (_discr_) with
| R_box (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_unbox = (fun _discr_ -> (match (_discr_) with
| R_unbox (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_mkwire = (fun _discr_ -> (match (_discr_) with
| R_mkwire (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_projwire = (fun _discr_ -> (match (_discr_) with
| R_projwire (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_concatwire = (fun _discr_ -> (match (_discr_) with
| R_concatwire (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_let = (fun _discr_ -> (match (_discr_) with
| R_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_app = (fun _discr_ -> (match (_discr_) with
| R_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_ffi = (fun _discr_ -> (match (_discr_) with
| R_ffi (_) -> begin
true
end
| _ -> begin
false
end))

let is_R_cond = (fun _discr_ -> (match (_discr_) with
| R_cond (_) -> begin
true
end
| _ -> begin
false
end))

let ___R_aspar___meta = (fun projectee -> (match (projectee) with
| R_aspar (_18_433, _18_434, _18_435) -> begin
_18_433
end))

let ___R_aspar___ps = (fun projectee -> (match (projectee) with
| R_aspar (_18_437, _18_436, _18_438) -> begin
_18_436
end))

let ___R_aspar___v = (fun projectee -> (match (projectee) with
| R_aspar (_18_440, _18_441, _18_439) -> begin
_18_439
end))

let ___R_assec___meta = (fun projectee -> (match (projectee) with
| R_assec (_18_444, _18_445, _18_446) -> begin
_18_444
end))

let ___R_assec___ps = (fun projectee -> (match (projectee) with
| R_assec (_18_448, _18_447, _18_449) -> begin
_18_447
end))

let ___R_assec___v = (fun projectee -> (match (projectee) with
| R_assec (_18_451, _18_452, _18_450) -> begin
_18_450
end))

let ___R_box___meta = (fun projectee -> (match (projectee) with
| R_box (_18_455, _18_456, _18_457) -> begin
_18_455
end))

let ___R_box___ps = (fun projectee -> (match (projectee) with
| R_box (_18_459, _18_458, _18_460) -> begin
_18_458
end))

let ___R_box___v = (fun projectee -> (match (projectee) with
| R_box (_18_462, _18_463, _18_461) -> begin
_18_461
end))

let ___R_unbox___meta = (fun projectee -> (match (projectee) with
| R_unbox (_18_466, _18_467) -> begin
_18_466
end))

let ___R_unbox___v = (fun projectee -> (match (projectee) with
| R_unbox (_18_469, _18_468) -> begin
_18_468
end))

let ___R_mkwire___mv = (fun projectee -> (match (projectee) with
| R_mkwire (_18_472, _18_473, _18_474) -> begin
_18_472
end))

let ___R_mkwire___ps = (fun projectee -> (match (projectee) with
| R_mkwire (_18_476, _18_475, _18_477) -> begin
_18_475
end))

let ___R_mkwire___v = (fun projectee -> (match (projectee) with
| R_mkwire (_18_479, _18_480, _18_478) -> begin
_18_478
end))

let ___R_projwire___meta = (fun projectee -> (match (projectee) with
| R_projwire (_18_483, _18_484, _18_485) -> begin
_18_483
end))

let ___R_projwire___p = (fun projectee -> (match (projectee) with
| R_projwire (_18_487, _18_486, _18_488) -> begin
_18_486
end))

let ___R_projwire___v = (fun projectee -> (match (projectee) with
| R_projwire (_18_490, _18_491, _18_489) -> begin
_18_489
end))

let ___R_concatwire___meta1 = (fun projectee -> (match (projectee) with
| R_concatwire (_18_494, _18_495, _18_496, _18_497) -> begin
_18_494
end))

let ___R_concatwire___meta2 = (fun projectee -> (match (projectee) with
| R_concatwire (_18_499, _18_498, _18_500, _18_501) -> begin
_18_498
end))

let ___R_concatwire___v1 = (fun projectee -> (match (projectee) with
| R_concatwire (_18_503, _18_504, _18_502, _18_505) -> begin
_18_502
end))

let ___R_concatwire___v2 = (fun projectee -> (match (projectee) with
| R_concatwire (_18_507, _18_508, _18_509, _18_506) -> begin
_18_506
end))

let ___R_let___meta = (fun projectee -> (match (projectee) with
| R_let (_18_512, _18_513, _18_514, _18_515) -> begin
_18_512
end))

let ___R_let___x = (fun projectee -> (match (projectee) with
| R_let (_18_517, _18_516, _18_518, _18_519) -> begin
_18_516
end))

let ___R_let___v = (fun projectee -> (match (projectee) with
| R_let (_18_521, _18_522, _18_520, _18_523) -> begin
_18_520
end))

let ___R_let___e = (fun projectee -> (match (projectee) with
| R_let (_18_525, _18_526, _18_527, _18_524) -> begin
_18_524
end))

let ___R_app___meta1 = (fun projectee -> (match (projectee) with
| R_app (_18_530, _18_531, _18_532, _18_533) -> begin
_18_530
end))

let ___R_app___meta2 = (fun projectee -> (match (projectee) with
| R_app (_18_535, _18_534, _18_536, _18_537) -> begin
_18_534
end))

let ___R_app___v1 = (fun projectee -> (match (projectee) with
| R_app (_18_539, _18_540, _18_538, _18_541) -> begin
_18_538
end))

let ___R_app___v2 = (fun projectee -> (match (projectee) with
| R_app (_18_543, _18_544, _18_545, _18_542) -> begin
_18_542
end))

let ___R_ffi___n = (fun projectee -> (match (projectee) with
| R_ffi (_, _, _18_548, _18_551, _18_552, _18_553) -> begin
_18_548
end))

let ___R_ffi___fn = (fun projectee -> (match (projectee) with
| R_ffi (_, _, _18_557, _18_554, _18_558, _18_559) -> begin
(Obj.magic _18_554)
end))

let ___R_ffi___args = (fun projectee -> (match (projectee) with
| R_ffi (_, _, _18_563, _18_564, _18_560, _18_565) -> begin
_18_560
end))

let ___R_ffi___inj = (fun projectee -> (match (projectee) with
| R_ffi (_, _, _18_569, _18_570, _18_571, _18_566) -> begin
(Obj.magic _18_566)
end))

let ___R_cond___meta = (fun projectee -> (match (projectee) with
| R_cond (_18_574, _18_575, _18_576, _18_577) -> begin
_18_574
end))

let ___R_cond___v = (fun projectee -> (match (projectee) with
| R_cond (_18_579, _18_578, _18_580, _18_581) -> begin
_18_578
end))

let ___R_cond___e1 = (fun projectee -> (match (projectee) with
| R_cond (_18_583, _18_584, _18_582, _18_585) -> begin
_18_582
end))

let ___R_cond___e2 = (fun projectee -> (match (projectee) with
| R_cond (_18_587, _18_588, _18_589, _18_586) -> begin
_18_586
end))

let empty_env = (fun _18_590 -> None)

let update_env = (fun meta en x v y -> if (y = x) then begin
Some (D_v (meta, v))
end else begin
(en y)
end)

type as_mode =
| Par
| Sec

let is_Par = (fun _discr_ -> (match (_discr_) with
| Par -> begin
true
end
| _ -> begin
false
end))

let is_Sec = (fun _discr_ -> (match (_discr_) with
| Sec -> begin
true
end
| _ -> begin
false
end))

type mode =
| Mode of as_mode * Prins.prins

let is_Mode = (fun _discr_ -> (match (_discr_) with
| Mode (_) -> begin
true
end
| _ -> begin
false
end))

let ___Mode___m = (fun projectee -> (match (projectee) with
| Mode (_18_601, _18_602) -> begin
_18_601
end))

let ___Mode___ps = (fun projectee -> (match (projectee) with
| Mode (_18_604, _18_603) -> begin
_18_603
end))

type frame' =
| F_aspar_ps of exp
| F_aspar_e of Prins.prins
| F_aspar_ret of Prins.prins
| F_assec_ps of exp
| F_assec_e of Prins.prins
| F_assec_ret
| F_box_ps of exp
| F_box_e of Prins.prins
| F_unbox
| F_mkwire_ps of exp
| F_mkwire_e of Prins.prins
| F_projwire_p of exp
| F_projwire_e of Prins.prin
| F_concatwire_e1 of exp
| F_concatwire_e2 of v_meta * Prims.unit value
| F_let of varname * exp
| F_app_e1 of exp
| F_app_e2 of v_meta * Prims.unit value
| F_ffi of Prims.unit * Prims.unit * Prims.nat * Obj.t * exp Prims.list * dvalue Prims.list * Obj.t
| F_cond of exp * exp

let is_F_aspar_ps = (fun _discr_ -> (match (_discr_) with
| F_aspar_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_aspar_e = (fun _discr_ -> (match (_discr_) with
| F_aspar_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_aspar_ret = (fun _discr_ -> (match (_discr_) with
| F_aspar_ret (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_assec_ps = (fun _discr_ -> (match (_discr_) with
| F_assec_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_assec_e = (fun _discr_ -> (match (_discr_) with
| F_assec_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_assec_ret = (fun _discr_ -> (match (_discr_) with
| F_assec_ret -> begin
true
end
| _ -> begin
false
end))

let is_F_box_ps = (fun _discr_ -> (match (_discr_) with
| F_box_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_box_e = (fun _discr_ -> (match (_discr_) with
| F_box_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_unbox = (fun _discr_ -> (match (_discr_) with
| F_unbox -> begin
true
end
| _ -> begin
false
end))

let is_F_mkwire_ps = (fun _discr_ -> (match (_discr_) with
| F_mkwire_ps (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_mkwire_e = (fun _discr_ -> (match (_discr_) with
| F_mkwire_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_projwire_p = (fun _discr_ -> (match (_discr_) with
| F_projwire_p (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_projwire_e = (fun _discr_ -> (match (_discr_) with
| F_projwire_e (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_concatwire_e1 = (fun _discr_ -> (match (_discr_) with
| F_concatwire_e1 (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_concatwire_e2 = (fun _discr_ -> (match (_discr_) with
| F_concatwire_e2 (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_let = (fun _discr_ -> (match (_discr_) with
| F_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_app_e1 = (fun _discr_ -> (match (_discr_) with
| F_app_e1 (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_app_e2 = (fun _discr_ -> (match (_discr_) with
| F_app_e2 (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_ffi = (fun _discr_ -> (match (_discr_) with
| F_ffi (_) -> begin
true
end
| _ -> begin
false
end))

let is_F_cond = (fun _discr_ -> (match (_discr_) with
| F_cond (_) -> begin
true
end
| _ -> begin
false
end))

let ___F_aspar_ps___e = (fun projectee -> (match (projectee) with
| F_aspar_ps (_18_635) -> begin
_18_635
end))

let ___F_aspar_e___ps = (fun projectee -> (match (projectee) with
| F_aspar_e (_18_638) -> begin
_18_638
end))

let ___F_aspar_ret___ps = (fun projectee -> (match (projectee) with
| F_aspar_ret (_18_641) -> begin
_18_641
end))

let ___F_assec_ps___e = (fun projectee -> (match (projectee) with
| F_assec_ps (_18_644) -> begin
_18_644
end))

let ___F_assec_e___ps = (fun projectee -> (match (projectee) with
| F_assec_e (_18_647) -> begin
_18_647
end))

let ___F_box_ps___e = (fun projectee -> (match (projectee) with
| F_box_ps (_18_650) -> begin
_18_650
end))

let ___F_box_e___ps = (fun projectee -> (match (projectee) with
| F_box_e (_18_653) -> begin
_18_653
end))

let ___F_mkwire_ps___e = (fun projectee -> (match (projectee) with
| F_mkwire_ps (_18_656) -> begin
_18_656
end))

let ___F_mkwire_e___ps = (fun projectee -> (match (projectee) with
| F_mkwire_e (_18_659) -> begin
_18_659
end))

let ___F_projwire_p___e = (fun projectee -> (match (projectee) with
| F_projwire_p (_18_662) -> begin
_18_662
end))

let ___F_projwire_e___p = (fun projectee -> (match (projectee) with
| F_projwire_e (_18_665) -> begin
_18_665
end))

let ___F_concatwire_e1___e = (fun projectee -> (match (projectee) with
| F_concatwire_e1 (_18_668) -> begin
_18_668
end))

let ___F_concatwire_e2___meta = (fun projectee -> (match (projectee) with
| F_concatwire_e2 (_18_671, _18_672) -> begin
_18_671
end))

let ___F_concatwire_e2___v = (fun projectee -> (match (projectee) with
| F_concatwire_e2 (_18_674, _18_673) -> begin
_18_673
end))

let ___F_let___x = (fun projectee -> (match (projectee) with
| F_let (_18_677, _18_678) -> begin
_18_677
end))

let ___F_let___e2 = (fun projectee -> (match (projectee) with
| F_let (_18_680, _18_679) -> begin
_18_679
end))

let ___F_app_e1___e2 = (fun projectee -> (match (projectee) with
| F_app_e1 (_18_683) -> begin
_18_683
end))

let ___F_app_e2___meta = (fun projectee -> (match (projectee) with
| F_app_e2 (_18_686, _18_687) -> begin
_18_686
end))

let ___F_app_e2___v = (fun projectee -> (match (projectee) with
| F_app_e2 (_18_689, _18_688) -> begin
_18_688
end))

let ___F_ffi___n = (fun projectee -> (match (projectee) with
| F_ffi (_, _, _18_692, _18_695, _18_696, _18_697, _18_698) -> begin
_18_692
end))

let ___F_ffi___fn = (fun projectee -> (match (projectee) with
| F_ffi (_, _, _18_702, _18_699, _18_703, _18_704, _18_705) -> begin
(Obj.magic _18_699)
end))

let ___F_ffi___es = (fun projectee -> (match (projectee) with
| F_ffi (_, _, _18_709, _18_710, _18_706, _18_711, _18_712) -> begin
_18_706
end))

let ___F_ffi___vs = (fun projectee -> (match (projectee) with
| F_ffi (_, _, _18_716, _18_717, _18_718, _18_713, _18_719) -> begin
_18_713
end))

let ___F_ffi___inj = (fun projectee -> (match (projectee) with
| F_ffi (_, _, _18_723, _18_724, _18_725, _18_726, _18_720) -> begin
(Obj.magic _18_720)
end))

let ___F_cond___e1 = (fun projectee -> (match (projectee) with
| F_cond (_18_729, _18_730) -> begin
_18_729
end))

let ___F_cond___e2 = (fun projectee -> (match (projectee) with
| F_cond (_18_732, _18_731) -> begin
_18_731
end))

type frame =
| Frame of mode * env * frame' * Prims.unit

let is_Frame = (fun _discr_ -> (match (_discr_) with
| Frame (_) -> begin
true
end
| _ -> begin
false
end))

let ___Frame___m = (fun projectee -> (match (projectee) with
| Frame (_18_738, _18_739, _18_740, _18_741) -> begin
_18_738
end))

let ___Frame___en = (fun projectee -> (match (projectee) with
| Frame (_18_743, _18_742, _18_744, _18_745) -> begin
_18_742
end))

let ___Frame___f = (fun projectee -> (match (projectee) with
| Frame (_18_747, _18_748, _18_746, _18_749) -> begin
_18_746
end))

let ___Frame___tr = (fun projectee -> ())

type stack =
frame Prims.list

type term =
| T_exp of exp
| T_red of redex
| T_val of v_meta * Prims.unit value
| T_sec_wait

let is_T_exp = (fun _discr_ -> (match (_discr_) with
| T_exp (_) -> begin
true
end
| _ -> begin
false
end))

let is_T_red = (fun _discr_ -> (match (_discr_) with
| T_red (_) -> begin
true
end
| _ -> begin
false
end))

let is_T_val = (fun _discr_ -> (match (_discr_) with
| T_val (_) -> begin
true
end
| _ -> begin
false
end))

let is_T_sec_wait = (fun _discr_ -> (match (_discr_) with
| T_sec_wait -> begin
true
end
| _ -> begin
false
end))

let ___T_exp___e = (fun projectee -> (match (projectee) with
| T_exp (_18_760) -> begin
_18_760
end))

let ___T_red___r = (fun projectee -> (match (projectee) with
| T_red (_18_763) -> begin
_18_763
end))

let ___T_val___meta = (fun projectee -> (match (projectee) with
| T_val (_18_766, _18_767) -> begin
_18_766
end))

let ___T_val___v = (fun projectee -> (match (projectee) with
| T_val (_18_769, _18_768) -> begin
_18_768
end))

type level =
| Source
| Target

let is_Source = (fun _discr_ -> (match (_discr_) with
| Source -> begin
true
end
| _ -> begin
false
end))

let is_Target = (fun _discr_ -> (match (_discr_) with
| Target -> begin
true
end
| _ -> begin
false
end))

let src = (fun l -> (is_Source l))

let m_of_mode = (fun _18_774 -> (match (_18_774) with
| Mode (m, _18_772) -> begin
m
end))

let is_sec_frame = (fun f' -> (not ((((is_F_aspar_ps f') || (is_F_aspar_e f')) || (is_F_aspar_ret f')))))

let ps_of_aspar_ret_frame = (fun _18_782 -> (match (_18_782) with
| F_aspar_ret (ps) -> begin
ps
end))

let rec stack_source_inv = (fun s _18_786 -> (Obj.magic ()))

let rec stack_target_inv = (fun s m -> (Obj.magic ()))

let rec stack_inv = (fun s m l -> (Obj.magic ()))

let is_sec_redex = (fun r -> (not ((is_R_aspar r))))

let r_of_t_red = (fun _18_817 -> (match (_18_817) with
| T_red (r) -> begin
r
end))

let term_inv = (fun t m l -> (((not ((is_Source l))) || (not ((t = T_sec_wait)))) && ((not (((is_T_red t) && ((m_of_mode m) = Sec)))) || (is_sec_redex (r_of_t_red t)))))

let trace_inv = (fun tr m -> (Obj.magic ()))

type config =
| Conf of level * mode * stack * env * term * Prims.unit

let is_Conf = (fun _discr_ -> (match (_discr_) with
| Conf (_) -> begin
true
end
| _ -> begin
false
end))

let ___Conf___l = (fun projectee -> (match (projectee) with
| Conf (_18_834, _18_835, _18_836, _18_837, _18_838, _18_839) -> begin
_18_834
end))

let ___Conf___m = (fun projectee -> (match (projectee) with
| Conf (_18_841, _18_840, _18_842, _18_843, _18_844, _18_845) -> begin
_18_840
end))

let ___Conf___s = (fun projectee -> (match (projectee) with
| Conf (_18_847, _18_848, _18_846, _18_849, _18_850, _18_851) -> begin
_18_846
end))

let ___Conf___en = (fun projectee -> (match (projectee) with
| Conf (_18_853, _18_854, _18_855, _18_852, _18_856, _18_857) -> begin
_18_852
end))

let ___Conf___t = (fun projectee -> (match (projectee) with
| Conf (_18_859, _18_860, _18_861, _18_862, _18_858, _18_863) -> begin
_18_858
end))

let ___Conf___tr = (fun projectee -> ())

type sconfig =
config

type tconfig =
config

let f_of_frame = (fun _18_879 -> (match (_18_879) with
| Frame (_18_878, _18_876, f, _18_873) -> begin
f
end))

let hd_of_list = (fun _18_886 -> (match (_18_886) with
| hd::_18_884 -> begin
hd
end))

let is_sframe = (fun _18_900 f -> (match (_18_900) with
| Conf (_18_899, _18_897, s, _18_894, _18_892, _18_890) -> begin
((Prims.is_Cons s) && (f (f_of_frame (hd_of_list s))))
end))

let t_of_conf = (fun _18_913 -> (match (_18_913) with
| Conf (_18_912, _18_910, _18_908, _18_906, t, _18_903) -> begin
t
end))

let is_value = (fun c -> (is_T_val (t_of_conf c)))

let is_value_ps = (fun c -> (match (c) with
| Conf (_18_930, _18_928, _18_926, _18_924, T_val (_18_36153, V_eprins (eps)), _18_919) -> begin
(not ((eps = (FStar_OrdSet.empty ((fun c _18_930 _18_928 _18_926 _18_924 _18_36153 eps _18_919 -> Prins.p_cmp) c _18_930 _18_928 _18_926 _18_924 _18_36153 eps ())))))
end
| _18_933 -> begin
false
end))

let is_value_p = (fun c -> (match (c) with
| Conf (_18_949, _18_947, _18_945, _18_943, T_val (_18_36673, V_prin (_18_939)), _18_937) -> begin
true
end
| _18_952 -> begin
false
end))

let c_value = (fun _18_968 -> (match (_18_968) with
| Conf (_18_967, _18_965, _18_963, _18_961, T_val (meta, v), _18_956) -> begin
D_v (meta, v)
end))

let c_value_ps = (fun c -> (match (c) with
| Conf (_18_984, _18_982, _18_980, _18_978, T_val (_18_37333, V_eprins (ps)), _18_973) -> begin
ps
end))

let c_value_p = (fun c -> (match (c) with
| Conf (_18_1001, _18_999, _18_997, _18_995, T_val (_18_37731, V_prin (p)), _18_990) -> begin
p
end))

let m_of_conf = (fun _18_1014 -> (match (_18_1014) with
| Conf (_18_1013, m, _18_1010, _18_1008, _18_1006, _18_1004) -> begin
m
end))

let is_par = (fun c -> (is_Par (m_of_mode (m_of_conf c))))

let is_sec = (fun c -> (is_Sec (m_of_mode (m_of_conf c))))

let is_clos = (fun meta v -> (match (v) with
| (V_clos (_, _, _)) | (V_emp_clos (_, _)) | (V_fix_clos (_, _, _, _)) -> begin
true
end
| _18_1042 -> begin
false
end))

let get_en_b = (fun meta v -> (match (v) with
| V_clos (en, x, e) -> begin
(en, x, e)
end
| V_fix_clos (en, f, x, e) -> begin
((update_env (Meta ((FStar_OrdSet.empty ((fun meta v en f x e -> Prins.p_cmp) meta v en f x e)), Cannot_b, (FStar_OrdSet.empty ((fun meta v en f x e -> Prins.p_cmp) meta v en f x e)), Cannot_w)) en f (V_fix_clos (en, f, x, e))), x, e)
end
| V_emp_clos (x, e) -> begin
(empty_env, x, e)
end))

let is_terminal = (fun _18_1072 -> (match (_18_1072) with
| Conf (_18_1071, Mode (as_m, _18_1067), s, _18_1064, t, _18_1061) -> begin
(((as_m = Par) && (s = [])) && (is_T_val t))
end))

let mk_aspar = (fun ps e -> E_aspar (ps, e))

let mk_assec = (fun ps e -> E_assec (ps, e))

let mk_box = (fun ps e -> E_box (ps, e))

let mk_unbox = (fun e -> E_unbox (e))

let mk_mkwire = (fun e1 e2 -> E_mkwire (e1, e2))

let mk_projwire = (fun e1 e2 -> E_projwire (e1, e2))

let mk_concatwire = (fun e1 e2 -> E_concatwire (e1, e2))

let mk_const = (fun c -> E_const (c))

let mk_var = (fun x -> E_var (x))

let mk_let = (fun x e1 e2 -> E_let (x, e1, e2))

let mk_abs = (fun x e -> E_abs (x, e))

let mk_fix = (fun f x e -> E_fix (f, x, e))

let mk_empabs = (fun x e -> E_empabs (x, e))

let mk_app = (fun e1 e2 -> E_app (e1, e2))

let mk_ffi = (fun n name a l b -> E_ffi ((), (), n, name, (Obj.magic a), l, (Obj.magic b)))

let mk_cond = (fun e e1 e2 -> E_cond (e, e1, e2))

let mk_v_opaque = (fun v s c sps -> D_v (Meta ((FStar_OrdSet.empty ((fun a v s c sps -> Prins.p_cmp) () (Obj.magic v) (Obj.magic s) (Obj.magic c) (Obj.magic sps))), Can_b, (FStar_OrdSet.empty ((fun a v s c sps -> Prins.p_cmp) () (Obj.magic v) (Obj.magic s) (Obj.magic c) (Obj.magic sps))), Can_w), V_opaque ((), (Obj.magic v), Meta ((FStar_OrdSet.empty ((fun a v s c sps -> Prins.p_cmp) () (Obj.magic v) (Obj.magic s) (Obj.magic c) (Obj.magic sps))), Can_b, (FStar_OrdSet.empty ((fun a v s c sps -> Prins.p_cmp) () (Obj.magic v) (Obj.magic s) (Obj.magic c) (Obj.magic sps))), Can_w), (Obj.magic s), (Obj.magic c), (Obj.magic sps))))

let compose_opaque_meta = (fun m1 m2 -> (let _18_1127 = m1
in (match (_18_1127) with
| Meta (bps1, cb1, wps1, cw1) -> begin
(let _18_1132 = m2
in (match (_18_1132) with
| Meta (bps2, cb2, wps2, cw2) -> begin
(let cb = if ((cb1 = Can_b) && (cb2 = Can_b)) then begin
Can_b
end else begin
Cannot_b
end
in (let cw = if ((cw1 = Can_w) && (cw2 = Can_w)) then begin
Can_w
end else begin
Cannot_w
end
in Meta ((FStar_OrdSet.union ((fun m1 m2 _18_1127 bps1 cb1 wps1 cw1 _18_1132 bps2 cb2 wps2 cw2 cb cw -> Prins.p_cmp) m1 m2 _18_1127 bps1 cb1 wps1 cw1 _18_1132 bps2 cb2 wps2 cw2 cb cw) bps1 bps2), cb, (FStar_OrdSet.union ((fun m1 m2 _18_1127 bps1 cb1 wps1 cw1 _18_1132 bps2 cb2 wps2 cw2 cb cw -> Prins.p_cmp) m1 m2 _18_1127 bps1 cb1 wps1 cw1 _18_1132 bps2 cb2 wps2 cw2 cb cw) wps1 wps2), cw)))
end))
end)))




