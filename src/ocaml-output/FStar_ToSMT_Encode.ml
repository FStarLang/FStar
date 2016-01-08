
open Prims
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _54_39 -> (match (_54_39) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (FStar_List.filter (fun _54_1 -> (match (_54_1) with
| (FStar_Util.Inl (_54_43), _54_46) -> begin
false
end
| _54_49 -> begin
true
end)) args))

let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText a.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)

let mk_typ_projector_name = (fun lid a -> (let _120_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _120_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _120_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _120_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _120_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _120_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _54_61 -> (match (()) with
| () -> begin
(let _120_30 = (let _120_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _120_29 lid.FStar_Absyn_Syntax.str))
in (FStar_All.failwith _120_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _120_31 = (FStar_Absyn_Util.compress_typ t)
in _120_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _54_65) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.FStar_Absyn_Syntax.v)
end
| FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.FStar_Absyn_Syntax.v)
end))
end
end
| _54_74 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun lid i -> (let _120_37 = (let _120_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str _120_36))
in (FStar_All.pipe_left escape _120_37)))

let mk_typ_projector = (fun lid a -> (let _120_43 = (let _120_42 = (mk_typ_projector_name lid a)
in (_120_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _120_43)))

let mk_term_projector = (fun lid a -> (let _120_49 = (let _120_48 = (mk_term_projector_name lid a)
in (_120_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _120_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _120_55 = (let _120_54 = (mk_term_projector_name_by_pos lid i)
in (_120_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _120_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

let varops = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _54_100 -> (match (()) with
| () -> begin
(let _120_159 = (FStar_Util.smap_create 100)
in (let _120_158 = (FStar_Util.smap_create 100)
in (_120_159, _120_158)))
end))
in (let scopes = (let _120_161 = (let _120_160 = (new_scope ())
in (_120_160)::[])
in (FStar_Util.mk_ref _120_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _120_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _120_165 (fun _54_108 -> (match (_54_108) with
| (names, _54_107) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_54_111) -> begin
(let _54_113 = (FStar_Util.incr ctr)
in (let _120_167 = (let _120_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _120_166))
in (Prims.strcat (Prims.strcat y "__") _120_167)))
end)
in (let top_scope = (let _120_169 = (let _120_168 = (FStar_ST.read scopes)
in (FStar_List.hd _120_168))
in (FStar_All.pipe_left Prims.fst _120_169))
in (let _54_117 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _120_175 = (let _120_174 = (FStar_All.pipe_left mk_unique pp.FStar_Absyn_Syntax.idText)
in (Prims.strcat _120_174 "__"))
in (Prims.strcat _120_175 rn.FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Absyn_Syntax.str))
in (let next_id = (fun _54_125 -> (match (()) with
| () -> begin
(let _54_126 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _120_183 = (let _120_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _120_182))
in (FStar_Util.format2 "%s_%s" pfx _120_183)))
in (let string_const = (fun s -> (match ((let _120_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _120_187 (fun _54_135 -> (match (_54_135) with
| (_54_133, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _120_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _120_188))
in (let top_scope = (let _120_190 = (let _120_189 = (FStar_ST.read scopes)
in (FStar_List.hd _120_189))
in (FStar_All.pipe_left Prims.snd _120_190))
in (let _54_142 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _54_145 -> (match (()) with
| () -> begin
(let _120_195 = (let _120_194 = (new_scope ())
in (let _120_193 = (FStar_ST.read scopes)
in (_120_194)::_120_193))
in (FStar_ST.op_Colon_Equals scopes _120_195))
end))
in (let pop = (fun _54_147 -> (match (()) with
| () -> begin
(let _120_199 = (let _120_198 = (FStar_ST.read scopes)
in (FStar_List.tl _120_198))
in (FStar_ST.op_Colon_Equals scopes _120_199))
end))
in (let mark = (fun _54_149 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _54_151 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _54_153 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _54_166 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _54_171 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _54_174 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (let _120_215 = (let _120_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _120_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_120_214, _120_213)))
in (FStar_Absyn_Util.mkbvd _120_215)))

type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Absyn_Syntax.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Absyn_Syntax.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)

let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tvar = (fun _discr_ -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_ftvar = (fun _discr_ -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_54_179) -> begin
_54_179
end))

let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_54_182) -> begin
_54_182
end))

let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_54_185) -> begin
_54_185
end))

let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_54_188) -> begin
_54_188
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

let print_env = (fun e -> (let _120_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _54_2 -> (match (_54_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _54_213) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _120_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _120_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_120_311))
end else begin
None
end)

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _120_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _120_316))))

let gen_term_var = (fun env x -> (let ysym = (let _120_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _120_321))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _54_232 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _54_232.tcenv; warn = _54_232.warn; cache = _54_232.cache; nolabels = _54_232.nolabels; use_zfuel_name = _54_232.use_zfuel_name; encode_non_total_function_typ = _54_232.encode_non_total_function_typ})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _54_238 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _54_238.depth; tcenv = _54_238.tcenv; warn = _54_238.warn; cache = _54_238.cache; nolabels = _54_238.nolabels; use_zfuel_name = _54_238.use_zfuel_name; encode_non_total_function_typ = _54_238.encode_non_total_function_typ})))))

let push_term_var = (fun env x t -> (let _54_243 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _54_243.depth; tcenv = _54_243.tcenv; warn = _54_243.warn; cache = _54_243.cache; nolabels = _54_243.nolabels; use_zfuel_name = _54_243.use_zfuel_name; encode_non_total_function_typ = _54_243.encode_non_total_function_typ}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _54_3 -> (match (_54_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _54_253 -> begin
None
end)))) with
| None -> begin
(let _120_336 = (let _120_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _120_335))
in (FStar_All.failwith _120_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _120_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _120_341))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _54_263 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _54_263.tcenv; warn = _54_263.warn; cache = _54_263.cache; nolabels = _54_263.nolabels; use_zfuel_name = _54_263.use_zfuel_name; encode_non_total_function_typ = _54_263.encode_non_total_function_typ})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _54_269 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _54_269.depth; tcenv = _54_269.tcenv; warn = _54_269.warn; cache = _54_269.cache; nolabels = _54_269.nolabels; use_zfuel_name = _54_269.use_zfuel_name; encode_non_total_function_typ = _54_269.encode_non_total_function_typ})))))

let push_typ_var = (fun env x t -> (let _54_274 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _54_274.depth; tcenv = _54_274.tcenv; warn = _54_274.warn; cache = _54_274.cache; nolabels = _54_274.nolabels; use_zfuel_name = _54_274.use_zfuel_name; encode_non_total_function_typ = _54_274.encode_non_total_function_typ}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _54_4 -> (match (_54_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _54_284 -> begin
None
end)))) with
| None -> begin
(let _120_356 = (let _120_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _120_355))
in (FStar_All.failwith _120_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _120_367 = (let _54_294 = env
in (let _120_366 = (let _120_365 = (let _120_364 = (let _120_363 = (let _120_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _120_361 -> Some (_120_361)) _120_362))
in (x, fname, _120_363, None))
in Binding_fvar (_120_364))
in (_120_365)::env.bindings)
in {bindings = _120_366; depth = _54_294.depth; tcenv = _54_294.tcenv; warn = _54_294.warn; cache = _54_294.cache; nolabels = _54_294.nolabels; use_zfuel_name = _54_294.use_zfuel_name; encode_non_total_function_typ = _54_294.encode_non_total_function_typ}))
in (fname, ftok, _120_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _54_5 -> (match (_54_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _54_306 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _120_378 = (let _120_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _120_377))
in (FStar_All.failwith _120_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _54_316 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _54_316.depth; tcenv = _54_316.tcenv; warn = _54_316.warn; cache = _54_316.cache; nolabels = _54_316.nolabels; use_zfuel_name = _54_316.use_zfuel_name; encode_non_total_function_typ = _54_316.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _54_325 = (lookup_lid env x)
in (match (_54_325) with
| (t1, t2, _54_324) -> begin
(let t3 = (let _120_395 = (let _120_394 = (let _120_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_120_393)::[])
in (f, _120_394))
in (FStar_ToSMT_Term.mkApp _120_395))
in (let _54_327 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _54_327.depth; tcenv = _54_327.tcenv; warn = _54_327.warn; cache = _54_327.cache; nolabels = _54_327.nolabels; use_zfuel_name = _54_327.use_zfuel_name; encode_non_total_function_typ = _54_327.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun env a -> (let _54_334 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_54_334) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _54_338 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_54_342, fuel::[]) -> begin
if (let _120_399 = (let _120_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _120_398 Prims.fst))
in (FStar_Util.starts_with _120_399 "fuel")) then begin
(let _120_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _120_400 fuel))
end else begin
t
end
end
| _54_348 -> begin
t
end)
end
| _54_350 -> begin
(let _120_402 = (let _120_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _120_401))
in (FStar_All.failwith _120_402))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _54_358 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_54_358) with
| (x, _54_355, _54_357) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _54_364 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_54_364) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _54_368; FStar_ToSMT_Term.freevars = _54_366}) when env.use_zfuel_name -> begin
(g, zf)
end
| _54_376 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _54_386 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _120_417 = (let _54_391 = env
in (let _120_416 = (let _120_415 = (let _120_414 = (let _120_413 = (let _120_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _120_411 -> Some (_120_411)) _120_412))
in (x, fname, _120_413))
in Binding_ftvar (_120_414))
in (_120_415)::env.bindings)
in {bindings = _120_416; depth = _54_391.depth; tcenv = _54_391.tcenv; warn = _54_391.warn; cache = _54_391.cache; nolabels = _54_391.nolabels; use_zfuel_name = _54_391.use_zfuel_name; encode_non_total_function_typ = _54_391.encode_non_total_function_typ}))
in (fname, ftok, _120_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _54_6 -> (match (_54_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _54_402 -> begin
None
end)))) with
| None -> begin
(let _120_424 = (let _120_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _120_423))
in (FStar_All.failwith _120_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _54_410 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _54_410.depth; tcenv = _54_410.tcenv; warn = _54_410.warn; cache = _54_410.cache; nolabels = _54_410.nolabels; use_zfuel_name = _54_410.use_zfuel_name; encode_non_total_function_typ = _54_410.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _120_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _120_435 Prims.snd))) with
| None -> begin
(let _120_437 = (let _120_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _120_436))
in (FStar_All.failwith _120_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _120_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _120_440 Prims.fst)))

let tok_of_name = (fun env nm -> (FStar_Util.find_map env.bindings (fun _54_7 -> (match (_54_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _54_435 -> begin
None
end))))

let mkForall_fuel' = (fun n _54_440 -> (match (_54_440) with
| (pats, vars, body) -> begin
(let fallback = (fun _54_442 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(let _54_445 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_54_445) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _54_455 -> begin
p
end)))))
in (let pats = (FStar_List.map add_fuel pats)
in (let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _120_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _120_453))
end
| _54_468 -> begin
(let _120_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _120_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _54_471 -> begin
body
end)
in (let vars = ((fsym, FStar_ToSMT_Term.Fuel_sort))::vars
in (FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end)
end))

let mkForall_fuel = (mkForall_fuel' 1)

let head_normal = (fun env t -> (let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _120_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _120_460 FStar_Option.isNone))
end
| _54_509 -> begin
false
end)))

let whnf = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end)

let whnf_e = (fun env e -> (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))

let norm_t = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env.tcenv t))

let norm_k = (fun env k -> (FStar_Tc_Normalize.normalize_kind env.tcenv k))

let trivial_post = (fun t -> (let _120_482 = (let _120_481 = (let _120_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_120_479)::[])
in (let _120_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_120_481, _120_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _120_482 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _120_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _120_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _120_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _120_490))
end
| _54_526 -> begin
(let _120_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _120_491))
end)) e)))

let mk_ApplyE_args = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyET out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))

let mk_ApplyT = (fun t vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _120_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _120_504))
end
| _54_541 -> begin
(let _120_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _120_505))
end)) t)))

let mk_ApplyT_args = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app = (fun _54_8 -> (match (_54_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _54_560 -> begin
false
end))

let is_eta = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _54_571; FStar_ToSMT_Term.freevars = _54_569}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _54_589) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _54_596 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_54_598, []) -> begin
(let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _54_604 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)

type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}

let is_Mkpattern = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const = (fun _54_9 -> (match (_54_9) with
| FStar_Absyn_Syntax.Const_unit -> begin
FStar_ToSMT_Term.mk_Term_unit
end
| FStar_Absyn_Syntax.Const_bool (true) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
end
| FStar_Absyn_Syntax.Const_bool (false) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkFalse)
end
| FStar_Absyn_Syntax.Const_char (c) -> begin
(let _120_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _120_561))
end
| FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _120_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _120_562))
end
| FStar_Absyn_Syntax.Const_int (i) -> begin
(let _120_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _120_563))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _120_567 = (let _120_566 = (let _120_565 = (let _120_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _120_564))
in (_120_565)::[])
in ("FStar.Int32.Int32", _120_566))
in (FStar_ToSMT_Term.mkApp _120_567))
end
| FStar_Absyn_Syntax.Const_string (bytes, _54_626) -> begin
(let _120_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _120_568))
end
| c -> begin
(let _120_570 = (let _120_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _120_569))
in (FStar_All.failwith _120_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_54_637) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_54_640) -> begin
(let _120_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _120_579))
end
| _54_643 -> begin
if norm then begin
(let _120_580 = (whnf env t)
in (aux false _120_580))
end else begin
(let _120_583 = (let _120_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _120_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _120_582 _120_581)))
in (FStar_All.failwith _120_583))
end
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _120_620 = (FStar_Absyn_Util.compress_kind k)
in _120_620.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_54_648, k0) -> begin
(let _54_652 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _120_622 = (FStar_Absyn_Print.kind_to_string k)
in (let _120_621 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _120_622 _120_621)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _54_656) -> begin
(let _120_624 = (let _120_623 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _120_623))
in (_120_624, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _120_625 = (varops.fresh "t")
in (_120_625, FStar_ToSMT_Term.Type_sort))
in (let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (let _54_671 = (encode_binders None bs env)
in (match (_54_671) with
| (vars, guards, env', decls, _54_670) -> begin
(let app = (mk_ApplyT t vars)
in (let _54_675 = (encode_knd kbody env' app)
in (match (_54_675) with
| (kbody, decls') -> begin
(let rec aux = (fun app vars guards -> (match ((vars, guards)) with
| ([], []) -> begin
kbody
end
| (x::vars, g::guards) -> begin
(let app = (mk_ApplyT app ((x)::[]))
in (let body = (aux app vars guards)
in (let body = (match (vars) with
| [] -> begin
body
end
| _54_694 -> begin
(let _120_634 = (let _120_633 = (let _120_632 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _120_632))
in (_120_633, body))
in (FStar_ToSMT_Term.mkAnd _120_634))
end)
in (let _120_636 = (let _120_635 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _120_635))
in (FStar_ToSMT_Term.mkForall _120_636)))))
end
| _54_697 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _120_638 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _120_638 (FStar_List.filter (fun _54_702 -> (match (_54_702) with
| (x, _54_701) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _54_708) -> begin
(let _120_641 = (let _120_640 = (let _120_639 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _120_639))
in (FStar_ToSMT_Term.mkApp _120_640))
in (_120_641, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _120_642 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_120_642))
end else begin
None
end
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _120_644 = (let _120_643 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _120_643))
in (FStar_ToSMT_Term.mkApp _120_644))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _120_653 = (let _120_652 = (let _120_651 = (let _120_650 = (let _120_649 = (let _120_648 = (let _120_647 = (let _120_646 = (let _120_645 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _120_645))
in (_120_646, k_interp))
in (FStar_ToSMT_Term.mkAnd _120_647))
in (t_has_k, _120_648))
in (FStar_ToSMT_Term.mkIff _120_649))
in (((t_has_k)::[])::[], (tsym)::cvars, _120_650))
in (FStar_ToSMT_Term.mkForall _120_651))
in (_120_652, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_120_653))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _54_720 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _54_723 -> begin
(let _120_655 = (let _120_654 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _120_654))
in (FStar_All.failwith _120_655))
end))
and encode_knd = (fun k env t -> (let _54_729 = (encode_knd_term k env)
in (match (_54_729) with
| (k, decls) -> begin
(let _120_659 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_120_659, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _54_733 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _120_663 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _120_663))
end else begin
()
end
in (let _54_783 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _54_740 b -> (match (_54_740) with
| (vars, guards, env, decls, names) -> begin
(let _54_777 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _54_743}) -> begin
(let a = (unmangle a)
in (let _54_752 = (gen_typ_var env a)
in (match (_54_752) with
| (aasym, aa, env') -> begin
(let _54_753 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _120_667 = (FStar_Absyn_Print.strBvd a)
in (let _120_666 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _120_667 aasym _120_666)))
end else begin
()
end
in (let _54_757 = (encode_knd k env aa)
in (match (_54_757) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _54_759}) -> begin
(let x = (unmangle x)
in (let _54_768 = (gen_term_var env x)
in (match (_54_768) with
| (xxsym, xx, env') -> begin
(let _54_771 = (let _120_668 = (norm_t env t)
in (encode_typ_pred fuel_opt _120_668 env xx))
in (match (_54_771) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_54_777) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_54_783) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _54_791 = (encode_typ_term t env)
in (match (_54_791) with
| (t, decls) -> begin
(let _120_673 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_120_673, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _54_799 = (encode_typ_term t env)
in (match (_54_799) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _120_678 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_120_678, decls))
end
| Some (f) -> begin
(let _120_679 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_120_679, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _120_682 = (lookup_typ_var env a)
in (_120_682, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _120_683 = (lookup_free_tvar env fv)
in (_120_683, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(let _54_820 = (encode_binders None binders env)
in (match (_54_820) with
| (vars, guards, env', decls, _54_819) -> begin
(let fsym = (let _120_684 = (varops.fresh "f")
in (_120_684, FStar_ToSMT_Term.Term_sort))
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _54_826 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_54_826) with
| (pre_opt, res_t) -> begin
(let _54_829 = (encode_typ_pred None res_t env' app)
in (match (_54_829) with
| (res_pred, decls') -> begin
(let _54_838 = (match (pre_opt) with
| None -> begin
(let _120_685 = (FStar_ToSMT_Term.mk_and_l guards)
in (_120_685, decls))
end
| Some (pre) -> begin
(let _54_835 = (encode_formula pre env')
in (match (_54_835) with
| (guard, decls0) -> begin
(let _120_686 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_120_686, (FStar_List.append decls decls0)))
end))
end)
in (match (_54_838) with
| (guards, guard_decls) -> begin
(let t_interp = (let _120_688 = (let _120_687 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _120_687))
in (FStar_ToSMT_Term.mkForall _120_688))
in (let cvars = (let _120_690 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _120_690 (FStar_List.filter (fun _54_843 -> (match (_54_843) with
| (x, _54_842) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _54_849) -> begin
(let _120_693 = (let _120_692 = (let _120_691 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _120_691))
in (FStar_ToSMT_Term.mkApp _120_692))
in (_120_693, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _120_694 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_120_694))
end else begin
None
end
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _120_696 = (let _120_695 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _120_695))
in (FStar_ToSMT_Term.mkApp _120_696))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _120_698 = (let _120_697 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_120_697, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_120_698))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _120_705 = (let _120_704 = (let _120_703 = (let _120_702 = (let _120_701 = (let _120_700 = (let _120_699 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _120_699))
in (f_has_t, _120_700))
in (FStar_ToSMT_Term.mkImp _120_701))
in (((f_has_t)::[])::[], (fsym)::cvars, _120_702))
in (mkForall_fuel _120_703))
in (_120_704, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_120_705))
in (let t_interp = (let _120_709 = (let _120_708 = (let _120_707 = (let _120_706 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _120_706))
in (FStar_ToSMT_Term.mkForall _120_707))
in (_120_708, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_120_709))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _54_865 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(let tsym = (varops.fresh "Non_total_Typ_fun")
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, [], FStar_ToSMT_Term.Type_sort, None))
in (let t = (FStar_ToSMT_Term.mkApp (tsym, []))
in (let t_kinding = (let _120_711 = (let _120_710 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_120_710, None))
in FStar_ToSMT_Term.Assume (_120_711))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _120_718 = (let _120_717 = (let _120_716 = (let _120_715 = (let _120_714 = (let _120_713 = (let _120_712 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _120_712))
in (f_has_t, _120_713))
in (FStar_ToSMT_Term.mkImp _120_714))
in (((f_has_t)::[])::[], (fsym)::[], _120_715))
in (mkForall_fuel _120_716))
in (_120_717, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_120_718))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_54_876) -> begin
(let _54_895 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _54_885; FStar_Absyn_Syntax.pos = _54_883; FStar_Absyn_Syntax.fvs = _54_881; FStar_Absyn_Syntax.uvs = _54_879} -> begin
(x, f)
end
| _54_892 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_54_895) with
| (x, f) -> begin
(let _54_898 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_54_898) with
| (base_t, decls) -> begin
(let _54_902 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_54_902) with
| (x, xtm, env') -> begin
(let _54_905 = (encode_formula f env')
in (match (_54_905) with
| (refinement, decls') -> begin
(let _54_908 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_54_908) with
| (fsym, fterm) -> begin
(let encoding = (let _120_720 = (let _120_719 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_120_719, refinement))
in (FStar_ToSMT_Term.mkAnd _120_720))
in (let cvars = (let _120_722 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _120_722 (FStar_List.filter (fun _54_913 -> (match (_54_913) with
| (y, _54_912) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _54_920, _54_922) -> begin
(let _120_725 = (let _120_724 = (let _120_723 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _120_723))
in (FStar_ToSMT_Term.mkApp _120_724))
in (_120_725, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _120_727 = (let _120_726 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _120_726))
in (FStar_ToSMT_Term.mkApp _120_727))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (let assumption = (let _120_729 = (let _120_728 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _120_728))
in (FStar_ToSMT_Term.mkForall _120_729))
in (let t_decls = (let _120_736 = (let _120_735 = (let _120_734 = (let _120_733 = (let _120_732 = (let _120_731 = (let _120_730 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_120_730))
in (assumption, _120_731))
in FStar_ToSMT_Term.Assume (_120_732))
in (_120_733)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_120_734)
in (tdecl)::_120_735)
in (FStar_List.append (FStar_List.append decls decls') _120_736))
in (let _54_935 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _120_737 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _120_737))
in (let _54_944 = (encode_knd k env ttm)
in (match (_54_944) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let is_full_app = (fun _54_951 -> (match (()) with
| () -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind head)
in (let _54_956 = (FStar_Absyn_Util.kind_formals kk)
in (match (_54_956) with
| (formals, _54_955) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _54_963 = (encode_args args env)
in (match (_54_963) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _54_969 = (encode_args args env)
in (match (_54_969) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _120_742 = (let _120_741 = (FStar_List.map (fun _54_10 -> (match (_54_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _120_741))
in (FStar_ToSMT_Term.mkApp _120_742))
in (t, decls)))
end else begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _120_743 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _120_743))
in (let _54_985 = (encode_knd k env ttm)
in (match (_54_985) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _54_988 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(let _54_1000 = (encode_binders None bs env)
in (match (_54_1000) with
| (vars, guards, env, decls, _54_999) -> begin
(let _54_1003 = (encode_typ_term body env)
in (match (_54_1003) with
| (body, decls') -> begin
(let key_body = (let _120_747 = (let _120_746 = (let _120_745 = (let _120_744 = (FStar_ToSMT_Term.mk_and_l guards)
in (_120_744, body))
in (FStar_ToSMT_Term.mkImp _120_745))
in ([], vars, _120_746))
in (FStar_ToSMT_Term.mkForall _120_747))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _54_1009, _54_1011) -> begin
(let _120_750 = (let _120_749 = (let _120_748 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _120_748))
in (FStar_ToSMT_Term.mkApp _120_749))
in (_120_750, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tsym = (varops.fresh "Typ_lam")
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _120_752 = (let _120_751 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _120_751))
in (FStar_ToSMT_Term.mkApp _120_752))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _120_759 = (let _120_758 = (let _120_757 = (let _120_756 = (let _120_755 = (let _120_754 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _120_753 = (FStar_ToSMT_Term.mkEq (app, body))
in (_120_754, _120_753)))
in (FStar_ToSMT_Term.mkImp _120_755))
in (((app)::[])::[], (FStar_List.append vars cvars), _120_756))
in (FStar_ToSMT_Term.mkForall _120_757))
in (_120_758, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_120_759))
in (let kinding = (let _54_1026 = (let _120_760 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _120_760 env t))
in (match (_54_1026) with
| (ktm, decls'') -> begin
(let _120_764 = (let _120_763 = (let _120_762 = (let _120_761 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_120_761, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_120_762))
in (_120_763)::[])
in (FStar_List.append decls'' _120_764))
end))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _54_1029 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _54_1033) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_54_1037) -> begin
(let _120_765 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _120_765 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _120_770 = (let _120_769 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _120_768 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _120_767 = (FStar_Absyn_Print.typ_to_string t0)
in (let _120_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _120_769 _120_768 _120_767 _120_766)))))
in (FStar_All.failwith _120_770))
end)))
and encode_exp = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_54_1048) -> begin
(let _120_773 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _120_773 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _54_1055) -> begin
(let _120_774 = (lookup_free_var env v)
in (_120_774, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _120_775 = (encode_const c)
in (_120_775, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _54_1063) -> begin
(let _54_1066 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _54_1070)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _54_1076) -> begin
(let e = (let _120_776 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _120_776))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _54_1085 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _120_779 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_120_779, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _54_1089 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _120_780 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _120_780)) then begin
(fallback ())
end else begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(let _54_1101 = (FStar_Util.first_N nformals bs)
in (match (_54_1101) with
| (bs0, rest) -> begin
(let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _54_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (let e = (let _120_782 = (let _120_781 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _120_781))
in (FStar_Absyn_Syntax.mk_Exp_abs _120_782 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(let _54_1114 = (encode_binders None bs env)
in (match (_54_1114) with
| (vars, guards, envbody, decls, _54_1113) -> begin
(let _54_1117 = (encode_exp body envbody)
in (match (_54_1117) with
| (body, decls') -> begin
(let key_body = (let _120_786 = (let _120_785 = (let _120_784 = (let _120_783 = (FStar_ToSMT_Term.mk_and_l guards)
in (_120_783, body))
in (FStar_ToSMT_Term.mkImp _120_784))
in ([], vars, _120_785))
in (FStar_ToSMT_Term.mkForall _120_786))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _54_1123, _54_1125) -> begin
(let _120_789 = (let _120_788 = (let _120_787 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _120_787))
in (FStar_ToSMT_Term.mkApp _120_788))
in (_120_789, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, FStar_ToSMT_Term.Term_sort, None))
in (let f = (let _120_791 = (let _120_790 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _120_790))
in (FStar_ToSMT_Term.mkApp _120_791))
in (let app = (mk_ApplyE f vars)
in (let _54_1139 = (encode_typ_pred None tfun env f)
in (match (_54_1139) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _120_793 = (let _120_792 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_120_792, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_120_793))
in (let interp_f = (let _120_800 = (let _120_799 = (let _120_798 = (let _120_797 = (let _120_796 = (let _120_795 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _120_794 = (FStar_ToSMT_Term.mkEq (app, body))
in (_120_795, _120_794)))
in (FStar_ToSMT_Term.mkImp _120_796))
in (((app)::[])::[], (FStar_List.append vars cvars), _120_797))
in (FStar_ToSMT_Term.mkForall _120_798))
in (_120_799, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_120_800))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _54_1143 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _54_1146 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _54_1157); FStar_Absyn_Syntax.tk = _54_1154; FStar_Absyn_Syntax.pos = _54_1152; FStar_Absyn_Syntax.fvs = _54_1150; FStar_Absyn_Syntax.uvs = _54_1148}, (FStar_Util.Inl (_54_1172), _54_1175)::(FStar_Util.Inr (v1), _54_1169)::(FStar_Util.Inr (v2), _54_1164)::[]) when (FStar_Absyn_Syntax.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(let _54_1182 = (encode_exp v1 env)
in (match (_54_1182) with
| (v1, decls1) -> begin
(let _54_1185 = (encode_exp v2 env)
in (match (_54_1185) with
| (v2, decls2) -> begin
(let _120_801 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_120_801, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_54_1195); FStar_Absyn_Syntax.tk = _54_1193; FStar_Absyn_Syntax.pos = _54_1191; FStar_Absyn_Syntax.fvs = _54_1189; FStar_Absyn_Syntax.uvs = _54_1187}, _54_1199) -> begin
(let _120_802 = (whnf_e env e)
in (encode_exp _120_802 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(let _54_1208 = (encode_args args_e env)
in (match (_54_1208) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _54_1213 = (encode_exp head env)
in (match (_54_1213) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _54_1222 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_54_1222) with
| (formals, rest) -> begin
(let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _120_805 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _120_805 (FStar_Absyn_Util.subst_typ subst)))
in (let _54_1227 = (encode_typ_pred None ty env app_tm)
in (match (_54_1227) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _120_807 = (let _120_806 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_120_806, None))
in FStar_ToSMT_Term.Assume (_120_807))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _54_1234 = (lookup_free_var_sym env fv)
in (match (_54_1234) with
| (fname, fuel_args) -> begin
(let tm = (let _120_813 = (let _120_812 = (let _120_811 = (FStar_List.map (fun _54_11 -> (match (_54_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _120_811))
in (fname, _120_812))
in (FStar_ToSMT_Term.mkApp' _120_813))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _54_1241 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _120_815 = (FStar_Absyn_Print.exp_to_string head)
in (let _120_814 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _120_815 _120_814)))
end else begin
()
end
in (let head_type = (let _120_818 = (let _120_817 = (let _120_816 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _120_816))
in (whnf env _120_817))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _120_818))
in (let _54_1244 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _120_821 = (FStar_Absyn_Print.exp_to_string head)
in (let _120_820 = (FStar_Absyn_Print.tag_of_exp head)
in (let _120_819 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _120_821 _120_820 _120_819))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _120_825 = (let _120_824 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _120_823 = (FStar_Absyn_Print.exp_to_string e0)
in (let _120_822 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _120_824 _120_823 _120_822))))
in (FStar_All.failwith _120_825))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _54_1253) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _54_1257 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_54_1266); FStar_Absyn_Syntax.lbtyp = _54_1264; FStar_Absyn_Syntax.lbeff = _54_1262; FStar_Absyn_Syntax.lbdef = _54_1260}::[]), _54_1272) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _54_1278; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _54_1290 = (encode_exp e1 env)
in (match (_54_1290) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _54_1294 = (encode_exp e2 env')
in (match (_54_1294) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_54_1296) -> begin
(let _54_1298 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _120_826 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_120_826, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _54_1308 = (encode_exp e env)
in (match (_54_1308) with
| (scr, decls) -> begin
(let _54_1348 = (FStar_List.fold_right (fun _54_1312 _54_1315 -> (match ((_54_1312, _54_1315)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _54_1319 _54_1322 -> (match ((_54_1319, _54_1322)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _54_1328 -> (match (_54_1328) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _54_1342 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _54_1339 = (encode_exp w env)
in (match (_54_1339) with
| (w, decls2) -> begin
(let _120_837 = (let _120_836 = (let _120_835 = (let _120_834 = (let _120_833 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _120_833))
in (FStar_ToSMT_Term.mkEq _120_834))
in (guard, _120_835))
in (FStar_ToSMT_Term.mkAnd _120_836))
in (_120_837, decls2))
end))
end)
in (match (_54_1342) with
| (guard, decls2) -> begin
(let _54_1345 = (encode_exp br env)
in (match (_54_1345) with
| (br, decls3) -> begin
(let _120_838 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_120_838, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_54_1348) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_54_1350) -> begin
(let _120_841 = (let _120_840 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _120_839 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _120_840 _120_839)))
in (FStar_All.failwith _120_841))
end))))
and encode_pat = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _54_1357 -> begin
(let _120_844 = (encode_one_pat env pat)
in (_120_844)::[])
end))
and encode_one_pat = (fun env pat -> (let _54_1360 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _120_847 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _120_847))
end else begin
()
end
in (let _54_1364 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_54_1364) with
| (vars, pat_exp_or_typ) -> begin
(let _54_1385 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _54_1367 v -> (match (_54_1367) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(let _54_1375 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_54_1375) with
| (aa, _54_1373, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(let _54_1382 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_54_1382) with
| (xx, _54_1380, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_54_1385) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_54_1390) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _120_855 = (let _120_854 = (encode_const c)
in (scrutinee, _120_854))
in (FStar_ToSMT_Term.mkEq _120_855))
end
| FStar_Absyn_Syntax.Pat_cons (f, _54_1414, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _54_1423 -> (match (_54_1423) with
| (arg, _54_1422) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _120_858 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _120_858)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_54_1430) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_54_1447) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _54_1451, args) -> begin
(let _120_866 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _54_1459 -> (match (_54_1459) with
| (arg, _54_1458) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _120_865 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _120_865)))
end))))
in (FStar_All.pipe_right _120_866 FStar_List.flatten))
end))
in (let pat_term = (fun _54_1462 -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| FStar_Util.Inl (t) -> begin
(encode_typ_term t env)
end
| FStar_Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args = (fun l env -> (let _54_1492 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _54_1472 x -> (match (_54_1472) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _54_1477) -> begin
(let _54_1481 = (encode_typ_term t env)
in (match (_54_1481) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _54_1485) -> begin
(let _54_1489 = (encode_exp e env)
in (match (_54_1489) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_54_1492) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _54_1498 = (encode_formula_with_labels phi env)
in (match (_54_1498) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _54_1501 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun induction_on new_pats t env -> (let rec list_elements = (fun e -> (match ((let _120_881 = (FStar_Absyn_Util.unmeta_exp e)
in _120_881.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _54_1518); FStar_Absyn_Syntax.tk = _54_1515; FStar_Absyn_Syntax.pos = _54_1513; FStar_Absyn_Syntax.fvs = _54_1511; FStar_Absyn_Syntax.uvs = _54_1509}, _54_1523) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _54_1536); FStar_Absyn_Syntax.tk = _54_1533; FStar_Absyn_Syntax.pos = _54_1531; FStar_Absyn_Syntax.fvs = _54_1529; FStar_Absyn_Syntax.uvs = _54_1527}, _54_1551::(FStar_Util.Inr (hd), _54_1548)::(FStar_Util.Inr (tl), _54_1543)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _120_882 = (list_elements tl)
in (hd)::_120_882)
end
| _54_1556 -> begin
(let _54_1557 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (let v_or_t_pat = (fun p -> (match ((let _120_885 = (FStar_Absyn_Util.unmeta_exp p)
in _120_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _54_1571); FStar_Absyn_Syntax.tk = _54_1568; FStar_Absyn_Syntax.pos = _54_1566; FStar_Absyn_Syntax.fvs = _54_1564; FStar_Absyn_Syntax.uvs = _54_1562}, (FStar_Util.Inl (_54_1581), _54_1584)::(FStar_Util.Inr (e), _54_1578)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _54_1599); FStar_Absyn_Syntax.tk = _54_1596; FStar_Absyn_Syntax.pos = _54_1594; FStar_Absyn_Syntax.fvs = _54_1592; FStar_Absyn_Syntax.uvs = _54_1590}, (FStar_Util.Inl (t), _54_1606)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _54_1612 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let lemma_pats = (fun p -> (let elts = (list_elements p)
in (match (elts) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _54_1634); FStar_Absyn_Syntax.tk = _54_1631; FStar_Absyn_Syntax.pos = _54_1629; FStar_Absyn_Syntax.fvs = _54_1627; FStar_Absyn_Syntax.uvs = _54_1625}, (FStar_Util.Inr (e), _54_1641)::[]); FStar_Absyn_Syntax.tk = _54_1623; FStar_Absyn_Syntax.pos = _54_1621; FStar_Absyn_Syntax.fvs = _54_1619; FStar_Absyn_Syntax.uvs = _54_1617}::[] when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _120_890 = (list_elements e)
in (FStar_All.pipe_right _120_890 (FStar_List.map (fun branch -> (let _120_889 = (list_elements branch)
in (FStar_All.pipe_right _120_889 (FStar_List.map v_or_t_pat)))))))
end
| _54_1650 -> begin
(let _120_891 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_120_891)::[])
end)))
in (let _54_1693 = (match ((let _120_892 = (FStar_Absyn_Util.compress_typ t)
in _120_892.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _54_1659; FStar_Absyn_Syntax.pos = _54_1657; FStar_Absyn_Syntax.fvs = _54_1655; FStar_Absyn_Syntax.uvs = _54_1653}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _54_1678)::(FStar_Util.Inl (post), _54_1673)::(FStar_Util.Inr (pats), _54_1668)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _120_893 = (lemma_pats pats')
in (binders, pre, post, _120_893)))
end
| _54_1686 -> begin
(FStar_All.failwith "impos")
end)
end
| _54_1688 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_54_1693) with
| (binders, pre, post, patterns) -> begin
(let _54_1700 = (encode_binders None binders env)
in (match (_54_1700) with
| (vars, guards, env, decls, _54_1699) -> begin
(let _54_1720 = (let _120_897 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (let _54_1717 = (let _120_896 = (FStar_All.pipe_right branch (FStar_List.map (fun _54_12 -> (match (_54_12) with
| (FStar_Util.Inl (t), _54_1706) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _54_1711) -> begin
(encode_exp e (let _54_1713 = env
in {bindings = _54_1713.bindings; depth = _54_1713.depth; tcenv = _54_1713.tcenv; warn = _54_1713.warn; cache = _54_1713.cache; nolabels = _54_1713.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _54_1713.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _120_896 FStar_List.unzip))
in (match (_54_1717) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _120_897 FStar_List.unzip))
in (match (_54_1720) with
| (pats, decls') -> begin
(let decls' = (FStar_List.flatten decls')
in (let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _120_900 = (let _120_899 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _120_899 e))
in (_120_900)::p))))
end
| _54_1730 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _120_906 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_120_906)::p))))
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _120_908 = (let _120_907 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _120_907 tl))
in (aux _120_908 vars))
end
| _54_1742 -> begin
pats
end))
in (let _120_909 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _120_909 vars)))
end)
end)
in (let env = (let _54_1744 = env
in {bindings = _54_1744.bindings; depth = _54_1744.depth; tcenv = _54_1744.tcenv; warn = _54_1744.warn; cache = _54_1744.cache; nolabels = true; use_zfuel_name = _54_1744.use_zfuel_name; encode_non_total_function_typ = _54_1744.encode_non_total_function_typ})
in (let _54_1749 = (let _120_910 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _120_910 env))
in (match (_54_1749) with
| (pre, decls'') -> begin
(let _54_1752 = (let _120_911 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _120_911 env))
in (match (_54_1752) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _120_916 = (let _120_915 = (let _120_914 = (let _120_913 = (let _120_912 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_120_912, post))
in (FStar_ToSMT_Term.mkImp _120_913))
in (pats, vars, _120_914))
in (FStar_ToSMT_Term.mkForall _120_915))
in (_120_916, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f l -> (let _54_1773 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(let _54_1765 = (encode_typ_term t env)
in (match (_54_1765) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(let _54_1770 = (encode_exp e env)
in (match (_54_1770) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_54_1773) with
| (decls, args) -> begin
(let _120_934 = (f args)
in (_120_934, [], decls))
end)))
in (let enc_prop_c = (fun f l -> (let _54_1793 = (FStar_List.fold_right (fun t _54_1781 -> (match (_54_1781) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(let _54_1787 = (encode_formula_with_labels t env)
in (match (_54_1787) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _54_1789 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_54_1793) with
| (phis, labs, decls) -> begin
(let _120_950 = (f phis)
in (_120_950, labs, decls))
end)))
in (let const_op = (fun f _54_1796 -> (f, [], []))
in (let un_op = (fun f l -> (let _120_964 = (FStar_List.hd l)
in (FStar_All.pipe_left f _120_964)))
in (let bin_op = (fun f _54_13 -> (match (_54_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _54_1807 -> begin
(FStar_All.failwith "Impossible")
end))
in (let eq_op = (fun _54_14 -> (match (_54_14) with
| _54_1815::_54_1813::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _54_15 -> (match (_54_15) with
| (FStar_Util.Inl (lhs), _54_1828)::(FStar_Util.Inl (rhs), _54_1823)::[] -> begin
(let _54_1834 = (encode_formula_with_labels rhs env)
in (match (_54_1834) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _54_1837) -> begin
(l1, labs1, decls1)
end
| _54_1841 -> begin
(let _54_1845 = (encode_formula_with_labels lhs env)
in (match (_54_1845) with
| (l2, labs2, decls2) -> begin
(let _120_978 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_120_978, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _54_1847 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _54_16 -> (match (_54_16) with
| (FStar_Util.Inl (guard), _54_1863)::(FStar_Util.Inl (_then), _54_1858)::(FStar_Util.Inl (_else), _54_1853)::[] -> begin
(let _54_1869 = (encode_formula_with_labels guard env)
in (match (_54_1869) with
| (g, labs1, decls1) -> begin
(let _54_1873 = (encode_formula_with_labels _then env)
in (match (_54_1873) with
| (t, labs2, decls2) -> begin
(let _54_1877 = (encode_formula_with_labels _else env)
in (match (_54_1877) with
| (e, labs3, decls3) -> begin
(let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _54_1880 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _120_990 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _120_990)))
in (let connectives = (let _120_1051 = (let _120_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _120_999))
in (let _120_1050 = (let _120_1049 = (let _120_1005 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _120_1005))
in (let _120_1048 = (let _120_1047 = (let _120_1046 = (let _120_1014 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _120_1014))
in (let _120_1045 = (let _120_1044 = (let _120_1043 = (let _120_1023 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _120_1023))
in (let _120_1042 = (let _120_1041 = (let _120_1029 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _120_1029))
in (_120_1041)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_120_1043)::_120_1042))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_120_1044)
in (_120_1046)::_120_1045))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_120_1047)
in (_120_1049)::_120_1048))
in (_120_1051)::_120_1050))
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _54_1898 = (encode_formula_with_labels phi' env)
in (match (_54_1898) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(let lvar = (let _120_1054 = (varops.fresh "label")
in (_120_1054, FStar_ToSMT_Term.Bool_sort))
in (let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _54_1909; FStar_Absyn_Syntax.pos = _54_1907; FStar_Absyn_Syntax.fvs = _54_1905; FStar_Absyn_Syntax.uvs = _54_1903}, _54_1924::(FStar_Util.Inr (l), _54_1921)::(FStar_Util.Inl (phi), _54_1916)::[]) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let _54_1930 = (encode_exp l env)
in (match (_54_1930) with
| (e, decls) -> begin
(let _54_1933 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_54_1933) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _54_1941; FStar_Absyn_Syntax.pos = _54_1939; FStar_Absyn_Syntax.fvs = _54_1937; FStar_Absyn_Syntax.uvs = _54_1935}, _54_1953::(FStar_Util.Inl (phi), _54_1949)::tl) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _54_1961)::[] -> begin
Some (pat)
end)
in (let _54_1967 = (encode_function_type_as_formula None pat phi env)
in (match (_54_1967) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _54_1969 -> begin
(let _54_1972 = (encode_typ_term phi env)
in (match (_54_1972) with
| (tt, decls) -> begin
(let _120_1055 = (FStar_ToSMT_Term.mk_Valid tt)
in (_120_1055, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _54_1984 = (encode_binders None bs env)
in (match (_54_1984) with
| (vars, guards, env, decls, _54_1983) -> begin
(let _54_2004 = (let _120_1067 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (let _54_2001 = (let _120_1066 = (FStar_All.pipe_right p (FStar_List.map (fun _54_17 -> (match (_54_17) with
| (FStar_Util.Inl (t), _54_1990) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _54_1995) -> begin
(encode_exp e (let _54_1997 = env
in {bindings = _54_1997.bindings; depth = _54_1997.depth; tcenv = _54_1997.tcenv; warn = _54_1997.warn; cache = _54_1997.cache; nolabels = _54_1997.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _54_1997.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _120_1066 FStar_List.unzip))
in (match (_54_2001) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _120_1067 FStar_List.unzip))
in (match (_54_2004) with
| (pats, decls') -> begin
(let _54_2008 = (encode_formula_with_labels body env)
in (match (_54_2008) with
| (body, labs, decls'') -> begin
(let _120_1068 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _120_1068, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _54_2009 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _120_1069 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _120_1069))
end else begin
()
end
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _54_2021 -> (match (_54_2021) with
| (l, _54_2020) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_54_2024, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _54_2034 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _120_1086 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _120_1086))
end else begin
()
end
in (let _54_2042 = (encode_q_body env vars pats body)
in (match (_54_2042) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _120_1089 = (let _120_1088 = (let _120_1087 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _120_1087))
in (FStar_ToSMT_Term.mkForall _120_1088))
in (_120_1089, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _54_2055 = (encode_q_body env vars pats body)
in (match (_54_2055) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _120_1092 = (let _120_1091 = (let _120_1090 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _120_1090))
in (FStar_ToSMT_Term.mkExists _120_1091))
in (_120_1092, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Absyn_Syntax.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Absyn_Syntax.lident  ->  Prims.bool}

let is_Mkprims_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

let prims = (let _54_2061 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_54_2061) with
| (asym, a) -> begin
(let _54_2064 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_54_2064) with
| (xsym, x) -> begin
(let _54_2067 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_54_2067) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_ToSMT_Term.DefineFun ((x, vars, FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (let _120_1135 = (let _120_1134 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _120_1134))
in (FStar_ToSMT_Term.mkApp _120_1135))
in (let vname_decl = (let _120_1137 = (let _120_1136 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _120_1136, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_120_1137))
in (let _120_1143 = (let _120_1142 = (let _120_1141 = (let _120_1140 = (let _120_1139 = (let _120_1138 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _120_1138))
in (FStar_ToSMT_Term.mkForall _120_1139))
in (_120_1140, None))
in FStar_ToSMT_Term.Assume (_120_1141))
in (_120_1142)::[])
in (vname_decl)::_120_1143))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _120_1303 = (let _120_1152 = (let _120_1151 = (let _120_1150 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1150))
in (quant axy _120_1151))
in (FStar_Absyn_Const.op_Eq, _120_1152))
in (let _120_1302 = (let _120_1301 = (let _120_1159 = (let _120_1158 = (let _120_1157 = (let _120_1156 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _120_1156))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1157))
in (quant axy _120_1158))
in (FStar_Absyn_Const.op_notEq, _120_1159))
in (let _120_1300 = (let _120_1299 = (let _120_1168 = (let _120_1167 = (let _120_1166 = (let _120_1165 = (let _120_1164 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1163 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1164, _120_1163)))
in (FStar_ToSMT_Term.mkLT _120_1165))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1166))
in (quant xy _120_1167))
in (FStar_Absyn_Const.op_LT, _120_1168))
in (let _120_1298 = (let _120_1297 = (let _120_1177 = (let _120_1176 = (let _120_1175 = (let _120_1174 = (let _120_1173 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1172 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1173, _120_1172)))
in (FStar_ToSMT_Term.mkLTE _120_1174))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1175))
in (quant xy _120_1176))
in (FStar_Absyn_Const.op_LTE, _120_1177))
in (let _120_1296 = (let _120_1295 = (let _120_1186 = (let _120_1185 = (let _120_1184 = (let _120_1183 = (let _120_1182 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1181 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1182, _120_1181)))
in (FStar_ToSMT_Term.mkGT _120_1183))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1184))
in (quant xy _120_1185))
in (FStar_Absyn_Const.op_GT, _120_1186))
in (let _120_1294 = (let _120_1293 = (let _120_1195 = (let _120_1194 = (let _120_1193 = (let _120_1192 = (let _120_1191 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1190 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1191, _120_1190)))
in (FStar_ToSMT_Term.mkGTE _120_1192))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1193))
in (quant xy _120_1194))
in (FStar_Absyn_Const.op_GTE, _120_1195))
in (let _120_1292 = (let _120_1291 = (let _120_1204 = (let _120_1203 = (let _120_1202 = (let _120_1201 = (let _120_1200 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1199 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1200, _120_1199)))
in (FStar_ToSMT_Term.mkSub _120_1201))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _120_1202))
in (quant xy _120_1203))
in (FStar_Absyn_Const.op_Subtraction, _120_1204))
in (let _120_1290 = (let _120_1289 = (let _120_1211 = (let _120_1210 = (let _120_1209 = (let _120_1208 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _120_1208))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _120_1209))
in (quant qx _120_1210))
in (FStar_Absyn_Const.op_Minus, _120_1211))
in (let _120_1288 = (let _120_1287 = (let _120_1220 = (let _120_1219 = (let _120_1218 = (let _120_1217 = (let _120_1216 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1215 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1216, _120_1215)))
in (FStar_ToSMT_Term.mkAdd _120_1217))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _120_1218))
in (quant xy _120_1219))
in (FStar_Absyn_Const.op_Addition, _120_1220))
in (let _120_1286 = (let _120_1285 = (let _120_1229 = (let _120_1228 = (let _120_1227 = (let _120_1226 = (let _120_1225 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1224 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1225, _120_1224)))
in (FStar_ToSMT_Term.mkMul _120_1226))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _120_1227))
in (quant xy _120_1228))
in (FStar_Absyn_Const.op_Multiply, _120_1229))
in (let _120_1284 = (let _120_1283 = (let _120_1238 = (let _120_1237 = (let _120_1236 = (let _120_1235 = (let _120_1234 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1233 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1234, _120_1233)))
in (FStar_ToSMT_Term.mkDiv _120_1235))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _120_1236))
in (quant xy _120_1237))
in (FStar_Absyn_Const.op_Division, _120_1238))
in (let _120_1282 = (let _120_1281 = (let _120_1247 = (let _120_1246 = (let _120_1245 = (let _120_1244 = (let _120_1243 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1242 = (FStar_ToSMT_Term.unboxInt y)
in (_120_1243, _120_1242)))
in (FStar_ToSMT_Term.mkMod _120_1244))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _120_1245))
in (quant xy _120_1246))
in (FStar_Absyn_Const.op_Modulus, _120_1247))
in (let _120_1280 = (let _120_1279 = (let _120_1256 = (let _120_1255 = (let _120_1254 = (let _120_1253 = (let _120_1252 = (FStar_ToSMT_Term.unboxBool x)
in (let _120_1251 = (FStar_ToSMT_Term.unboxBool y)
in (_120_1252, _120_1251)))
in (FStar_ToSMT_Term.mkAnd _120_1253))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1254))
in (quant xy _120_1255))
in (FStar_Absyn_Const.op_And, _120_1256))
in (let _120_1278 = (let _120_1277 = (let _120_1265 = (let _120_1264 = (let _120_1263 = (let _120_1262 = (let _120_1261 = (FStar_ToSMT_Term.unboxBool x)
in (let _120_1260 = (FStar_ToSMT_Term.unboxBool y)
in (_120_1261, _120_1260)))
in (FStar_ToSMT_Term.mkOr _120_1262))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1263))
in (quant xy _120_1264))
in (FStar_Absyn_Const.op_Or, _120_1265))
in (let _120_1276 = (let _120_1275 = (let _120_1272 = (let _120_1271 = (let _120_1270 = (let _120_1269 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _120_1269))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_1270))
in (quant qx _120_1271))
in (FStar_Absyn_Const.op_Negation, _120_1272))
in (_120_1275)::[])
in (_120_1277)::_120_1276))
in (_120_1279)::_120_1278))
in (_120_1281)::_120_1280))
in (_120_1283)::_120_1282))
in (_120_1285)::_120_1284))
in (_120_1287)::_120_1286))
in (_120_1289)::_120_1288))
in (_120_1291)::_120_1290))
in (_120_1293)::_120_1292))
in (_120_1295)::_120_1294))
in (_120_1297)::_120_1296))
in (_120_1299)::_120_1298))
in (_120_1301)::_120_1300))
in (_120_1303)::_120_1302))
in (let mk = (fun l v -> (let _120_1335 = (FStar_All.pipe_right prims (FStar_List.filter (fun _54_2087 -> (match (_54_2087) with
| (l', _54_2086) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end))))
in (FStar_All.pipe_right _120_1335 (FStar_List.collect (fun _54_2091 -> (match (_54_2091) with
| (_54_2089, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _54_2097 -> (match (_54_2097) with
| (l', _54_2096) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms = (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let mk_unit = (fun _54_2103 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _120_1367 = (let _120_1358 = (let _120_1357 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_120_1357, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_120_1358))
in (let _120_1366 = (let _120_1365 = (let _120_1364 = (let _120_1363 = (let _120_1362 = (let _120_1361 = (let _120_1360 = (let _120_1359 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _120_1359))
in (FStar_ToSMT_Term.mkImp _120_1360))
in (((typing_pred)::[])::[], (xx)::[], _120_1361))
in (mkForall_fuel _120_1362))
in (_120_1363, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_120_1364))
in (_120_1365)::[])
in (_120_1367)::_120_1366))))
in (let mk_bool = (fun _54_2108 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _120_1388 = (let _120_1377 = (let _120_1376 = (let _120_1375 = (let _120_1374 = (let _120_1373 = (let _120_1372 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _120_1372))
in (FStar_ToSMT_Term.mkImp _120_1373))
in (((typing_pred)::[])::[], (xx)::[], _120_1374))
in (mkForall_fuel _120_1375))
in (_120_1376, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_120_1377))
in (let _120_1387 = (let _120_1386 = (let _120_1385 = (let _120_1384 = (let _120_1383 = (let _120_1382 = (let _120_1379 = (let _120_1378 = (FStar_ToSMT_Term.boxBool b)
in (_120_1378)::[])
in (_120_1379)::[])
in (let _120_1381 = (let _120_1380 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _120_1380 tt))
in (_120_1382, (bb)::[], _120_1381)))
in (FStar_ToSMT_Term.mkForall _120_1383))
in (_120_1384, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_120_1385))
in (_120_1386)::[])
in (_120_1388)::_120_1387))))))
in (let mk_int = (fun _54_2115 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _120_1400 = (let _120_1399 = (let _120_1398 = (let _120_1397 = (let _120_1396 = (let _120_1395 = (FStar_ToSMT_Term.boxInt a)
in (let _120_1394 = (let _120_1393 = (FStar_ToSMT_Term.boxInt b)
in (_120_1393)::[])
in (_120_1395)::_120_1394))
in (tt)::_120_1396)
in (tt)::_120_1397)
in ("Prims.Precedes", _120_1398))
in (FStar_ToSMT_Term.mkApp _120_1399))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _120_1400))
in (let precedes_y_x = (let _120_1401 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _120_1401))
in (let _120_1443 = (let _120_1407 = (let _120_1406 = (let _120_1405 = (let _120_1404 = (let _120_1403 = (let _120_1402 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _120_1402))
in (FStar_ToSMT_Term.mkImp _120_1403))
in (((typing_pred)::[])::[], (xx)::[], _120_1404))
in (mkForall_fuel _120_1405))
in (_120_1406, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_120_1407))
in (let _120_1442 = (let _120_1441 = (let _120_1415 = (let _120_1414 = (let _120_1413 = (let _120_1412 = (let _120_1409 = (let _120_1408 = (FStar_ToSMT_Term.boxInt b)
in (_120_1408)::[])
in (_120_1409)::[])
in (let _120_1411 = (let _120_1410 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _120_1410 tt))
in (_120_1412, (bb)::[], _120_1411)))
in (FStar_ToSMT_Term.mkForall _120_1413))
in (_120_1414, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_120_1415))
in (let _120_1440 = (let _120_1439 = (let _120_1438 = (let _120_1437 = (let _120_1436 = (let _120_1435 = (let _120_1434 = (let _120_1433 = (let _120_1432 = (let _120_1431 = (let _120_1430 = (let _120_1429 = (let _120_1418 = (let _120_1417 = (FStar_ToSMT_Term.unboxInt x)
in (let _120_1416 = (FStar_ToSMT_Term.mkInteger' 0)
in (_120_1417, _120_1416)))
in (FStar_ToSMT_Term.mkGT _120_1418))
in (let _120_1428 = (let _120_1427 = (let _120_1421 = (let _120_1420 = (FStar_ToSMT_Term.unboxInt y)
in (let _120_1419 = (FStar_ToSMT_Term.mkInteger' 0)
in (_120_1420, _120_1419)))
in (FStar_ToSMT_Term.mkGTE _120_1421))
in (let _120_1426 = (let _120_1425 = (let _120_1424 = (let _120_1423 = (FStar_ToSMT_Term.unboxInt y)
in (let _120_1422 = (FStar_ToSMT_Term.unboxInt x)
in (_120_1423, _120_1422)))
in (FStar_ToSMT_Term.mkLT _120_1424))
in (_120_1425)::[])
in (_120_1427)::_120_1426))
in (_120_1429)::_120_1428))
in (typing_pred_y)::_120_1430)
in (typing_pred)::_120_1431)
in (FStar_ToSMT_Term.mk_and_l _120_1432))
in (_120_1433, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _120_1434))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _120_1435))
in (mkForall_fuel _120_1436))
in (_120_1437, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_120_1438))
in (_120_1439)::[])
in (_120_1441)::_120_1440))
in (_120_1443)::_120_1442)))))))))))
in (let mk_int_alias = (fun _54_2127 tt -> (let _120_1452 = (let _120_1451 = (let _120_1450 = (let _120_1449 = (let _120_1448 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Absyn_Syntax.str, []))
in (tt, _120_1448))
in (FStar_ToSMT_Term.mkEq _120_1449))
in (_120_1450, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_120_1451))
in (_120_1452)::[]))
in (let mk_str = (fun _54_2131 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _120_1473 = (let _120_1462 = (let _120_1461 = (let _120_1460 = (let _120_1459 = (let _120_1458 = (let _120_1457 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _120_1457))
in (FStar_ToSMT_Term.mkImp _120_1458))
in (((typing_pred)::[])::[], (xx)::[], _120_1459))
in (mkForall_fuel _120_1460))
in (_120_1461, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_120_1462))
in (let _120_1472 = (let _120_1471 = (let _120_1470 = (let _120_1469 = (let _120_1468 = (let _120_1467 = (let _120_1464 = (let _120_1463 = (FStar_ToSMT_Term.boxString b)
in (_120_1463)::[])
in (_120_1464)::[])
in (let _120_1466 = (let _120_1465 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _120_1465 tt))
in (_120_1467, (bb)::[], _120_1466)))
in (FStar_ToSMT_Term.mkForall _120_1468))
in (_120_1469, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_120_1470))
in (_120_1471)::[])
in (_120_1473)::_120_1472))))))
in (let mk_ref = (fun reft_name _54_2139 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _120_1480 = (let _120_1479 = (let _120_1478 = (FStar_ToSMT_Term.mkFreeV aa)
in (_120_1478)::[])
in (reft_name, _120_1479))
in (FStar_ToSMT_Term.mkApp _120_1480))
in (let refb = (let _120_1483 = (let _120_1482 = (let _120_1481 = (FStar_ToSMT_Term.mkFreeV bb)
in (_120_1481)::[])
in (reft_name, _120_1482))
in (FStar_ToSMT_Term.mkApp _120_1483))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _120_1502 = (let _120_1489 = (let _120_1488 = (let _120_1487 = (let _120_1486 = (let _120_1485 = (let _120_1484 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _120_1484))
in (FStar_ToSMT_Term.mkImp _120_1485))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _120_1486))
in (mkForall_fuel _120_1487))
in (_120_1488, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_120_1489))
in (let _120_1501 = (let _120_1500 = (let _120_1499 = (let _120_1498 = (let _120_1497 = (let _120_1496 = (let _120_1495 = (let _120_1494 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _120_1493 = (let _120_1492 = (let _120_1491 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _120_1490 = (FStar_ToSMT_Term.mkFreeV bb)
in (_120_1491, _120_1490)))
in (FStar_ToSMT_Term.mkEq _120_1492))
in (_120_1494, _120_1493)))
in (FStar_ToSMT_Term.mkImp _120_1495))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _120_1496))
in (mkForall_fuel' 2 _120_1497))
in (_120_1498, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_120_1499))
in (_120_1500)::[])
in (_120_1502)::_120_1501))))))))))
in (let mk_false_interp = (fun _54_2149 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _120_1509 = (let _120_1508 = (let _120_1507 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_120_1507, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_120_1508))
in (_120_1509)::[])))
in (let mk_and_interp = (fun conj _54_2155 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _120_1516 = (let _120_1515 = (let _120_1514 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_120_1514)::[])
in ("Valid", _120_1515))
in (FStar_ToSMT_Term.mkApp _120_1516))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _120_1523 = (let _120_1522 = (let _120_1521 = (let _120_1520 = (let _120_1519 = (let _120_1518 = (let _120_1517 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_120_1517, valid))
in (FStar_ToSMT_Term.mkIff _120_1518))
in (((valid)::[])::[], (aa)::(bb)::[], _120_1519))
in (FStar_ToSMT_Term.mkForall _120_1520))
in (_120_1521, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_120_1522))
in (_120_1523)::[])))))))))
in (let mk_or_interp = (fun disj _54_2166 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _120_1530 = (let _120_1529 = (let _120_1528 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_120_1528)::[])
in ("Valid", _120_1529))
in (FStar_ToSMT_Term.mkApp _120_1530))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _120_1537 = (let _120_1536 = (let _120_1535 = (let _120_1534 = (let _120_1533 = (let _120_1532 = (let _120_1531 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_120_1531, valid))
in (FStar_ToSMT_Term.mkIff _120_1532))
in (((valid)::[])::[], (aa)::(bb)::[], _120_1533))
in (FStar_ToSMT_Term.mkForall _120_1534))
in (_120_1535, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_120_1536))
in (_120_1537)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _120_1544 = (let _120_1543 = (let _120_1542 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_120_1542)::[])
in ("Valid", _120_1543))
in (FStar_ToSMT_Term.mkApp _120_1544))
in (let _120_1551 = (let _120_1550 = (let _120_1549 = (let _120_1548 = (let _120_1547 = (let _120_1546 = (let _120_1545 = (FStar_ToSMT_Term.mkEq (x, y))
in (_120_1545, valid))
in (FStar_ToSMT_Term.mkIff _120_1546))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _120_1547))
in (FStar_ToSMT_Term.mkForall _120_1548))
in (_120_1549, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_120_1550))
in (_120_1551)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _120_1558 = (let _120_1557 = (let _120_1556 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_120_1556)::[])
in ("Valid", _120_1557))
in (FStar_ToSMT_Term.mkApp _120_1558))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _120_1565 = (let _120_1564 = (let _120_1563 = (let _120_1562 = (let _120_1561 = (let _120_1560 = (let _120_1559 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_120_1559, valid))
in (FStar_ToSMT_Term.mkIff _120_1560))
in (((valid)::[])::[], (aa)::(bb)::[], _120_1561))
in (FStar_ToSMT_Term.mkForall _120_1562))
in (_120_1563, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_120_1564))
in (_120_1565)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _120_1572 = (let _120_1571 = (let _120_1570 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_120_1570)::[])
in ("Valid", _120_1571))
in (FStar_ToSMT_Term.mkApp _120_1572))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _120_1579 = (let _120_1578 = (let _120_1577 = (let _120_1576 = (let _120_1575 = (let _120_1574 = (let _120_1573 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_120_1573, valid))
in (FStar_ToSMT_Term.mkIff _120_1574))
in (((valid)::[])::[], (aa)::(bb)::[], _120_1575))
in (FStar_ToSMT_Term.mkForall _120_1576))
in (_120_1577, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_120_1578))
in (_120_1579)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _120_1586 = (let _120_1585 = (let _120_1584 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_120_1584)::[])
in ("Valid", _120_1585))
in (FStar_ToSMT_Term.mkApp _120_1586))
in (let valid_b_x = (let _120_1589 = (let _120_1588 = (let _120_1587 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_120_1587)::[])
in ("Valid", _120_1588))
in (FStar_ToSMT_Term.mkApp _120_1589))
in (let _120_1603 = (let _120_1602 = (let _120_1601 = (let _120_1600 = (let _120_1599 = (let _120_1598 = (let _120_1597 = (let _120_1596 = (let _120_1595 = (let _120_1591 = (let _120_1590 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_120_1590)::[])
in (_120_1591)::[])
in (let _120_1594 = (let _120_1593 = (let _120_1592 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_120_1592, valid_b_x))
in (FStar_ToSMT_Term.mkImp _120_1593))
in (_120_1595, (xx)::[], _120_1594)))
in (FStar_ToSMT_Term.mkForall _120_1596))
in (_120_1597, valid))
in (FStar_ToSMT_Term.mkIff _120_1598))
in (((valid)::[])::[], (aa)::(bb)::[], _120_1599))
in (FStar_ToSMT_Term.mkForall _120_1600))
in (_120_1601, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_120_1602))
in (_120_1603)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _120_1610 = (let _120_1609 = (let _120_1608 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_120_1608)::[])
in ("Valid", _120_1609))
in (FStar_ToSMT_Term.mkApp _120_1610))
in (let valid_b_x = (let _120_1613 = (let _120_1612 = (let _120_1611 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_120_1611)::[])
in ("Valid", _120_1612))
in (FStar_ToSMT_Term.mkApp _120_1613))
in (let _120_1627 = (let _120_1626 = (let _120_1625 = (let _120_1624 = (let _120_1623 = (let _120_1622 = (let _120_1621 = (let _120_1620 = (let _120_1619 = (let _120_1615 = (let _120_1614 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_120_1614)::[])
in (_120_1615)::[])
in (let _120_1618 = (let _120_1617 = (let _120_1616 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_120_1616, valid_b_x))
in (FStar_ToSMT_Term.mkImp _120_1617))
in (_120_1619, (xx)::[], _120_1618)))
in (FStar_ToSMT_Term.mkExists _120_1620))
in (_120_1621, valid))
in (FStar_ToSMT_Term.mkIff _120_1622))
in (((valid)::[])::[], (aa)::(bb)::[], _120_1623))
in (FStar_ToSMT_Term.mkForall _120_1624))
in (_120_1625, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_120_1626))
in (_120_1627)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _120_1634 = (let _120_1633 = (let _120_1632 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_120_1632)::[])
in ("Valid", _120_1633))
in (FStar_ToSMT_Term.mkApp _120_1634))
in (let valid_a_b = (let _120_1637 = (let _120_1636 = (let _120_1635 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_120_1635)::[])
in ("Valid", _120_1636))
in (FStar_ToSMT_Term.mkApp _120_1637))
in (let _120_1651 = (let _120_1650 = (let _120_1649 = (let _120_1648 = (let _120_1647 = (let _120_1646 = (let _120_1645 = (let _120_1644 = (let _120_1643 = (let _120_1639 = (let _120_1638 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_120_1638)::[])
in (_120_1639)::[])
in (let _120_1642 = (let _120_1641 = (let _120_1640 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_120_1640, valid_a_b))
in (FStar_ToSMT_Term.mkImp _120_1641))
in (_120_1643, (bb)::[], _120_1642)))
in (FStar_ToSMT_Term.mkForall _120_1644))
in (_120_1645, valid))
in (FStar_ToSMT_Term.mkIff _120_1646))
in (((valid)::[])::[], (kk)::(aa)::[], _120_1647))
in (FStar_ToSMT_Term.mkForall _120_1648))
in (_120_1649, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_120_1650))
in (_120_1651)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _120_1658 = (let _120_1657 = (let _120_1656 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_120_1656)::[])
in ("Valid", _120_1657))
in (FStar_ToSMT_Term.mkApp _120_1658))
in (let valid_a_b = (let _120_1661 = (let _120_1660 = (let _120_1659 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_120_1659)::[])
in ("Valid", _120_1660))
in (FStar_ToSMT_Term.mkApp _120_1661))
in (let _120_1675 = (let _120_1674 = (let _120_1673 = (let _120_1672 = (let _120_1671 = (let _120_1670 = (let _120_1669 = (let _120_1668 = (let _120_1667 = (let _120_1663 = (let _120_1662 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_120_1662)::[])
in (_120_1663)::[])
in (let _120_1666 = (let _120_1665 = (let _120_1664 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_120_1664, valid_a_b))
in (FStar_ToSMT_Term.mkImp _120_1665))
in (_120_1667, (bb)::[], _120_1666)))
in (FStar_ToSMT_Term.mkExists _120_1668))
in (_120_1669, valid))
in (FStar_ToSMT_Term.mkIff _120_1670))
in (((valid)::[])::[], (kk)::(aa)::[], _120_1671))
in (FStar_ToSMT_Term.mkForall _120_1672))
in (_120_1673, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_120_1674))
in (_120_1675)::[]))))))))))
in (let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _54_2259 -> (match (_54_2259) with
| (l, _54_2258) -> begin
(FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_54_2262, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun env se -> (let _54_2268 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _120_1818 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _120_1818))
end else begin
()
end
in (let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Absyn_Syntax.str
end)
in (let _54_2276 = (encode_sigelt' env se)
in (match (_54_2276) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _120_1821 = (let _120_1820 = (let _120_1819 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_120_1819))
in (_120_1820)::[])
in (_120_1821, e))
end
| _54_2279 -> begin
(let _120_1828 = (let _120_1827 = (let _120_1823 = (let _120_1822 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_120_1822))
in (_120_1823)::g)
in (let _120_1826 = (let _120_1825 = (let _120_1824 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_120_1824))
in (_120_1825)::[])
in (FStar_List.append _120_1827 _120_1826)))
in (_120_1828, e))
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.all_")))
in (let encode_top_level_val = (fun env lid t quals -> (let tt = (whnf env t)
in (let _54_2292 = (encode_free_var env lid t tt quals)
in (match (_54_2292) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _120_1842 = (let _120_1841 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _120_1841))
in (_120_1842, env))
end else begin
(decls, env)
end
end))))
in (let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _54_2299 lb -> (match (_54_2299) with
| (decls, env) -> begin
(let _54_2303 = (let _120_1851 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _120_1851 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_54_2303) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_54_2305, _54_2307, _54_2309, _54_2311, FStar_Absyn_Syntax.Effect::[], _54_2315) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _54_2320, _54_2322, _54_2324, _54_2326, _54_2328) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _54_2333, _54_2335, _54_2337, _54_2339, _54_2341) when (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(let _54_2347 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_54_2347) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _120_1854 = (let _120_1853 = (let _120_1852 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_120_1852)::[])
in ("Valid", _120_1853))
in (FStar_ToSMT_Term.mkApp _120_1854))
in (let decls = (let _120_1862 = (let _120_1861 = (let _120_1860 = (let _120_1859 = (let _120_1858 = (let _120_1857 = (let _120_1856 = (let _120_1855 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _120_1855))
in (FStar_ToSMT_Term.mkEq _120_1856))
in (((valid_b2t_x)::[])::[], (xx)::[], _120_1857))
in (FStar_ToSMT_Term.mkForall _120_1858))
in (_120_1859, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_120_1860))
in (_120_1861)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_120_1862)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _54_2355, t, tags, _54_2359) -> begin
(let _54_2365 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_54_2365) with
| (tname, ttok, env) -> begin
(let _54_2374 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _54_2371 -> begin
(tps, t)
end)
in (match (_54_2374) with
| (tps, t) -> begin
(let _54_2381 = (encode_binders None tps env)
in (match (_54_2381) with
| (vars, guards, env', binder_decls, _54_2380) -> begin
(let tok_app = (let _120_1863 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _120_1863 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _120_1865 = (let _120_1864 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _120_1864))
in (FStar_ToSMT_Term.mkApp _120_1865))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _54_2387 -> begin
(let _120_1867 = (let _120_1866 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _120_1866))
in (_120_1867)::[])
end)
in (let decls = (let _120_1878 = (let _120_1871 = (let _120_1870 = (let _120_1869 = (let _120_1868 = (FStar_List.map Prims.snd vars)
in (tname, _120_1868, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_120_1869))
in (_120_1870)::(tok_decl)::[])
in (FStar_List.append _120_1871 fresh_tok))
in (let _120_1877 = (let _120_1876 = (let _120_1875 = (let _120_1874 = (let _120_1873 = (let _120_1872 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _120_1872))
in (FStar_ToSMT_Term.mkForall _120_1873))
in (_120_1874, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_120_1875))
in (_120_1876)::[])
in (FStar_List.append _120_1878 _120_1877)))
in (let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (let _54_2399 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _54_18 -> (match (_54_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _54_2394 -> begin
false
end)))) then begin
(let _120_1881 = (FStar_ToSMT_Term.mk_Valid app)
in (let _120_1880 = (encode_formula t env')
in (_120_1881, _120_1880)))
end else begin
(let _120_1882 = (encode_typ_term t env')
in (app, _120_1882))
end
in (match (_54_2399) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _120_1889 = (let _120_1888 = (let _120_1887 = (let _120_1886 = (let _120_1885 = (let _120_1884 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _120_1883 = (FStar_ToSMT_Term.mkEq (def, body))
in (_120_1884, _120_1883)))
in (FStar_ToSMT_Term.mkImp _120_1885))
in (((def)::[])::[], vars, _120_1886))
in (FStar_ToSMT_Term.mkForall _120_1887))
in (_120_1888, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_120_1889))
in (let kindingAx = (let _54_2403 = (let _120_1890 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _120_1890 env' app))
in (match (_54_2403) with
| (k, decls) -> begin
(let _120_1898 = (let _120_1897 = (let _120_1896 = (let _120_1895 = (let _120_1894 = (let _120_1893 = (let _120_1892 = (let _120_1891 = (FStar_ToSMT_Term.mk_and_l guards)
in (_120_1891, k))
in (FStar_ToSMT_Term.mkImp _120_1892))
in (((app)::[])::[], vars, _120_1893))
in (FStar_ToSMT_Term.mkForall _120_1894))
in (_120_1895, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_120_1896))
in (_120_1897)::[])
in (FStar_List.append decls _120_1898))
end))
in (let g = (let _120_1899 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _120_1899))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _54_2410) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _54_2416, _54_2418) -> begin
(let _54_2423 = (encode_formula f env)
in (match (_54_2423) with
| (f, decls) -> begin
(let g = (let _120_1904 = (let _120_1903 = (let _120_1902 = (let _120_1901 = (let _120_1900 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _120_1900))
in Some (_120_1901))
in (f, _120_1902))
in FStar_ToSMT_Term.Assume (_120_1903))
in (_120_1904)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _54_2429, datas, quals, _54_2433) when (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(let _54_2439 = (new_typ_constant_and_tok_from_lid env t)
in (match (_54_2439) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _54_2442, _54_2444, _54_2446, _54_2448, _54_2450, _54_2452) when ((FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.FStar_Absyn_Syntax.str
in (let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _120_1906 = (let _120_1905 = (primitive_type_axioms t tname tsym)
in (decl)::_120_1905)
in (_120_1906, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _54_2462, datas, quals, _54_2466) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_19 -> (match (_54_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _54_2473 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _54_2483 = c
in (match (_54_2483) with
| (name, args, _54_2480, _54_2482) -> begin
(let _120_1912 = (let _120_1911 = (let _120_1910 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _120_1910, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_120_1911))
in (_120_1912)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _120_1918 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _120_1918 FStar_Option.isNone)))))) then begin
[]
end else begin
(let _54_2490 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_54_2490) with
| (xxsym, xx) -> begin
(let _54_2533 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _54_2493 l -> (match (_54_2493) with
| (out, decls) -> begin
(let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _54_2503 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_54_2503) with
| (args, res) -> begin
(let indices = (match ((let _120_1921 = (FStar_Absyn_Util.compress_typ res)
in _120_1921.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_54_2505, indices) -> begin
indices
end
| _54_2510 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _120_1926 = (let _120_1925 = (let _120_1924 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_120_1924, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _120_1925))
in (push_typ_var env a.FStar_Absyn_Syntax.v _120_1926))
end
| FStar_Util.Inr (x) -> begin
(let _120_1929 = (let _120_1928 = (let _120_1927 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_120_1927, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _120_1928))
in (push_term_var env x.FStar_Absyn_Syntax.v _120_1929))
end)) env))
in (let _54_2521 = (encode_args indices env)
in (match (_54_2521) with
| (indices, decls') -> begin
(let _54_2522 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (let eqs = (let _120_1936 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _120_1933 = (let _120_1932 = (FStar_ToSMT_Term.mkFreeV v)
in (_120_1932, a))
in (FStar_ToSMT_Term.mkEq _120_1933))
end
| FStar_Util.Inr (a) -> begin
(let _120_1935 = (let _120_1934 = (FStar_ToSMT_Term.mkFreeV v)
in (_120_1934, a))
in (FStar_ToSMT_Term.mkEq _120_1935))
end)) vars indices)
in (FStar_All.pipe_right _120_1936 FStar_ToSMT_Term.mk_and_l))
in (let _120_1941 = (let _120_1940 = (let _120_1939 = (let _120_1938 = (let _120_1937 = (mk_data_tester env l xx)
in (_120_1937, eqs))
in (FStar_ToSMT_Term.mkAnd _120_1938))
in (out, _120_1939))
in (FStar_ToSMT_Term.mkOr _120_1940))
in (_120_1941, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_54_2533) with
| (data_ax, decls) -> begin
(let _54_2536 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_54_2536) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _120_1942 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _120_1942 xx tapp))
in (let _120_1949 = (let _120_1948 = (let _120_1947 = (let _120_1946 = (let _120_1945 = (let _120_1944 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _120_1943 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _120_1944, _120_1943)))
in (FStar_ToSMT_Term.mkForall _120_1945))
in (_120_1946, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_120_1947))
in (_120_1948)::[])
in (FStar_List.append decls _120_1949)))
end))
end))
end))
end)
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _54_2548 = (match ((let _120_1950 = (FStar_Absyn_Util.compress_kind k)
in _120_1950.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _54_2544 -> begin
(false, [], k)
end)
in (match (_54_2548) with
| (is_kind_arrow, formals, res) -> begin
(let _54_2555 = (encode_binders None formals env)
in (match (_54_2555) with
| (vars, guards, env', binder_decls, _54_2554) -> begin
(let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _54_20 -> (match (_54_20) with
| FStar_Absyn_Syntax.Projector (_54_2561) -> begin
true
end
| _54_2564 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _54_21 -> (match (_54_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_54_2579) -> begin
(projectee (i + 1) tl)
end
| FStar_Util.Inr (x) -> begin
if (x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = "projectee") then begin
i
end else begin
(projectee (i + 1) tl)
end
end)
end))
in (let projectee_pos = (projectee 0 formals)
in (let _54_2594 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_54_2585, xx::suffix) -> begin
(xx, suffix)
end
| _54_2591 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_54_2594) with
| (xx, suffix) -> begin
(let dproj_app = (let _120_1964 = (let _120_1963 = (let _120_1962 = (mk_typ_projector_name d a)
in (let _120_1961 = (let _120_1960 = (FStar_ToSMT_Term.mkFreeV xx)
in (_120_1960)::[])
in (_120_1962, _120_1961)))
in (FStar_ToSMT_Term.mkApp _120_1963))
in (mk_ApplyT _120_1964 suffix))
in (let _120_1969 = (let _120_1968 = (let _120_1967 = (let _120_1966 = (let _120_1965 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _120_1965))
in (FStar_ToSMT_Term.mkForall _120_1966))
in (_120_1967, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_120_1968))
in (_120_1969)::[]))
end))))
end
| _54_2597 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _54_2603 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_54_2603) with
| (xxsym, xx) -> begin
(let _54_2606 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_54_2606) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _120_1982 = (let _120_1981 = (let _120_1980 = (let _120_1979 = (let _120_1978 = (let _120_1977 = (let _120_1976 = (let _120_1975 = (let _120_1974 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _120_1974))
in (FStar_ToSMT_Term.mkEq _120_1975))
in (xx_has_type, _120_1976))
in (FStar_ToSMT_Term.mkImp _120_1977))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _120_1978))
in (FStar_ToSMT_Term.mkForall _120_1979))
in (_120_1980, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_120_1981))
in (_120_1982)::[]))
end))
end)))
in (let _54_2611 = (new_typ_constant_and_tok_from_lid env t)
in (match (_54_2611) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _120_1984 = (let _120_1983 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _120_1983))
in (FStar_ToSMT_Term.mkApp _120_1984))
in (let _54_2632 = (let tname_decl = (let _120_1988 = (let _120_1987 = (FStar_All.pipe_right vars (FStar_List.map (fun _54_2617 -> (match (_54_2617) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _120_1986 = (varops.next_id ())
in (tname, _120_1987, FStar_ToSMT_Term.Type_sort, _120_1986)))
in (constructor_or_logic_type_decl _120_1988))
in (let _54_2629 = (match (vars) with
| [] -> begin
(let _120_1992 = (let _120_1991 = (let _120_1990 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _120_1989 -> Some (_120_1989)) _120_1990))
in (push_free_tvar env t tname _120_1991))
in ([], _120_1992))
end
| _54_2621 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _120_1993 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _120_1993))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (let name_tok_corr = (let _120_1997 = (let _120_1996 = (let _120_1995 = (let _120_1994 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _120_1994))
in (FStar_ToSMT_Term.mkForall' _120_1995))
in (_120_1996, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_120_1997))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_54_2629) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_54_2632) with
| (decls, env) -> begin
(let kindingAx = (let _54_2635 = (encode_knd res env' tapp)
in (match (_54_2635) with
| (k, decls) -> begin
(let karr = if is_kind_arrow then begin
(let _120_2001 = (let _120_2000 = (let _120_1999 = (let _120_1998 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _120_1998))
in (_120_1999, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_120_2000))
in (_120_2001)::[])
end else begin
[]
end
in (let _120_2007 = (let _120_2006 = (let _120_2005 = (let _120_2004 = (let _120_2003 = (let _120_2002 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _120_2002))
in (FStar_ToSMT_Term.mkForall _120_2003))
in (_120_2004, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_120_2005))
in (_120_2006)::[])
in (FStar_List.append (FStar_List.append decls karr) _120_2007)))
end))
in (let aux = if is_logical then begin
(let _120_2008 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _120_2008))
end else begin
(let _120_2015 = (let _120_2013 = (let _120_2011 = (let _120_2009 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _120_2009))
in (let _120_2010 = (inversion_axioms tapp vars)
in (FStar_List.append _120_2011 _120_2010)))
in (let _120_2012 = (projection_axioms tapp vars)
in (FStar_List.append _120_2013 _120_2012)))
in (let _120_2014 = (pretype_axioms tapp vars)
in (FStar_List.append _120_2015 _120_2014)))
end
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _54_2642, _54_2644, _54_2646, _54_2648, _54_2650) when (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_54_2656, tps, _54_2659), quals, _54_2663, drange) -> begin
(let t = (let _120_2017 = (FStar_List.map (fun _54_2670 -> (match (_54_2670) with
| (x, _54_2669) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _120_2017 t))
in (let _54_2675 = (new_term_constant_and_tok_from_lid env d)
in (match (_54_2675) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _54_2684 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_54_2684) with
| (formals, t_res) -> begin
(let _54_2687 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_54_2687) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _54_2694 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_54_2694) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _54_22 -> (match (_54_22) with
| FStar_Util.Inl (a) -> begin
(let _120_2019 = (mk_typ_projector_name d a)
in (_120_2019, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _120_2020 = (mk_term_projector_name d x)
in (_120_2020, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _120_2022 = (let _120_2021 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _120_2021))
in (FStar_All.pipe_right _120_2022 FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _54_2708 = (encode_typ_pred None t env ddtok_tm)
in (match (_54_2708) with
| (tok_typing, decls3) -> begin
(let _54_2715 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_54_2715) with
| (vars', guards', env'', decls_formals, _54_2714) -> begin
(let _54_2720 = (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_54_2720) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _54_2724 -> begin
(let _120_2024 = (let _120_2023 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _120_2023))
in (_120_2024)::[])
end)
in (let encode_elim = (fun _54_2727 -> (match (()) with
| () -> begin
(let _54_2730 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_54_2730) with
| (head, args) -> begin
(match ((let _120_2027 = (FStar_Absyn_Util.compress_typ head)
in _120_2027.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _54_2736 = (encode_args args env')
in (match (_54_2736) with
| (encoded_args, arg_decls) -> begin
(let _54_2760 = (FStar_List.fold_left (fun _54_2740 arg -> (match (_54_2740) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _54_2748 = (let _120_2030 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _120_2030))
in (match (_54_2748) with
| (_54_2745, tv, env) -> begin
(let _120_2032 = (let _120_2031 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_120_2031)::eqns)
in (env, (tv)::arg_vars, _120_2032))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _54_2755 = (let _120_2033 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _120_2033))
in (match (_54_2755) with
| (_54_2752, xv, env) -> begin
(let _120_2035 = (let _120_2034 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_120_2034)::eqns)
in (env, (xv)::arg_vars, _120_2035))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_54_2760) with
| (_54_2757, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _120_2042 = (let _120_2041 = (let _120_2040 = (let _120_2039 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _120_2038 = (let _120_2037 = (let _120_2036 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _120_2036))
in (FStar_ToSMT_Term.mkImp _120_2037))
in (((ty_pred)::[])::[], _120_2039, _120_2038)))
in (FStar_ToSMT_Term.mkForall _120_2040))
in (_120_2041, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_120_2042))
in (let subterm_ordering = if (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(let x = (let _120_2043 = (varops.fresh "x")
in (_120_2043, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _120_2053 = (let _120_2052 = (let _120_2051 = (let _120_2050 = (let _120_2045 = (let _120_2044 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_120_2044)::[])
in (_120_2045)::[])
in (let _120_2049 = (let _120_2048 = (let _120_2047 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _120_2046 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_120_2047, _120_2046)))
in (FStar_ToSMT_Term.mkImp _120_2048))
in (_120_2050, (x)::[], _120_2049)))
in (FStar_ToSMT_Term.mkForall _120_2051))
in (_120_2052, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_120_2053))))
end else begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _120_2056 = (let _120_2055 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _120_2055 dapp))
in (_120_2056)::[])
end
| _54_2775 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _120_2063 = (let _120_2062 = (let _120_2061 = (let _120_2060 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _120_2059 = (let _120_2058 = (let _120_2057 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _120_2057))
in (FStar_ToSMT_Term.mkImp _120_2058))
in (((ty_pred)::[])::[], _120_2060, _120_2059)))
in (FStar_ToSMT_Term.mkForall _120_2061))
in (_120_2062, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_120_2063)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _54_2779 -> begin
(let _54_2780 = (let _120_2066 = (let _120_2065 = (FStar_Absyn_Print.sli d)
in (let _120_2064 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _120_2065 _120_2064)))
in (FStar_Tc_Errors.warn drange _120_2066))
in ([], []))
end)
end))
end))
in (let _54_2784 = (encode_elim ())
in (match (_54_2784) with
| (decls2, elim) -> begin
(let g = (let _120_2091 = (let _120_2090 = (let _120_2075 = (let _120_2074 = (let _120_2073 = (let _120_2072 = (let _120_2071 = (let _120_2070 = (let _120_2069 = (let _120_2068 = (let _120_2067 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _120_2067))
in Some (_120_2068))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _120_2069))
in FStar_ToSMT_Term.DeclFun (_120_2070))
in (_120_2071)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _120_2072))
in (FStar_List.append _120_2073 proxy_fresh))
in (FStar_List.append _120_2074 decls_formals))
in (FStar_List.append _120_2075 decls_pred))
in (let _120_2089 = (let _120_2088 = (let _120_2087 = (let _120_2079 = (let _120_2078 = (let _120_2077 = (let _120_2076 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _120_2076))
in (FStar_ToSMT_Term.mkForall _120_2077))
in (_120_2078, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_120_2079))
in (let _120_2086 = (let _120_2085 = (let _120_2084 = (let _120_2083 = (let _120_2082 = (let _120_2081 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _120_2080 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _120_2081, _120_2080)))
in (FStar_ToSMT_Term.mkForall _120_2082))
in (_120_2083, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_120_2084))
in (_120_2085)::[])
in (_120_2087)::_120_2086))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_120_2088)
in (FStar_List.append _120_2090 _120_2089)))
in (FStar_List.append _120_2091 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end)))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _54_2788, _54_2790, _54_2792) -> begin
(let _54_2797 = (encode_signature env ses)
in (match (_54_2797) with
| (g, env) -> begin
(let _54_2809 = (FStar_All.pipe_right g (FStar_List.partition (fun _54_23 -> (match (_54_23) with
| FStar_ToSMT_Term.Assume (_54_2800, Some ("inversion axiom")) -> begin
false
end
| _54_2806 -> begin
true
end))))
in (match (_54_2809) with
| (g', inversions) -> begin
(let _54_2818 = (FStar_All.pipe_right g' (FStar_List.partition (fun _54_24 -> (match (_54_24) with
| FStar_ToSMT_Term.DeclFun (_54_2812) -> begin
true
end
| _54_2815 -> begin
false
end))))
in (match (_54_2818) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_54_2820, _54_2822, _54_2824, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_25 -> (match (_54_25) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _54_2836 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _54_2841, _54_2843, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _54_2855 = (FStar_Util.first_N nbinders formals)
in (match (_54_2855) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _120_2106 = (let _120_2105 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _120_2105))
in FStar_Util.Inl (_120_2106))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _120_2108 = (let _120_2107 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _120_2107))
in FStar_Util.Inr (_120_2108))
end
| _54_2869 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _120_2109 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _120_2109 FStar_Absyn_Util.name_binders))
in (let body = (let _120_2115 = (let _120_2111 = (let _120_2110 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _120_2110))
in (body, _120_2111))
in (let _120_2114 = (let _120_2113 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _120_2112 -> Some (_120_2112)) _120_2113))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _120_2115 _120_2114 body.FStar_Absyn_Syntax.pos)))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let nformals = (FStar_List.length formals)
in (let nbinders = (FStar_List.length binders)
in (let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(let _54_2907 = (FStar_Util.first_N nformals binders)
in (match (_54_2907) with
| (bs0, rest) -> begin
(let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _54_2911 -> begin
(FStar_All.failwith "impossible")
end)
in (let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(let _54_2916 = (eta_expand binders formals body tres)
in (match (_54_2916) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _54_2918 -> begin
(let _120_2124 = (let _120_2123 = (FStar_Absyn_Print.exp_to_string e)
in (let _120_2122 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Absyn_Syntax.str _120_2123 _120_2122)))
in (FStar_All.failwith _120_2124))
end)
end
| _54_2920 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (FStar_Absyn_Util.comp_result c)
in (let _54_2928 = (eta_expand [] formals e tres)
in (match (_54_2928) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _54_2930 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _54_2932 -> (match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_26 -> (match (_54_26) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _54_2943 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(let _54_2962 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _54_2949 lb -> (match (_54_2949) with
| (toks, typs, decls, env) -> begin
(let _54_2951 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (let t_norm = (let _120_2130 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _120_2130 FStar_Absyn_Util.compress_typ))
in (let _54_2957 = (let _120_2131 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _120_2131 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_54_2957) with
| (tok, decl, env) -> begin
(let _120_2134 = (let _120_2133 = (let _120_2132 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_120_2132, tok))
in (_120_2133)::toks)
in (_120_2134, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_54_2962) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _54_27 -> (match (_54_27) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _54_2969 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _120_2137 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _120_2137))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _54_2977; FStar_Absyn_Syntax.lbtyp = _54_2975; FStar_Absyn_Syntax.lbeff = _54_2973; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _54_2993 = (destruct_bound_function flid t_norm e)
in (match (_54_2993) with
| (binders, body, formals, tres) -> begin
(let _54_3000 = (encode_binders None binders env)
in (match (_54_3000) with
| (vars, guards, env', binder_decls, _54_2999) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _54_3003 -> begin
(let _120_2139 = (let _120_2138 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _120_2138))
in (FStar_ToSMT_Term.mkApp _120_2139))
end)
in (let _54_3007 = (encode_exp body env')
in (match (_54_3007) with
| (body, decls2) -> begin
(let eqn = (let _120_2148 = (let _120_2147 = (let _120_2144 = (let _120_2143 = (let _120_2142 = (let _120_2141 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _120_2140 = (FStar_ToSMT_Term.mkEq (app, body))
in (_120_2141, _120_2140)))
in (FStar_ToSMT_Term.mkImp _120_2142))
in (((app)::[])::[], vars, _120_2143))
in (FStar_ToSMT_Term.mkForall _120_2144))
in (let _120_2146 = (let _120_2145 = (FStar_Util.format1 "Equation for %s" flid.FStar_Absyn_Syntax.str)
in Some (_120_2145))
in (_120_2147, _120_2146)))
in FStar_ToSMT_Term.Assume (_120_2148))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _54_3010 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let fuel = (let _120_2149 = (varops.fresh "fuel")
in (_120_2149, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _54_3027 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _54_3016 _54_3021 -> (match ((_54_3016, _54_3021)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _120_2154 = (let _120_2153 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _120_2152 -> Some (_120_2152)) _120_2153))
in (push_free_var env flid gtok _120_2154))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_54_3027) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _54_3036 t_norm _54_3045 -> (match ((_54_3036, _54_3045)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _54_3044; FStar_Absyn_Syntax.lbtyp = _54_3042; FStar_Absyn_Syntax.lbeff = _54_3040; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _54_3050 = (destruct_bound_function flid t_norm e)
in (match (_54_3050) with
| (binders, body, formals, tres) -> begin
(let _54_3057 = (encode_binders None binders env)
in (match (_54_3057) with
| (vars, guards, env', binder_decls, _54_3056) -> begin
(let decl_g = (let _120_2165 = (let _120_2164 = (let _120_2163 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_120_2163)
in (g, _120_2164, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_120_2165))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _120_2168 = (let _120_2167 = (let _120_2166 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_120_2166)::vars_tm)
in (g, _120_2167))
in (FStar_ToSMT_Term.mkApp _120_2168))
in (let gmax = (let _120_2171 = (let _120_2170 = (let _120_2169 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_120_2169)::vars_tm)
in (g, _120_2170))
in (FStar_ToSMT_Term.mkApp _120_2171))
in (let _54_3067 = (encode_exp body env')
in (match (_54_3067) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _120_2180 = (let _120_2179 = (let _120_2176 = (let _120_2175 = (let _120_2174 = (let _120_2173 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _120_2172 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_120_2173, _120_2172)))
in (FStar_ToSMT_Term.mkImp _120_2174))
in (((gsapp)::[])::[], (fuel)::vars, _120_2175))
in (FStar_ToSMT_Term.mkForall _120_2176))
in (let _120_2178 = (let _120_2177 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Absyn_Syntax.str)
in Some (_120_2177))
in (_120_2179, _120_2178)))
in FStar_ToSMT_Term.Assume (_120_2180))
in (let eqn_f = (let _120_2184 = (let _120_2183 = (let _120_2182 = (let _120_2181 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _120_2181))
in (FStar_ToSMT_Term.mkForall _120_2182))
in (_120_2183, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_120_2184))
in (let eqn_g' = (let _120_2193 = (let _120_2192 = (let _120_2191 = (let _120_2190 = (let _120_2189 = (let _120_2188 = (let _120_2187 = (let _120_2186 = (let _120_2185 = (FStar_ToSMT_Term.n_fuel 0)
in (_120_2185)::vars_tm)
in (g, _120_2186))
in (FStar_ToSMT_Term.mkApp _120_2187))
in (gsapp, _120_2188))
in (FStar_ToSMT_Term.mkEq _120_2189))
in (((gsapp)::[])::[], (fuel)::vars, _120_2190))
in (FStar_ToSMT_Term.mkForall _120_2191))
in (_120_2192, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_120_2193))
in (let _54_3090 = (let _54_3077 = (encode_binders None formals env0)
in (match (_54_3077) with
| (vars, v_guards, env, binder_decls, _54_3076) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _120_2194 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _120_2194 ((fuel)::vars)))
in (let _120_2198 = (let _120_2197 = (let _120_2196 = (let _120_2195 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _120_2195))
in (FStar_ToSMT_Term.mkForall _120_2196))
in (_120_2197, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_120_2198)))
in (let _54_3087 = (let _54_3084 = (encode_typ_pred None tres env gapp)
in (match (_54_3084) with
| (g_typing, d3) -> begin
(let _120_2206 = (let _120_2205 = (let _120_2204 = (let _120_2203 = (let _120_2202 = (let _120_2201 = (let _120_2200 = (let _120_2199 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_120_2199, g_typing))
in (FStar_ToSMT_Term.mkImp _120_2200))
in (((gapp)::[])::[], (fuel)::vars, _120_2201))
in (FStar_ToSMT_Term.mkForall _120_2202))
in (_120_2203, None))
in FStar_ToSMT_Term.Assume (_120_2204))
in (_120_2205)::[])
in (d3, _120_2206))
end))
in (match (_54_3087) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_54_3090) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _54_3106 = (let _120_2209 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _54_3094 _54_3098 -> (match ((_54_3094, _54_3098)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _54_3102 = (encode_one_binding env0 gtok ty bs)
in (match (_54_3102) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _120_2209))
in (match (_54_3106) with
| (decls, eqns, env0) -> begin
(let _54_3115 = (let _120_2211 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _120_2211 (FStar_List.partition (fun _54_28 -> (match (_54_28) with
| FStar_ToSMT_Term.DeclFun (_54_3109) -> begin
true
end
| _54_3112 -> begin
false
end)))))
in (match (_54_3115) with
| (prefix_decls, rest) -> begin
(let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _54_2931 -> (match (_54_2931) with
| Let_rec_unencodeable -> begin
(let msg = (let _120_2214 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _120_2214 (FStar_String.concat " and ")))
in (let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _54_3142 = (encode_free_var env x t t_norm [])
in (match (_54_3142) with
| (decls, env) -> begin
(let _54_3147 = (lookup_lid env x)
in (match (_54_3147) with
| (n, x', _54_3146) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _54_3151) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _54_3159 = (encode_function_type_as_formula None None t env)
in (match (_54_3159) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> if ((let _120_2227 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _120_2227)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(let _54_3168 = (new_term_constant_and_tok_from_lid env lid)
in (match (_54_3168) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _54_3171) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _54_29 -> (match (_54_29) with
| (FStar_Util.Inl (_54_3176), _54_3179) -> begin
FStar_ToSMT_Term.Type_sort
end
| _54_3182 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _54_3184 -> begin
[]
end)
in (let d = FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(let encode_non_total_function_typ = (lid.FStar_Absyn_Syntax.nsstr <> "Prims")
in (let _54_3201 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _120_2229 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _120_2229))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_54_3201) with
| (formals, (pre_opt, res_t)) -> begin
(let _54_3205 = (new_term_constant_and_tok_from_lid env lid)
in (match (_54_3205) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _54_3208 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _54_30 -> (match (_54_30) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _54_3224 = (FStar_Util.prefix vars)
in (match (_54_3224) with
| (_54_3219, (xxsym, _54_3222)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _120_2246 = (let _120_2245 = (let _120_2244 = (let _120_2243 = (let _120_2242 = (let _120_2241 = (let _120_2240 = (let _120_2239 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Absyn_Syntax.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _120_2239))
in (vapp, _120_2240))
in (FStar_ToSMT_Term.mkEq _120_2241))
in (((vapp)::[])::[], vars, _120_2242))
in (FStar_ToSMT_Term.mkForall _120_2243))
in (_120_2244, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_120_2245))
in (_120_2246)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _54_3237 = (FStar_Util.prefix vars)
in (match (_54_3237) with
| (_54_3232, (xxsym, _54_3235)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _120_2248 = (let _120_2247 = (mk_term_projector_name d f)
in (_120_2247, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _120_2248))
in (let _120_2253 = (let _120_2252 = (let _120_2251 = (let _120_2250 = (let _120_2249 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _120_2249))
in (FStar_ToSMT_Term.mkForall _120_2250))
in (_120_2251, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_120_2252))
in (_120_2253)::[])))
end))
end
| _54_3241 -> begin
[]
end)))))
in (let _54_3248 = (encode_binders None formals env)
in (match (_54_3248) with
| (vars, guards, env', decls1, _54_3247) -> begin
(let _54_3257 = (match (pre_opt) with
| None -> begin
(let _120_2254 = (FStar_ToSMT_Term.mk_and_l guards)
in (_120_2254, decls1))
end
| Some (p) -> begin
(let _54_3254 = (encode_formula p env')
in (match (_54_3254) with
| (g, ds) -> begin
(let _120_2255 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_120_2255, (FStar_List.append decls1 ds)))
end))
end)
in (match (_54_3257) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _120_2257 = (let _120_2256 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _120_2256))
in (FStar_ToSMT_Term.mkApp _120_2257))
in (let _54_3288 = (let vname_decl = (let _120_2260 = (let _120_2259 = (FStar_All.pipe_right formals (FStar_List.map (fun _54_31 -> (match (_54_31) with
| (FStar_Util.Inl (_54_3262), _54_3265) -> begin
FStar_ToSMT_Term.Type_sort
end
| _54_3268 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _120_2259, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_120_2260))
in (let _54_3275 = (let env = (let _54_3270 = env
in {bindings = _54_3270.bindings; depth = _54_3270.depth; tcenv = _54_3270.tcenv; warn = _54_3270.warn; cache = _54_3270.cache; nolabels = _54_3270.nolabels; use_zfuel_name = _54_3270.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_54_3275) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _54_3285 = (match (formals) with
| [] -> begin
(let _120_2264 = (let _120_2263 = (let _120_2262 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _120_2261 -> Some (_120_2261)) _120_2262))
in (push_free_var env lid vname _120_2263))
in ((FStar_List.append decls2 ((tok_typing)::[])), _120_2264))
end
| _54_3279 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _120_2265 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _120_2265))
in (let name_tok_corr = (let _120_2269 = (let _120_2268 = (let _120_2267 = (let _120_2266 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _120_2266))
in (FStar_ToSMT_Term.mkForall _120_2267))
in (_120_2268, None))
in FStar_ToSMT_Term.Assume (_120_2269))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_54_3285) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_54_3288) with
| (decls2, env) -> begin
(let _54_3296 = (let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (let _54_3292 = (encode_typ_term res_t env')
in (match (_54_3292) with
| (encoded_res_t, decls) -> begin
(let _120_2270 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _120_2270, decls))
end)))
in (match (_54_3296) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _120_2274 = (let _120_2273 = (let _120_2272 = (let _120_2271 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _120_2271))
in (FStar_ToSMT_Term.mkForall _120_2272))
in (_120_2273, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_120_2274))
in (let g = (let _120_2276 = (let _120_2275 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_120_2275)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _120_2276))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _54_3303 se -> (match (_54_3303) with
| (g, env) -> begin
(let _54_3307 = (encode_sigelt env se)
in (match (_54_3307) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _54_3314 -> (match (_54_3314) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _54_3322 = (new_term_constant env x)
in (match (_54_3322) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _54_3324 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _120_2291 = (FStar_Absyn_Print.strBvd x)
in (let _120_2290 = (FStar_Absyn_Print.typ_to_string t0)
in (let _120_2289 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _120_2291 _120_2290 _120_2289))))
end else begin
()
end
in (let _54_3328 = (encode_typ_pred None t1 env xx)
in (match (_54_3328) with
| (t, decls') -> begin
(let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _120_2295 = (let _120_2294 = (FStar_Absyn_Print.strBvd x)
in (let _120_2293 = (FStar_Absyn_Print.typ_to_string t0)
in (let _120_2292 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _120_2294 _120_2293 _120_2292))))
in Some (_120_2295))
end else begin
None
end
in (let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let _54_3338 = (new_typ_constant env a)
in (match (_54_3338) with
| (aasym, aa, env') -> begin
(let _54_3341 = (encode_knd k env aa)
in (match (_54_3341) with
| (k, decls') -> begin
(let g = (let _120_2301 = (let _120_2300 = (let _120_2299 = (let _120_2298 = (let _120_2297 = (let _120_2296 = (FStar_Absyn_Print.strBvd a)
in Some (_120_2296))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _120_2297))
in FStar_ToSMT_Term.DeclFun (_120_2298))
in (_120_2299)::[])
in (FStar_List.append _120_2300 decls'))
in (FStar_List.append _120_2301 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _54_3350 = (encode_free_var env x t t_norm [])
in (match (_54_3350) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(let _54_3355 = (encode_sigelt env se)
in (match (_54_3355) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _54_3362 -> (match (_54_3362) with
| (l, _54_3359, _54_3361) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _54_3369 -> (match (_54_3369) with
| (l, _54_3366, _54_3368) -> begin
(let _120_2309 = (FStar_All.pipe_left (fun _120_2305 -> FStar_ToSMT_Term.Echo (_120_2305)) (Prims.fst l))
in (let _120_2308 = (let _120_2307 = (let _120_2306 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_120_2306))
in (_120_2307)::[])
in (_120_2309)::_120_2308))
end))))
in (prefix, suffix))))

let last_env = (FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _120_2314 = (let _120_2313 = (let _120_2312 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _120_2312; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_120_2313)::[])
in (FStar_ST.op_Colon_Equals last_env _120_2314)))

let get_env = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_54_3375 -> begin
(let _54_3378 = e
in {bindings = _54_3378.bindings; depth = _54_3378.depth; tcenv = tcenv; warn = _54_3378.warn; cache = _54_3378.cache; nolabels = _54_3378.nolabels; use_zfuel_name = _54_3378.use_zfuel_name; encode_non_total_function_typ = _54_3378.encode_non_total_function_typ})
end))

let set_env = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _54_3384::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun _54_3386 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _54_3392 = hd
in {bindings = _54_3392.bindings; depth = _54_3392.depth; tcenv = _54_3392.tcenv; warn = _54_3392.warn; cache = refs; nolabels = _54_3392.nolabels; use_zfuel_name = _54_3392.use_zfuel_name; encode_non_total_function_typ = _54_3392.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun _54_3395 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _54_3399::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun _54_3401 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _54_3402 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _54_3403 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_54_3406::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _54_3411 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init = (fun tcenv -> (let _54_3413 = (init_env tcenv)
in (let _54_3415 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _54_3418 = (push_env ())
in (let _54_3420 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _54_3423 = (let _120_2335 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _120_2335))
in (let _54_3425 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _54_3428 = (mark_env ())
in (let _54_3430 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _54_3433 = (reset_mark_env ())
in (let _54_3435 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _54_3438 = (commit_mark_env ())
in (let _54_3440 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _120_2349 = (let _120_2348 = (let _120_2347 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _120_2347))
in FStar_ToSMT_Term.Caption (_120_2348))
in (_120_2349)::decls)
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _54_3449 = (encode_sigelt env se)
in (match (_54_3449) with
| (decls, env) -> begin
(let _54_3450 = (set_env env)
in (let _120_2350 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _120_2350)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let _54_3455 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _120_2355 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _120_2355))
end else begin
()
end
in (let env = (get_env tcenv)
in (let _54_3462 = (encode_signature (let _54_3458 = env
in {bindings = _54_3458.bindings; depth = _54_3458.depth; tcenv = _54_3458.tcenv; warn = false; cache = _54_3458.cache; nolabels = _54_3458.nolabels; use_zfuel_name = _54_3458.use_zfuel_name; encode_non_total_function_typ = _54_3458.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_54_3462) with
| (decls, env) -> begin
(let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _54_3468 = (set_env (let _54_3466 = env
in {bindings = _54_3466.bindings; depth = _54_3466.depth; tcenv = _54_3466.tcenv; warn = true; cache = _54_3466.cache; nolabels = _54_3466.nolabels; use_zfuel_name = _54_3466.use_zfuel_name; encode_non_total_function_typ = _54_3466.encode_non_total_function_typ}))
in (let _54_3470 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _54_3475 = (let _120_2364 = (let _120_2363 = (let _120_2362 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _120_2362))
in (FStar_Util.format1 "Starting query at %s" _120_2363))
in (push _120_2364))
in (let pop = (fun _54_3478 -> (match (()) with
| () -> begin
(let _120_2369 = (let _120_2368 = (let _120_2367 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _120_2367))
in (FStar_Util.format1 "Ending query at %s" _120_2368))
in (pop _120_2369))
end))
in (let _54_3537 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _54_3511 = (let rec aux = (fun bindings -> (match (bindings) with
| FStar_Tc_Env.Binding_var (x, t)::rest -> begin
(let _54_3493 = (aux rest)
in (match (_54_3493) with
| (out, rest) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _120_2375 = (let _120_2374 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_120_2374)::out)
in (_120_2375, rest)))
end))
end
| FStar_Tc_Env.Binding_typ (a, k)::rest -> begin
(let _54_3503 = (aux rest)
in (match (_54_3503) with
| (out, rest) -> begin
(let _120_2377 = (let _120_2376 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_120_2376)::out)
in (_120_2377, rest))
end))
end
| _54_3505 -> begin
([], bindings)
end))
in (let _54_3508 = (aux bindings)
in (match (_54_3508) with
| (closing, bindings) -> begin
(let _120_2378 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in (_120_2378, bindings))
end)))
in (match (_54_3511) with
| (q, bindings) -> begin
(let _54_3520 = (let _120_2380 = (FStar_List.filter (fun _54_32 -> (match (_54_32) with
| FStar_Tc_Env.Binding_sig (_54_3514) -> begin
false
end
| _54_3517 -> begin
true
end)) bindings)
in (encode_env_bindings env _120_2380))
in (match (_54_3520) with
| (env_decls, env) -> begin
(let _54_3521 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _120_2381 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _120_2381))
end else begin
()
end
in (let _54_3526 = (encode_formula_with_labels q env)
in (match (_54_3526) with
| (phi, labels, qdecls) -> begin
(let _54_3529 = (encode_labels labels)
in (match (_54_3529) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _120_2383 = (let _120_2382 = (FStar_ToSMT_Term.mkNot phi)
in (_120_2382, Some ("query")))
in FStar_ToSMT_Term.Assume (_120_2383))
in (let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))
end))))
in (match (_54_3537) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _54_3544); FStar_ToSMT_Term.hash = _54_3541; FStar_ToSMT_Term.freevars = _54_3539}, _54_3549) -> begin
(let _54_3552 = (pop ())
in ())
end
| _54_3555 when tcenv.FStar_Tc_Env.admit -> begin
(let _54_3556 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _54_3560) -> begin
(let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (let _54_3564 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _54_3570 -> (match (_54_3570) with
| (n, i) -> begin
(let _120_2406 = (let _120_2405 = (let _120_2390 = (let _120_2389 = (FStar_Util.string_of_int n)
in (let _120_2388 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _120_2389 _120_2388)))
in FStar_ToSMT_Term.Caption (_120_2390))
in (let _120_2404 = (let _120_2403 = (let _120_2395 = (let _120_2394 = (let _120_2393 = (let _120_2392 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _120_2391 = (FStar_ToSMT_Term.n_fuel n)
in (_120_2392, _120_2391)))
in (FStar_ToSMT_Term.mkEq _120_2393))
in (_120_2394, None))
in FStar_ToSMT_Term.Assume (_120_2395))
in (let _120_2402 = (let _120_2401 = (let _120_2400 = (let _120_2399 = (let _120_2398 = (let _120_2397 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _120_2396 = (FStar_ToSMT_Term.n_fuel i)
in (_120_2397, _120_2396)))
in (FStar_ToSMT_Term.mkEq _120_2398))
in (_120_2399, None))
in FStar_ToSMT_Term.Assume (_120_2400))
in (_120_2401)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_120_2403)::_120_2402))
in (_120_2405)::_120_2404))
in (FStar_List.append _120_2406 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _120_2410 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _120_2409 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_120_2410, _120_2409)))
in (let alt_configs = (let _120_2429 = (let _120_2428 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _120_2413 = (let _120_2412 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _120_2411 = (FStar_ST.read FStar_Options.max_ifuel)
in (_120_2412, _120_2411)))
in (_120_2413)::[])
end else begin
[]
end
in (let _120_2427 = (let _120_2426 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _120_2416 = (let _120_2415 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _120_2414 = (FStar_ST.read FStar_Options.max_ifuel)
in (_120_2415, _120_2414)))
in (_120_2416)::[])
end else begin
[]
end
in (let _120_2425 = (let _120_2424 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _120_2419 = (let _120_2418 = (FStar_ST.read FStar_Options.max_fuel)
in (let _120_2417 = (FStar_ST.read FStar_Options.max_ifuel)
in (_120_2418, _120_2417)))
in (_120_2419)::[])
end else begin
[]
end
in (let _120_2423 = (let _120_2422 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _120_2421 = (let _120_2420 = (FStar_ST.read FStar_Options.min_fuel)
in (_120_2420, 1))
in (_120_2421)::[])
end else begin
[]
end
in (_120_2422)::[])
in (_120_2424)::_120_2423))
in (_120_2426)::_120_2425))
in (_120_2428)::_120_2427))
in (FStar_List.flatten _120_2429))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _54_3579 -> begin
errs
end)
in (let _54_3581 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _120_2437 = (let _120_2432 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _120_2432))
in (let _120_2436 = (let _120_2433 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _120_2433 FStar_Util.string_of_int))
in (let _120_2435 = (let _120_2434 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _120_2434 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _120_2437 _120_2436 _120_2435))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _54_33 -> (match (_54_33) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _120_2448 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _120_2448 (cb mi p [])))
end
| _54_3593 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _120_2450 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _120_2450 (fun _54_3599 -> (match (_54_3599) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _54_3602 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _54_3605 p alt _54_3610 -> (match ((_54_3605, _54_3610)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _120_2458 = (let _120_2455 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _120_2455))
in (let _120_2457 = (FStar_Util.string_of_int prev_fuel)
in (let _120_2456 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _120_2458 _120_2457 _120_2456))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _120_2459 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _120_2459 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let _54_3615 = (let _120_2465 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _120_2465 q))
in (match (_54_3615) with
| (b, cb) -> begin
if b then begin
(FStar_ToSMT_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (let _54_3616 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _54_3621 = (push "query")
in (let _54_3628 = (encode_formula_with_labels q env)
in (match (_54_3628) with
| (f, _54_3625, _54_3627) -> begin
(let _54_3629 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _54_3633) -> begin
true
end
| _54_3637 -> begin
false
end))
end)))))

let solver = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

let dummy = {FStar_Tc_Env.init = (fun _54_3638 -> ()); FStar_Tc_Env.push = (fun _54_3640 -> ()); FStar_Tc_Env.pop = (fun _54_3642 -> ()); FStar_Tc_Env.mark = (fun _54_3644 -> ()); FStar_Tc_Env.reset_mark = (fun _54_3646 -> ()); FStar_Tc_Env.commit_mark = (fun _54_3648 -> ()); FStar_Tc_Env.encode_modul = (fun _54_3650 _54_3652 -> ()); FStar_Tc_Env.encode_sig = (fun _54_3654 _54_3656 -> ()); FStar_Tc_Env.solve = (fun _54_3658 _54_3660 -> ()); FStar_Tc_Env.is_trivial = (fun _54_3662 _54_3664 -> false); FStar_Tc_Env.finish = (fun _54_3666 -> ()); FStar_Tc_Env.refresh = (fun _54_3667 -> ())}




