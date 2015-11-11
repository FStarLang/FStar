
open Prims
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _53_39 -> (match (_53_39) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (FStar_List.filter (fun _53_1 -> (match (_53_1) with
| (FStar_Util.Inl (_53_43), _53_46) -> begin
false
end
| _53_49 -> begin
true
end)) args))

let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText a.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)

let mk_typ_projector_name = (fun lid a -> (let _119_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _119_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _119_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _119_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _119_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _119_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _53_61 -> (match (()) with
| () -> begin
(let _119_30 = (let _119_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _119_29 lid.FStar_Absyn_Syntax.str))
in (FStar_All.failwith _119_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _119_31 = (FStar_Absyn_Util.compress_typ t)
in _119_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_65) -> begin
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
| _53_74 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun lid i -> (let _119_37 = (let _119_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str _119_36))
in (FStar_All.pipe_left escape _119_37)))

let mk_typ_projector = (fun lid a -> (let _119_43 = (let _119_42 = (mk_typ_projector_name lid a)
in (_119_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _119_43)))

let mk_term_projector = (fun lid a -> (let _119_49 = (let _119_48 = (mk_term_projector_name lid a)
in (_119_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _119_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _119_55 = (let _119_54 = (mk_term_projector_name_by_pos lid i)
in (_119_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _119_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t")))

let varops = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _53_100 -> (match (()) with
| () -> begin
(let _119_159 = (FStar_Util.smap_create 100)
in (let _119_158 = (FStar_Util.smap_create 100)
in (_119_159, _119_158)))
end))
in (let scopes = (let _119_161 = (let _119_160 = (new_scope ())
in (_119_160)::[])
in (FStar_Util.mk_ref _119_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _119_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _119_165 (fun _53_108 -> (match (_53_108) with
| (names, _53_107) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_53_111) -> begin
(let _53_113 = (FStar_Util.incr ctr)
in (let _119_167 = (let _119_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _119_166))
in (Prims.strcat (Prims.strcat y "__") _119_167)))
end)
in (let top_scope = (let _119_169 = (let _119_168 = (FStar_ST.read scopes)
in (FStar_List.hd _119_168))
in (FStar_All.pipe_left Prims.fst _119_169))
in (let _53_117 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _119_175 = (let _119_174 = (FStar_All.pipe_left mk_unique pp.FStar_Absyn_Syntax.idText)
in (Prims.strcat _119_174 "__"))
in (Prims.strcat _119_175 rn.FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Absyn_Syntax.str))
in (let next_id = (fun _53_125 -> (match (()) with
| () -> begin
(let _53_126 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _119_183 = (let _119_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _119_182))
in (FStar_Util.format2 "%s_%s" pfx _119_183)))
in (let string_const = (fun s -> (match ((let _119_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _119_187 (fun _53_135 -> (match (_53_135) with
| (_53_133, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _119_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _119_188))
in (let top_scope = (let _119_190 = (let _119_189 = (FStar_ST.read scopes)
in (FStar_List.hd _119_189))
in (FStar_All.pipe_left Prims.snd _119_190))
in (let _53_142 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _53_145 -> (match (()) with
| () -> begin
(let _119_195 = (let _119_194 = (new_scope ())
in (let _119_193 = (FStar_ST.read scopes)
in (_119_194)::_119_193))
in (FStar_ST.op_Colon_Equals scopes _119_195))
end))
in (let pop = (fun _53_147 -> (match (()) with
| () -> begin
(let _119_199 = (let _119_198 = (FStar_ST.read scopes)
in (FStar_List.tl _119_198))
in (FStar_ST.op_Colon_Equals scopes _119_199))
end))
in (let mark = (fun _53_149 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _53_151 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _53_153 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _53_166 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _53_171 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _53_174 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (let _119_215 = (let _119_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _119_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_119_214, _119_213)))
in (FStar_Absyn_Util.mkbvd _119_215)))

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
| Binding_var (_53_179) -> begin
_53_179
end))

let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_53_182) -> begin
_53_182
end))

let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_53_185) -> begin
_53_185
end))

let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_53_188) -> begin
_53_188
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t")))

let print_env = (fun e -> (let _119_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _53_2 -> (match (_53_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _53_213) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _119_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _119_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_119_311))
end else begin
None
end)

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _119_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _119_316))))

let gen_term_var = (fun env x -> (let ysym = (let _119_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _119_321))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _53_232 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _53_232.tcenv; warn = _53_232.warn; cache = _53_232.cache; nolabels = _53_232.nolabels; use_zfuel_name = _53_232.use_zfuel_name; encode_non_total_function_typ = _53_232.encode_non_total_function_typ})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _53_238 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _53_238.depth; tcenv = _53_238.tcenv; warn = _53_238.warn; cache = _53_238.cache; nolabels = _53_238.nolabels; use_zfuel_name = _53_238.use_zfuel_name; encode_non_total_function_typ = _53_238.encode_non_total_function_typ})))))

let push_term_var = (fun env x t -> (let _53_243 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _53_243.depth; tcenv = _53_243.tcenv; warn = _53_243.warn; cache = _53_243.cache; nolabels = _53_243.nolabels; use_zfuel_name = _53_243.use_zfuel_name; encode_non_total_function_typ = _53_243.encode_non_total_function_typ}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _53_3 -> (match (_53_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _53_253 -> begin
None
end)))) with
| None -> begin
(let _119_336 = (let _119_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _119_335))
in (FStar_All.failwith _119_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _119_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _119_341))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _53_263 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _53_263.tcenv; warn = _53_263.warn; cache = _53_263.cache; nolabels = _53_263.nolabels; use_zfuel_name = _53_263.use_zfuel_name; encode_non_total_function_typ = _53_263.encode_non_total_function_typ})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _53_269 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _53_269.depth; tcenv = _53_269.tcenv; warn = _53_269.warn; cache = _53_269.cache; nolabels = _53_269.nolabels; use_zfuel_name = _53_269.use_zfuel_name; encode_non_total_function_typ = _53_269.encode_non_total_function_typ})))))

let push_typ_var = (fun env x t -> (let _53_274 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _53_274.depth; tcenv = _53_274.tcenv; warn = _53_274.warn; cache = _53_274.cache; nolabels = _53_274.nolabels; use_zfuel_name = _53_274.use_zfuel_name; encode_non_total_function_typ = _53_274.encode_non_total_function_typ}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _53_4 -> (match (_53_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _53_284 -> begin
None
end)))) with
| None -> begin
(let _119_356 = (let _119_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _119_355))
in (FStar_All.failwith _119_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _119_367 = (let _53_294 = env
in (let _119_366 = (let _119_365 = (let _119_364 = (let _119_363 = (let _119_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _119_361 -> Some (_119_361)) _119_362))
in (x, fname, _119_363, None))
in Binding_fvar (_119_364))
in (_119_365)::env.bindings)
in {bindings = _119_366; depth = _53_294.depth; tcenv = _53_294.tcenv; warn = _53_294.warn; cache = _53_294.cache; nolabels = _53_294.nolabels; use_zfuel_name = _53_294.use_zfuel_name; encode_non_total_function_typ = _53_294.encode_non_total_function_typ}))
in (fname, ftok, _119_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _53_5 -> (match (_53_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _53_306 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _119_378 = (let _119_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _119_377))
in (FStar_All.failwith _119_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _53_316 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _53_316.depth; tcenv = _53_316.tcenv; warn = _53_316.warn; cache = _53_316.cache; nolabels = _53_316.nolabels; use_zfuel_name = _53_316.use_zfuel_name; encode_non_total_function_typ = _53_316.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _53_325 = (lookup_lid env x)
in (match (_53_325) with
| (t1, t2, _53_324) -> begin
(let t3 = (let _119_395 = (let _119_394 = (let _119_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_119_393)::[])
in (f, _119_394))
in (FStar_ToSMT_Term.mkApp _119_395))
in (let _53_327 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _53_327.depth; tcenv = _53_327.tcenv; warn = _53_327.warn; cache = _53_327.cache; nolabels = _53_327.nolabels; use_zfuel_name = _53_327.use_zfuel_name; encode_non_total_function_typ = _53_327.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun env a -> (let _53_334 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_334) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _53_338 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_53_342, fuel::[]) -> begin
if (let _119_399 = (let _119_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _119_398 Prims.fst))
in (FStar_Util.starts_with _119_399 "fuel")) then begin
(let _119_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _119_400 fuel))
end else begin
t
end
end
| _53_348 -> begin
t
end)
end
| _53_350 -> begin
(let _119_402 = (let _119_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _119_401))
in (FStar_All.failwith _119_402))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _53_358 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_358) with
| (x, _53_355, _53_357) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _53_364 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_364) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _53_368; FStar_ToSMT_Term.freevars = _53_366}) when env.use_zfuel_name -> begin
(g, zf)
end
| _53_376 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _53_386 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _119_417 = (let _53_391 = env
in (let _119_416 = (let _119_415 = (let _119_414 = (let _119_413 = (let _119_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _119_411 -> Some (_119_411)) _119_412))
in (x, fname, _119_413))
in Binding_ftvar (_119_414))
in (_119_415)::env.bindings)
in {bindings = _119_416; depth = _53_391.depth; tcenv = _53_391.tcenv; warn = _53_391.warn; cache = _53_391.cache; nolabels = _53_391.nolabels; use_zfuel_name = _53_391.use_zfuel_name; encode_non_total_function_typ = _53_391.encode_non_total_function_typ}))
in (fname, ftok, _119_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _53_6 -> (match (_53_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _53_402 -> begin
None
end)))) with
| None -> begin
(let _119_424 = (let _119_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _119_423))
in (FStar_All.failwith _119_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _53_410 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _53_410.depth; tcenv = _53_410.tcenv; warn = _53_410.warn; cache = _53_410.cache; nolabels = _53_410.nolabels; use_zfuel_name = _53_410.use_zfuel_name; encode_non_total_function_typ = _53_410.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _119_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _119_435 Prims.snd))) with
| None -> begin
(let _119_437 = (let _119_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _119_436))
in (FStar_All.failwith _119_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _119_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _119_440 Prims.fst)))

let tok_of_name = (fun env nm -> (FStar_Util.find_map env.bindings (fun _53_7 -> (match (_53_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _53_435 -> begin
None
end))))

let mkForall_fuel' = (fun n _53_440 -> (match (_53_440) with
| (pats, vars, body) -> begin
(let fallback = (fun _53_442 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(let _53_445 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_445) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _53_455 -> begin
p
end)))))
in (let pats = (FStar_List.map add_fuel pats)
in (let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _119_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _119_453))
end
| _53_468 -> begin
(let _119_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _119_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _53_471 -> begin
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
(let _119_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _119_460 FStar_Option.isNone))
end
| _53_509 -> begin
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

let trivial_post = (fun t -> (let _119_482 = (let _119_481 = (let _119_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_119_479)::[])
in (let _119_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_119_481, _119_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _119_482 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _119_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _119_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _119_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _119_490))
end
| _53_526 -> begin
(let _119_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _119_491))
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
(let _119_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _119_504))
end
| _53_541 -> begin
(let _119_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _119_505))
end)) t)))

let mk_ApplyT_args = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app = (fun _53_8 -> (match (_53_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _53_560 -> begin
false
end))

let is_eta = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _53_571; FStar_ToSMT_Term.freevars = _53_569}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _53_589) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _53_596 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_53_598, []) -> begin
(let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _53_604 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)

type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}

let is_Mkpattern = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern")))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const = (fun _53_9 -> (match (_53_9) with
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
(let _119_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _119_561))
end
| FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _119_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _119_562))
end
| FStar_Absyn_Syntax.Const_int (i) -> begin
(let _119_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _119_563))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _119_567 = (let _119_566 = (let _119_565 = (let _119_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _119_564))
in (_119_565)::[])
in ("FStar.Int32.Int32", _119_566))
in (FStar_ToSMT_Term.mkApp _119_567))
end
| FStar_Absyn_Syntax.Const_string (bytes, _53_626) -> begin
(let _119_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _119_568))
end
| c -> begin
(let _119_570 = (let _119_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _119_569))
in (FStar_All.failwith _119_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_637) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_53_640) -> begin
(let _119_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _119_579))
end
| _53_643 -> begin
if norm then begin
(let _119_580 = (whnf env t)
in (aux false _119_580))
end else begin
(let _119_583 = (let _119_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _119_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _119_582 _119_581)))
in (FStar_All.failwith _119_583))
end
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _119_620 = (FStar_Absyn_Util.compress_kind k)
in _119_620.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_648, k0) -> begin
(let _53_652 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _119_622 = (FStar_Absyn_Print.kind_to_string k)
in (let _119_621 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _119_622 _119_621)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _53_656) -> begin
(let _119_624 = (let _119_623 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _119_623))
in (_119_624, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _119_625 = (varops.fresh "t")
in (_119_625, FStar_ToSMT_Term.Type_sort))
in (let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (let _53_671 = (encode_binders None bs env)
in (match (_53_671) with
| (vars, guards, env', decls, _53_670) -> begin
(let app = (mk_ApplyT t vars)
in (let _53_675 = (encode_knd kbody env' app)
in (match (_53_675) with
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
| _53_694 -> begin
(let _119_634 = (let _119_633 = (let _119_632 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _119_632))
in (_119_633, body))
in (FStar_ToSMT_Term.mkAnd _119_634))
end)
in (let _119_636 = (let _119_635 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _119_635))
in (FStar_ToSMT_Term.mkForall _119_636)))))
end
| _53_697 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _119_638 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _119_638 (FStar_List.filter (fun _53_702 -> (match (_53_702) with
| (x, _53_701) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _53_708) -> begin
(let _119_641 = (let _119_640 = (let _119_639 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _119_639))
in (FStar_ToSMT_Term.mkApp _119_640))
in (_119_641, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _119_642 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_119_642))
end else begin
None
end
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _119_644 = (let _119_643 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _119_643))
in (FStar_ToSMT_Term.mkApp _119_644))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _119_653 = (let _119_652 = (let _119_651 = (let _119_650 = (let _119_649 = (let _119_648 = (let _119_647 = (let _119_646 = (let _119_645 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _119_645))
in (_119_646, k_interp))
in (FStar_ToSMT_Term.mkAnd _119_647))
in (t_has_k, _119_648))
in (FStar_ToSMT_Term.mkIff _119_649))
in (((t_has_k)::[])::[], (tsym)::cvars, _119_650))
in (FStar_ToSMT_Term.mkForall _119_651))
in (_119_652, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_119_653))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _53_720 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _53_723 -> begin
(let _119_655 = (let _119_654 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _119_654))
in (FStar_All.failwith _119_655))
end))
and encode_knd = (fun k env t -> (let _53_729 = (encode_knd_term k env)
in (match (_53_729) with
| (k, decls) -> begin
(let _119_659 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_119_659, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _53_733 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _119_663 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.fprint1 "Encoding binders %s\n" _119_663))
end else begin
()
end
in (let _53_783 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_740 b -> (match (_53_740) with
| (vars, guards, env, decls, names) -> begin
(let _53_777 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_743}) -> begin
(let a = (unmangle a)
in (let _53_752 = (gen_typ_var env a)
in (match (_53_752) with
| (aasym, aa, env') -> begin
(let _53_753 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _119_667 = (FStar_Absyn_Print.strBvd a)
in (let _119_666 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _119_667 aasym _119_666)))
end else begin
()
end
in (let _53_757 = (encode_knd k env aa)
in (match (_53_757) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_759}) -> begin
(let x = (unmangle x)
in (let _53_768 = (gen_term_var env x)
in (match (_53_768) with
| (xxsym, xx, env') -> begin
(let _53_771 = (let _119_668 = (norm_t env t)
in (encode_typ_pred fuel_opt _119_668 env xx))
in (match (_53_771) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_53_777) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_53_783) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_791 = (encode_typ_term t env)
in (match (_53_791) with
| (t, decls) -> begin
(let _119_673 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_119_673, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_799 = (encode_typ_term t env)
in (match (_53_799) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _119_678 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_119_678, decls))
end
| Some (f) -> begin
(let _119_679 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_119_679, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _119_682 = (lookup_typ_var env a)
in (_119_682, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _119_683 = (lookup_free_tvar env fv)
in (_119_683, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(let _53_820 = (encode_binders None binders env)
in (match (_53_820) with
| (vars, guards, env', decls, _53_819) -> begin
(let fsym = (let _119_684 = (varops.fresh "f")
in (_119_684, FStar_ToSMT_Term.Term_sort))
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _53_826 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_53_826) with
| (pre_opt, res_t) -> begin
(let _53_829 = (encode_typ_pred None res_t env' app)
in (match (_53_829) with
| (res_pred, decls') -> begin
(let _53_838 = (match (pre_opt) with
| None -> begin
(let _119_685 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_685, decls))
end
| Some (pre) -> begin
(let _53_835 = (encode_formula pre env')
in (match (_53_835) with
| (guard, decls0) -> begin
(let _119_686 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_119_686, (FStar_List.append decls decls0)))
end))
end)
in (match (_53_838) with
| (guards, guard_decls) -> begin
(let t_interp = (let _119_688 = (let _119_687 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _119_687))
in (FStar_ToSMT_Term.mkForall _119_688))
in (let cvars = (let _119_690 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _119_690 (FStar_List.filter (fun _53_843 -> (match (_53_843) with
| (x, _53_842) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _53_849) -> begin
(let _119_693 = (let _119_692 = (let _119_691 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _119_691))
in (FStar_ToSMT_Term.mkApp _119_692))
in (_119_693, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _119_694 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_119_694))
end else begin
None
end
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _119_696 = (let _119_695 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _119_695))
in (FStar_ToSMT_Term.mkApp _119_696))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _119_698 = (let _119_697 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_119_697, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_119_698))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _119_705 = (let _119_704 = (let _119_703 = (let _119_702 = (let _119_701 = (let _119_700 = (let _119_699 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _119_699))
in (f_has_t, _119_700))
in (FStar_ToSMT_Term.mkImp _119_701))
in (((f_has_t)::[])::[], (fsym)::cvars, _119_702))
in (mkForall_fuel _119_703))
in (_119_704, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_119_705))
in (let t_interp = (let _119_709 = (let _119_708 = (let _119_707 = (let _119_706 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _119_706))
in (FStar_ToSMT_Term.mkForall _119_707))
in (_119_708, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_119_709))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _53_865 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let t_kinding = (let _119_711 = (let _119_710 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_119_710, None))
in FStar_ToSMT_Term.Assume (_119_711))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _119_718 = (let _119_717 = (let _119_716 = (let _119_715 = (let _119_714 = (let _119_713 = (let _119_712 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _119_712))
in (f_has_t, _119_713))
in (FStar_ToSMT_Term.mkImp _119_714))
in (((f_has_t)::[])::[], (fsym)::[], _119_715))
in (mkForall_fuel _119_716))
in (_119_717, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_119_718))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_53_876) -> begin
(let _53_895 = (match ((FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _53_885; FStar_Absyn_Syntax.pos = _53_883; FStar_Absyn_Syntax.fvs = _53_881; FStar_Absyn_Syntax.uvs = _53_879} -> begin
(x, f)
end
| _53_892 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_895) with
| (x, f) -> begin
(let _53_898 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_53_898) with
| (base_t, decls) -> begin
(let _53_902 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_902) with
| (x, xtm, env') -> begin
(let _53_905 = (encode_formula f env')
in (match (_53_905) with
| (refinement, decls') -> begin
(let _53_908 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_908) with
| (fsym, fterm) -> begin
(let encoding = (let _119_720 = (let _119_719 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_119_719, refinement))
in (FStar_ToSMT_Term.mkAnd _119_720))
in (let cvars = (let _119_722 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _119_722 (FStar_List.filter (fun _53_913 -> (match (_53_913) with
| (y, _53_912) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_920, _53_922) -> begin
(let _119_725 = (let _119_724 = (let _119_723 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _119_723))
in (FStar_ToSMT_Term.mkApp _119_724))
in (_119_725, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _119_727 = (let _119_726 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _119_726))
in (FStar_ToSMT_Term.mkApp _119_727))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (let assumption = (let _119_729 = (let _119_728 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _119_728))
in (FStar_ToSMT_Term.mkForall _119_729))
in (let t_decls = (let _119_736 = (let _119_735 = (let _119_734 = (let _119_733 = (let _119_732 = (let _119_731 = (let _119_730 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_119_730))
in (assumption, _119_731))
in FStar_ToSMT_Term.Assume (_119_732))
in (_119_733)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_119_734)
in (tdecl)::_119_735)
in (FStar_List.append (FStar_List.append decls decls') _119_736))
in (let _53_935 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _119_737 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _119_737))
in (let _53_944 = (encode_knd k env ttm)
in (match (_53_944) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let is_full_app = (fun _53_951 -> (match (()) with
| () -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind head)
in (let _53_956 = (FStar_Absyn_Util.kind_formals kk)
in (match (_53_956) with
| (formals, _53_955) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _53_963 = (encode_args args env)
in (match (_53_963) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _53_969 = (encode_args args env)
in (match (_53_969) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _119_742 = (let _119_741 = (FStar_List.map (fun _53_10 -> (match (_53_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _119_741))
in (FStar_ToSMT_Term.mkApp _119_742))
in (t, decls)))
end else begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _119_743 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _119_743))
in (let _53_985 = (encode_knd k env ttm)
in (match (_53_985) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _53_988 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(let _53_1000 = (encode_binders None bs env)
in (match (_53_1000) with
| (vars, guards, env, decls, _53_999) -> begin
(let _53_1003 = (encode_typ_term body env)
in (match (_53_1003) with
| (body, decls') -> begin
(let key_body = (let _119_747 = (let _119_746 = (let _119_745 = (let _119_744 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_744, body))
in (FStar_ToSMT_Term.mkImp _119_745))
in ([], vars, _119_746))
in (FStar_ToSMT_Term.mkForall _119_747))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1009, _53_1011) -> begin
(let _119_750 = (let _119_749 = (let _119_748 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _119_748))
in (FStar_ToSMT_Term.mkApp _119_749))
in (_119_750, []))
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
in (let t = (let _119_752 = (let _119_751 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _119_751))
in (FStar_ToSMT_Term.mkApp _119_752))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _119_759 = (let _119_758 = (let _119_757 = (let _119_756 = (let _119_755 = (let _119_754 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_753 = (FStar_ToSMT_Term.mkEq (app, body))
in (_119_754, _119_753)))
in (FStar_ToSMT_Term.mkImp _119_755))
in (((app)::[])::[], (FStar_List.append vars cvars), _119_756))
in (FStar_ToSMT_Term.mkForall _119_757))
in (_119_758, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_119_759))
in (let kinding = (let _53_1026 = (let _119_760 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _119_760 env t))
in (match (_53_1026) with
| (ktm, decls'') -> begin
(let _119_764 = (let _119_763 = (let _119_762 = (let _119_761 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_119_761, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_119_762))
in (_119_763)::[])
in (FStar_List.append decls'' _119_764))
end))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _53_1029 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _53_1033) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_53_1037) -> begin
(let _119_765 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _119_765 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _119_770 = (let _119_769 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _119_768 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _119_767 = (FStar_Absyn_Print.typ_to_string t0)
in (let _119_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _119_769 _119_768 _119_767 _119_766)))))
in (FStar_All.failwith _119_770))
end)))
and encode_exp = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1048) -> begin
(let _119_773 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _119_773 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1055) -> begin
(let _119_774 = (lookup_free_var env v)
in (_119_774, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _119_775 = (encode_const c)
in (_119_775, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_1063) -> begin
(let _53_1066 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_1070)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _53_1076) -> begin
(let e = (let _119_776 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _119_776))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _53_1085 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _119_779 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_119_779, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _53_1089 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _119_780 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _119_780)) then begin
(fallback ())
end else begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(let _53_1101 = (FStar_Util.first_N nformals bs)
in (match (_53_1101) with
| (bs0, rest) -> begin
(let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _53_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (let e = (let _119_782 = (let _119_781 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _119_781))
in (FStar_Absyn_Syntax.mk_Exp_abs _119_782 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(let _53_1114 = (encode_binders None bs env)
in (match (_53_1114) with
| (vars, guards, envbody, decls, _53_1113) -> begin
(let _53_1117 = (encode_exp body envbody)
in (match (_53_1117) with
| (body, decls') -> begin
(let key_body = (let _119_786 = (let _119_785 = (let _119_784 = (let _119_783 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_783, body))
in (FStar_ToSMT_Term.mkImp _119_784))
in ([], vars, _119_785))
in (FStar_ToSMT_Term.mkForall _119_786))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1123, _53_1125) -> begin
(let _119_789 = (let _119_788 = (let _119_787 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _119_787))
in (FStar_ToSMT_Term.mkApp _119_788))
in (_119_789, []))
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
in (let f = (let _119_791 = (let _119_790 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _119_790))
in (FStar_ToSMT_Term.mkApp _119_791))
in (let app = (mk_ApplyE f vars)
in (let _53_1139 = (encode_typ_pred None tfun env f)
in (match (_53_1139) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _119_793 = (let _119_792 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_119_792, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_119_793))
in (let interp_f = (let _119_800 = (let _119_799 = (let _119_798 = (let _119_797 = (let _119_796 = (let _119_795 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _119_794 = (FStar_ToSMT_Term.mkEq (app, body))
in (_119_795, _119_794)))
in (FStar_ToSMT_Term.mkImp _119_796))
in (((app)::[])::[], (FStar_List.append vars cvars), _119_797))
in (FStar_ToSMT_Term.mkForall _119_798))
in (_119_799, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_119_800))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _53_1143 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _53_1146 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _53_1157); FStar_Absyn_Syntax.tk = _53_1154; FStar_Absyn_Syntax.pos = _53_1152; FStar_Absyn_Syntax.fvs = _53_1150; FStar_Absyn_Syntax.uvs = _53_1148}, (FStar_Util.Inl (_53_1172), _53_1175)::(FStar_Util.Inr (v1), _53_1169)::(FStar_Util.Inr (v2), _53_1164)::[]) when (FStar_Absyn_Syntax.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(let _53_1182 = (encode_exp v1 env)
in (match (_53_1182) with
| (v1, decls1) -> begin
(let _53_1185 = (encode_exp v2 env)
in (match (_53_1185) with
| (v2, decls2) -> begin
(let _119_801 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_119_801, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_53_1195); FStar_Absyn_Syntax.tk = _53_1193; FStar_Absyn_Syntax.pos = _53_1191; FStar_Absyn_Syntax.fvs = _53_1189; FStar_Absyn_Syntax.uvs = _53_1187}, _53_1199) -> begin
(let _119_802 = (whnf_e env e)
in (encode_exp _119_802 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(let _53_1208 = (encode_args args_e env)
in (match (_53_1208) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _53_1213 = (encode_exp head env)
in (match (_53_1213) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _53_1222 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_53_1222) with
| (formals, rest) -> begin
(let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _119_805 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _119_805 (FStar_Absyn_Util.subst_typ subst)))
in (let _53_1227 = (encode_typ_pred None ty env app_tm)
in (match (_53_1227) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _119_807 = (let _119_806 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_119_806, None))
in FStar_ToSMT_Term.Assume (_119_807))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _53_1234 = (lookup_free_var_sym env fv)
in (match (_53_1234) with
| (fname, fuel_args) -> begin
(let tm = (let _119_813 = (let _119_812 = (let _119_811 = (FStar_List.map (fun _53_11 -> (match (_53_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _119_811))
in (fname, _119_812))
in (FStar_ToSMT_Term.mkApp' _119_813))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _53_1241 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _119_815 = (FStar_Absyn_Print.exp_to_string head)
in (let _119_814 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _119_815 _119_814)))
end else begin
()
end
in (let head_type = (let _119_818 = (let _119_817 = (let _119_816 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _119_816))
in (whnf env _119_817))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _119_818))
in (let _53_1244 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _119_821 = (FStar_Absyn_Print.exp_to_string head)
in (let _119_820 = (FStar_Absyn_Print.tag_of_exp head)
in (let _119_819 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _119_821 _119_820 _119_819))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _119_825 = (let _119_824 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _119_823 = (FStar_Absyn_Print.exp_to_string e0)
in (let _119_822 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _119_824 _119_823 _119_822))))
in (FStar_All.failwith _119_825))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1253) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _53_1257 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_53_1266); FStar_Absyn_Syntax.lbtyp = _53_1264; FStar_Absyn_Syntax.lbeff = _53_1262; FStar_Absyn_Syntax.lbdef = _53_1260}::[]), _53_1272) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _53_1278; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _53_1290 = (encode_exp e1 env)
in (match (_53_1290) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _53_1294 = (encode_exp e2 env')
in (match (_53_1294) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_53_1296) -> begin
(let _53_1298 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _119_826 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_119_826, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _53_1308 = (encode_exp e env)
in (match (_53_1308) with
| (scr, decls) -> begin
(let _53_1348 = (FStar_List.fold_right (fun _53_1312 _53_1315 -> (match ((_53_1312, _53_1315)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _53_1319 _53_1322 -> (match ((_53_1319, _53_1322)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _53_1328 -> (match (_53_1328) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _53_1342 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _53_1339 = (encode_exp w env)
in (match (_53_1339) with
| (w, decls2) -> begin
(let _119_837 = (let _119_836 = (let _119_835 = (let _119_834 = (let _119_833 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _119_833))
in (FStar_ToSMT_Term.mkEq _119_834))
in (guard, _119_835))
in (FStar_ToSMT_Term.mkAnd _119_836))
in (_119_837, decls2))
end))
end)
in (match (_53_1342) with
| (guard, decls2) -> begin
(let _53_1345 = (encode_exp br env)
in (match (_53_1345) with
| (br, decls3) -> begin
(let _119_838 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_119_838, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_53_1348) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_53_1350) -> begin
(let _119_841 = (let _119_840 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _119_839 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _119_840 _119_839)))
in (FStar_All.failwith _119_841))
end))))
and encode_pat = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _53_1357 -> begin
(let _119_844 = (encode_one_pat env pat)
in (_119_844)::[])
end))
and encode_one_pat = (fun env pat -> (let _53_1360 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _119_847 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.fprint1 "Encoding pattern %s\n" _119_847))
end else begin
()
end
in (let _53_1364 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_53_1364) with
| (vars, pat_exp_or_typ) -> begin
(let _53_1385 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _53_1367 v -> (match (_53_1367) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(let _53_1375 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_53_1375) with
| (aa, _53_1373, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(let _53_1382 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_1382) with
| (xx, _53_1380, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_53_1385) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1390) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _119_855 = (let _119_854 = (encode_const c)
in (scrutinee, _119_854))
in (FStar_ToSMT_Term.mkEq _119_855))
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1414, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1423 -> (match (_53_1423) with
| (arg, _53_1422) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _119_858 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _119_858)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1430) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_53_1447) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1451, args) -> begin
(let _119_866 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1459 -> (match (_53_1459) with
| (arg, _53_1458) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _119_865 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _119_865)))
end))))
in (FStar_All.pipe_right _119_866 FStar_List.flatten))
end))
in (let pat_term = (fun _53_1462 -> (match (()) with
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
and encode_args = (fun l env -> (let _53_1492 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _53_1472 x -> (match (_53_1472) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _53_1477) -> begin
(let _53_1481 = (encode_typ_term t env)
in (match (_53_1481) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _53_1485) -> begin
(let _53_1489 = (encode_exp e env)
in (match (_53_1489) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_53_1492) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _53_1498 = (encode_formula_with_labels phi env)
in (match (_53_1498) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _53_1501 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun induction_on new_pats t env -> (let rec list_elements = (fun e -> (match ((let _119_881 = (FStar_Absyn_Util.unmeta_exp e)
in _119_881.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1518); FStar_Absyn_Syntax.tk = _53_1515; FStar_Absyn_Syntax.pos = _53_1513; FStar_Absyn_Syntax.fvs = _53_1511; FStar_Absyn_Syntax.uvs = _53_1509}, _53_1523) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1536); FStar_Absyn_Syntax.tk = _53_1533; FStar_Absyn_Syntax.pos = _53_1531; FStar_Absyn_Syntax.fvs = _53_1529; FStar_Absyn_Syntax.uvs = _53_1527}, _53_1551::(FStar_Util.Inr (hd), _53_1548)::(FStar_Util.Inr (tl), _53_1543)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _119_882 = (list_elements tl)
in (hd)::_119_882)
end
| _53_1556 -> begin
(let _53_1557 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (let v_or_t_pat = (fun p -> (match ((let _119_885 = (FStar_Absyn_Util.unmeta_exp p)
in _119_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1571); FStar_Absyn_Syntax.tk = _53_1568; FStar_Absyn_Syntax.pos = _53_1566; FStar_Absyn_Syntax.fvs = _53_1564; FStar_Absyn_Syntax.uvs = _53_1562}, (FStar_Util.Inl (_53_1581), _53_1584)::(FStar_Util.Inr (e), _53_1578)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1599); FStar_Absyn_Syntax.tk = _53_1596; FStar_Absyn_Syntax.pos = _53_1594; FStar_Absyn_Syntax.fvs = _53_1592; FStar_Absyn_Syntax.uvs = _53_1590}, (FStar_Util.Inl (t), _53_1606)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _53_1612 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let lemma_pats = (fun p -> (let elts = (list_elements p)
in (match (elts) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1634); FStar_Absyn_Syntax.tk = _53_1631; FStar_Absyn_Syntax.pos = _53_1629; FStar_Absyn_Syntax.fvs = _53_1627; FStar_Absyn_Syntax.uvs = _53_1625}, (FStar_Util.Inr (e), _53_1641)::[]); FStar_Absyn_Syntax.tk = _53_1623; FStar_Absyn_Syntax.pos = _53_1621; FStar_Absyn_Syntax.fvs = _53_1619; FStar_Absyn_Syntax.uvs = _53_1617}::[] when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _119_890 = (list_elements e)
in (FStar_All.pipe_right _119_890 (FStar_List.map (fun branch -> (let _119_889 = (list_elements branch)
in (FStar_All.pipe_right _119_889 (FStar_List.map v_or_t_pat)))))))
end
| _53_1650 -> begin
(let _119_891 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_119_891)::[])
end)))
in (let _53_1693 = (match ((let _119_892 = (FStar_Absyn_Util.compress_typ t)
in _119_892.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _53_1659; FStar_Absyn_Syntax.pos = _53_1657; FStar_Absyn_Syntax.fvs = _53_1655; FStar_Absyn_Syntax.uvs = _53_1653}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _53_1678)::(FStar_Util.Inl (post), _53_1673)::(FStar_Util.Inr (pats), _53_1668)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _119_893 = (lemma_pats pats')
in (binders, pre, post, _119_893)))
end
| _53_1686 -> begin
(FStar_All.failwith "impos")
end)
end
| _53_1688 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_53_1693) with
| (binders, pre, post, patterns) -> begin
(let _53_1700 = (encode_binders None binders env)
in (match (_53_1700) with
| (vars, guards, env, decls, _53_1699) -> begin
(let _53_1720 = (let _119_897 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (let _53_1717 = (let _119_896 = (FStar_All.pipe_right branch (FStar_List.map (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (t), _53_1706) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _53_1711) -> begin
(encode_exp e (let _53_1713 = env
in {bindings = _53_1713.bindings; depth = _53_1713.depth; tcenv = _53_1713.tcenv; warn = _53_1713.warn; cache = _53_1713.cache; nolabels = _53_1713.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1713.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _119_896 FStar_List.unzip))
in (match (_53_1717) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _119_897 FStar_List.unzip))
in (match (_53_1720) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _119_900 = (let _119_899 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _119_899 e))
in (_119_900)::p))))
end
| _53_1730 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _119_906 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_119_906)::p))))
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _119_908 = (let _119_907 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _119_907 tl))
in (aux _119_908 vars))
end
| _53_1742 -> begin
pats
end))
in (let _119_909 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _119_909 vars)))
end)
end)
in (let env = (let _53_1744 = env
in {bindings = _53_1744.bindings; depth = _53_1744.depth; tcenv = _53_1744.tcenv; warn = _53_1744.warn; cache = _53_1744.cache; nolabels = true; use_zfuel_name = _53_1744.use_zfuel_name; encode_non_total_function_typ = _53_1744.encode_non_total_function_typ})
in (let _53_1749 = (let _119_910 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _119_910 env))
in (match (_53_1749) with
| (pre, decls'') -> begin
(let _53_1752 = (let _119_911 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _119_911 env))
in (match (_53_1752) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _119_916 = (let _119_915 = (let _119_914 = (let _119_913 = (let _119_912 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_119_912, post))
in (FStar_ToSMT_Term.mkImp _119_913))
in (pats, vars, _119_914))
in (FStar_ToSMT_Term.mkForall _119_915))
in (_119_916, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f l -> (let _53_1773 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(let _53_1765 = (encode_typ_term t env)
in (match (_53_1765) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(let _53_1770 = (encode_exp e env)
in (match (_53_1770) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_53_1773) with
| (decls, args) -> begin
(let _119_934 = (f args)
in (_119_934, [], decls))
end)))
in (let enc_prop_c = (fun f l -> (let _53_1793 = (FStar_List.fold_right (fun t _53_1781 -> (match (_53_1781) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(let _53_1787 = (encode_formula_with_labels t env)
in (match (_53_1787) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _53_1789 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_53_1793) with
| (phis, labs, decls) -> begin
(let _119_950 = (f phis)
in (_119_950, labs, decls))
end)))
in (let const_op = (fun f _53_1796 -> (f, [], []))
in (let un_op = (fun f l -> (let _119_964 = (FStar_List.hd l)
in (FStar_All.pipe_left f _119_964)))
in (let bin_op = (fun f _53_13 -> (match (_53_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _53_1807 -> begin
(FStar_All.failwith "Impossible")
end))
in (let eq_op = (fun _53_14 -> (match (_53_14) with
| _53_1815::_53_1813::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _53_15 -> (match (_53_15) with
| (FStar_Util.Inl (lhs), _53_1828)::(FStar_Util.Inl (rhs), _53_1823)::[] -> begin
(let _53_1834 = (encode_formula_with_labels rhs env)
in (match (_53_1834) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_1837) -> begin
(l1, labs1, decls1)
end
| _53_1841 -> begin
(let _53_1845 = (encode_formula_with_labels lhs env)
in (match (_53_1845) with
| (l2, labs2, decls2) -> begin
(let _119_978 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_119_978, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _53_1847 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _53_16 -> (match (_53_16) with
| (FStar_Util.Inl (guard), _53_1863)::(FStar_Util.Inl (_then), _53_1858)::(FStar_Util.Inl (_else), _53_1853)::[] -> begin
(let _53_1869 = (encode_formula_with_labels guard env)
in (match (_53_1869) with
| (g, labs1, decls1) -> begin
(let _53_1873 = (encode_formula_with_labels _then env)
in (match (_53_1873) with
| (t, labs2, decls2) -> begin
(let _53_1877 = (encode_formula_with_labels _else env)
in (match (_53_1877) with
| (e, labs3, decls3) -> begin
(let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _53_1880 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _119_990 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _119_990)))
in (let connectives = (let _119_1051 = (let _119_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _119_999))
in (let _119_1050 = (let _119_1049 = (let _119_1005 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _119_1005))
in (let _119_1048 = (let _119_1047 = (let _119_1046 = (let _119_1014 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _119_1014))
in (let _119_1045 = (let _119_1044 = (let _119_1043 = (let _119_1023 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _119_1023))
in (let _119_1042 = (let _119_1041 = (let _119_1029 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _119_1029))
in (_119_1041)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_119_1043)::_119_1042))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_119_1044)
in (_119_1046)::_119_1045))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_119_1047)
in (_119_1049)::_119_1048))
in (_119_1051)::_119_1050))
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _53_1898 = (encode_formula_with_labels phi' env)
in (match (_53_1898) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(let lvar = (let _119_1054 = (varops.fresh "label")
in (_119_1054, FStar_ToSMT_Term.Bool_sort))
in (let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1909; FStar_Absyn_Syntax.pos = _53_1907; FStar_Absyn_Syntax.fvs = _53_1905; FStar_Absyn_Syntax.uvs = _53_1903}, _53_1924::(FStar_Util.Inr (l), _53_1921)::(FStar_Util.Inl (phi), _53_1916)::[]) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let _53_1930 = (encode_exp l env)
in (match (_53_1930) with
| (e, decls) -> begin
(let _53_1933 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_53_1933) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1941; FStar_Absyn_Syntax.pos = _53_1939; FStar_Absyn_Syntax.fvs = _53_1937; FStar_Absyn_Syntax.uvs = _53_1935}, _53_1953::(FStar_Util.Inl (phi), _53_1949)::tl) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _53_1961)::[] -> begin
Some (pat)
end)
in (let _53_1967 = (encode_function_type_as_formula None pat phi env)
in (match (_53_1967) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _53_1969 -> begin
(let _53_1972 = (encode_typ_term phi env)
in (match (_53_1972) with
| (tt, decls) -> begin
(let _119_1055 = (FStar_ToSMT_Term.mk_Valid tt)
in (_119_1055, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _53_1984 = (encode_binders None bs env)
in (match (_53_1984) with
| (vars, guards, env, decls, _53_1983) -> begin
(let _53_2004 = (let _119_1067 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (let _53_2001 = (let _119_1066 = (FStar_All.pipe_right p (FStar_List.map (fun _53_17 -> (match (_53_17) with
| (FStar_Util.Inl (t), _53_1990) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _53_1995) -> begin
(encode_exp e (let _53_1997 = env
in {bindings = _53_1997.bindings; depth = _53_1997.depth; tcenv = _53_1997.tcenv; warn = _53_1997.warn; cache = _53_1997.cache; nolabels = _53_1997.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1997.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _119_1066 FStar_List.unzip))
in (match (_53_2001) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _119_1067 FStar_List.unzip))
in (match (_53_2004) with
| (pats, decls') -> begin
(let _53_2008 = (encode_formula_with_labels body env)
in (match (_53_2008) with
| (body, labs, decls'') -> begin
(let _119_1068 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _119_1068, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _53_2009 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _119_1069 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.fprint1 ">>>> Destructing as formula ... %s\n" _119_1069))
end else begin
()
end
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _53_2021 -> (match (_53_2021) with
| (l, _53_2020) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_53_2024, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _53_2034 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _119_1086 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.fprint1 ">>>> Got QALL [%s]\n" _119_1086))
end else begin
()
end
in (let _53_2042 = (encode_q_body env vars pats body)
in (match (_53_2042) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _119_1089 = (let _119_1088 = (let _119_1087 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _119_1087))
in (FStar_ToSMT_Term.mkForall _119_1088))
in (_119_1089, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _53_2055 = (encode_q_body env vars pats body)
in (match (_53_2055) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _119_1092 = (let _119_1091 = (let _119_1090 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _119_1090))
in (FStar_ToSMT_Term.mkExists _119_1091))
in (_119_1092, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Absyn_Syntax.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Absyn_Syntax.lident  ->  Prims.bool}

let is_Mkprims_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t")))

let prims = (let _53_2061 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_53_2061) with
| (asym, a) -> begin
(let _53_2064 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2064) with
| (xsym, x) -> begin
(let _53_2067 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_53_2067) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_ToSMT_Term.DefineFun ((x, vars, FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (let _119_1135 = (let _119_1134 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _119_1134))
in (FStar_ToSMT_Term.mkApp _119_1135))
in (let vname_decl = (let _119_1137 = (let _119_1136 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _119_1136, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_1137))
in (let _119_1143 = (let _119_1142 = (let _119_1141 = (let _119_1140 = (let _119_1139 = (let _119_1138 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _119_1138))
in (FStar_ToSMT_Term.mkForall _119_1139))
in (_119_1140, None))
in FStar_ToSMT_Term.Assume (_119_1141))
in (_119_1142)::[])
in (vname_decl)::_119_1143))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _119_1303 = (let _119_1152 = (let _119_1151 = (let _119_1150 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1150))
in (quant axy _119_1151))
in (FStar_Absyn_Const.op_Eq, _119_1152))
in (let _119_1302 = (let _119_1301 = (let _119_1159 = (let _119_1158 = (let _119_1157 = (let _119_1156 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _119_1156))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1157))
in (quant axy _119_1158))
in (FStar_Absyn_Const.op_notEq, _119_1159))
in (let _119_1300 = (let _119_1299 = (let _119_1168 = (let _119_1167 = (let _119_1166 = (let _119_1165 = (let _119_1164 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1163 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1164, _119_1163)))
in (FStar_ToSMT_Term.mkLT _119_1165))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1166))
in (quant xy _119_1167))
in (FStar_Absyn_Const.op_LT, _119_1168))
in (let _119_1298 = (let _119_1297 = (let _119_1177 = (let _119_1176 = (let _119_1175 = (let _119_1174 = (let _119_1173 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1172 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1173, _119_1172)))
in (FStar_ToSMT_Term.mkLTE _119_1174))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1175))
in (quant xy _119_1176))
in (FStar_Absyn_Const.op_LTE, _119_1177))
in (let _119_1296 = (let _119_1295 = (let _119_1186 = (let _119_1185 = (let _119_1184 = (let _119_1183 = (let _119_1182 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1181 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1182, _119_1181)))
in (FStar_ToSMT_Term.mkGT _119_1183))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1184))
in (quant xy _119_1185))
in (FStar_Absyn_Const.op_GT, _119_1186))
in (let _119_1294 = (let _119_1293 = (let _119_1195 = (let _119_1194 = (let _119_1193 = (let _119_1192 = (let _119_1191 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1190 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1191, _119_1190)))
in (FStar_ToSMT_Term.mkGTE _119_1192))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1193))
in (quant xy _119_1194))
in (FStar_Absyn_Const.op_GTE, _119_1195))
in (let _119_1292 = (let _119_1291 = (let _119_1204 = (let _119_1203 = (let _119_1202 = (let _119_1201 = (let _119_1200 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1199 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1200, _119_1199)))
in (FStar_ToSMT_Term.mkSub _119_1201))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1202))
in (quant xy _119_1203))
in (FStar_Absyn_Const.op_Subtraction, _119_1204))
in (let _119_1290 = (let _119_1289 = (let _119_1211 = (let _119_1210 = (let _119_1209 = (let _119_1208 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _119_1208))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1209))
in (quant qx _119_1210))
in (FStar_Absyn_Const.op_Minus, _119_1211))
in (let _119_1288 = (let _119_1287 = (let _119_1220 = (let _119_1219 = (let _119_1218 = (let _119_1217 = (let _119_1216 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1215 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1216, _119_1215)))
in (FStar_ToSMT_Term.mkAdd _119_1217))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1218))
in (quant xy _119_1219))
in (FStar_Absyn_Const.op_Addition, _119_1220))
in (let _119_1286 = (let _119_1285 = (let _119_1229 = (let _119_1228 = (let _119_1227 = (let _119_1226 = (let _119_1225 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1224 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1225, _119_1224)))
in (FStar_ToSMT_Term.mkMul _119_1226))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1227))
in (quant xy _119_1228))
in (FStar_Absyn_Const.op_Multiply, _119_1229))
in (let _119_1284 = (let _119_1283 = (let _119_1238 = (let _119_1237 = (let _119_1236 = (let _119_1235 = (let _119_1234 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1233 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1234, _119_1233)))
in (FStar_ToSMT_Term.mkDiv _119_1235))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1236))
in (quant xy _119_1237))
in (FStar_Absyn_Const.op_Division, _119_1238))
in (let _119_1282 = (let _119_1281 = (let _119_1247 = (let _119_1246 = (let _119_1245 = (let _119_1244 = (let _119_1243 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1242 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1243, _119_1242)))
in (FStar_ToSMT_Term.mkMod _119_1244))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1245))
in (quant xy _119_1246))
in (FStar_Absyn_Const.op_Modulus, _119_1247))
in (let _119_1280 = (let _119_1279 = (let _119_1256 = (let _119_1255 = (let _119_1254 = (let _119_1253 = (let _119_1252 = (FStar_ToSMT_Term.unboxBool x)
in (let _119_1251 = (FStar_ToSMT_Term.unboxBool y)
in (_119_1252, _119_1251)))
in (FStar_ToSMT_Term.mkAnd _119_1253))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1254))
in (quant xy _119_1255))
in (FStar_Absyn_Const.op_And, _119_1256))
in (let _119_1278 = (let _119_1277 = (let _119_1265 = (let _119_1264 = (let _119_1263 = (let _119_1262 = (let _119_1261 = (FStar_ToSMT_Term.unboxBool x)
in (let _119_1260 = (FStar_ToSMT_Term.unboxBool y)
in (_119_1261, _119_1260)))
in (FStar_ToSMT_Term.mkOr _119_1262))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1263))
in (quant xy _119_1264))
in (FStar_Absyn_Const.op_Or, _119_1265))
in (let _119_1276 = (let _119_1275 = (let _119_1272 = (let _119_1271 = (let _119_1270 = (let _119_1269 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _119_1269))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1270))
in (quant qx _119_1271))
in (FStar_Absyn_Const.op_Negation, _119_1272))
in (_119_1275)::[])
in (_119_1277)::_119_1276))
in (_119_1279)::_119_1278))
in (_119_1281)::_119_1280))
in (_119_1283)::_119_1282))
in (_119_1285)::_119_1284))
in (_119_1287)::_119_1286))
in (_119_1289)::_119_1288))
in (_119_1291)::_119_1290))
in (_119_1293)::_119_1292))
in (_119_1295)::_119_1294))
in (_119_1297)::_119_1296))
in (_119_1299)::_119_1298))
in (_119_1301)::_119_1300))
in (_119_1303)::_119_1302))
in (let mk = (fun l v -> (let _119_1335 = (FStar_All.pipe_right prims (FStar_List.filter (fun _53_2087 -> (match (_53_2087) with
| (l', _53_2086) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end))))
in (FStar_All.pipe_right _119_1335 (FStar_List.collect (fun _53_2091 -> (match (_53_2091) with
| (_53_2089, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _53_2097 -> (match (_53_2097) with
| (l', _53_2096) -> begin
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
in (let mk_unit = (fun _53_2103 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _119_1367 = (let _119_1358 = (let _119_1357 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_119_1357, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_119_1358))
in (let _119_1366 = (let _119_1365 = (let _119_1364 = (let _119_1363 = (let _119_1362 = (let _119_1361 = (let _119_1360 = (let _119_1359 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _119_1359))
in (FStar_ToSMT_Term.mkImp _119_1360))
in (((typing_pred)::[])::[], (xx)::[], _119_1361))
in (mkForall_fuel _119_1362))
in (_119_1363, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_119_1364))
in (_119_1365)::[])
in (_119_1367)::_119_1366))))
in (let mk_bool = (fun _53_2108 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _119_1388 = (let _119_1377 = (let _119_1376 = (let _119_1375 = (let _119_1374 = (let _119_1373 = (let _119_1372 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _119_1372))
in (FStar_ToSMT_Term.mkImp _119_1373))
in (((typing_pred)::[])::[], (xx)::[], _119_1374))
in (mkForall_fuel _119_1375))
in (_119_1376, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_119_1377))
in (let _119_1387 = (let _119_1386 = (let _119_1385 = (let _119_1384 = (let _119_1383 = (let _119_1382 = (let _119_1379 = (let _119_1378 = (FStar_ToSMT_Term.boxBool b)
in (_119_1378)::[])
in (_119_1379)::[])
in (let _119_1381 = (let _119_1380 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _119_1380 tt))
in (_119_1382, (bb)::[], _119_1381)))
in (FStar_ToSMT_Term.mkForall _119_1383))
in (_119_1384, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_119_1385))
in (_119_1386)::[])
in (_119_1388)::_119_1387))))))
in (let mk_int = (fun _53_2115 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _119_1400 = (let _119_1399 = (let _119_1398 = (let _119_1397 = (let _119_1396 = (let _119_1395 = (FStar_ToSMT_Term.boxInt a)
in (let _119_1394 = (let _119_1393 = (FStar_ToSMT_Term.boxInt b)
in (_119_1393)::[])
in (_119_1395)::_119_1394))
in (tt)::_119_1396)
in (tt)::_119_1397)
in ("Prims.Precedes", _119_1398))
in (FStar_ToSMT_Term.mkApp _119_1399))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _119_1400))
in (let precedes_y_x = (let _119_1401 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _119_1401))
in (let _119_1443 = (let _119_1407 = (let _119_1406 = (let _119_1405 = (let _119_1404 = (let _119_1403 = (let _119_1402 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _119_1402))
in (FStar_ToSMT_Term.mkImp _119_1403))
in (((typing_pred)::[])::[], (xx)::[], _119_1404))
in (mkForall_fuel _119_1405))
in (_119_1406, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_119_1407))
in (let _119_1442 = (let _119_1441 = (let _119_1415 = (let _119_1414 = (let _119_1413 = (let _119_1412 = (let _119_1409 = (let _119_1408 = (FStar_ToSMT_Term.boxInt b)
in (_119_1408)::[])
in (_119_1409)::[])
in (let _119_1411 = (let _119_1410 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _119_1410 tt))
in (_119_1412, (bb)::[], _119_1411)))
in (FStar_ToSMT_Term.mkForall _119_1413))
in (_119_1414, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_119_1415))
in (let _119_1440 = (let _119_1439 = (let _119_1438 = (let _119_1437 = (let _119_1436 = (let _119_1435 = (let _119_1434 = (let _119_1433 = (let _119_1432 = (let _119_1431 = (let _119_1430 = (let _119_1429 = (let _119_1418 = (let _119_1417 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1416 = (FStar_ToSMT_Term.mkInteger' 0)
in (_119_1417, _119_1416)))
in (FStar_ToSMT_Term.mkGT _119_1418))
in (let _119_1428 = (let _119_1427 = (let _119_1421 = (let _119_1420 = (FStar_ToSMT_Term.unboxInt y)
in (let _119_1419 = (FStar_ToSMT_Term.mkInteger' 0)
in (_119_1420, _119_1419)))
in (FStar_ToSMT_Term.mkGTE _119_1421))
in (let _119_1426 = (let _119_1425 = (let _119_1424 = (let _119_1423 = (FStar_ToSMT_Term.unboxInt y)
in (let _119_1422 = (FStar_ToSMT_Term.unboxInt x)
in (_119_1423, _119_1422)))
in (FStar_ToSMT_Term.mkLT _119_1424))
in (_119_1425)::[])
in (_119_1427)::_119_1426))
in (_119_1429)::_119_1428))
in (typing_pred_y)::_119_1430)
in (typing_pred)::_119_1431)
in (FStar_ToSMT_Term.mk_and_l _119_1432))
in (_119_1433, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _119_1434))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _119_1435))
in (mkForall_fuel _119_1436))
in (_119_1437, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_119_1438))
in (_119_1439)::[])
in (_119_1441)::_119_1440))
in (_119_1443)::_119_1442)))))))))))
in (let mk_int_alias = (fun _53_2127 tt -> (let _119_1452 = (let _119_1451 = (let _119_1450 = (let _119_1449 = (let _119_1448 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Absyn_Syntax.str, []))
in (tt, _119_1448))
in (FStar_ToSMT_Term.mkEq _119_1449))
in (_119_1450, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_119_1451))
in (_119_1452)::[]))
in (let mk_str = (fun _53_2131 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _119_1473 = (let _119_1462 = (let _119_1461 = (let _119_1460 = (let _119_1459 = (let _119_1458 = (let _119_1457 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _119_1457))
in (FStar_ToSMT_Term.mkImp _119_1458))
in (((typing_pred)::[])::[], (xx)::[], _119_1459))
in (mkForall_fuel _119_1460))
in (_119_1461, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_119_1462))
in (let _119_1472 = (let _119_1471 = (let _119_1470 = (let _119_1469 = (let _119_1468 = (let _119_1467 = (let _119_1464 = (let _119_1463 = (FStar_ToSMT_Term.boxString b)
in (_119_1463)::[])
in (_119_1464)::[])
in (let _119_1466 = (let _119_1465 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _119_1465 tt))
in (_119_1467, (bb)::[], _119_1466)))
in (FStar_ToSMT_Term.mkForall _119_1468))
in (_119_1469, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_119_1470))
in (_119_1471)::[])
in (_119_1473)::_119_1472))))))
in (let mk_ref = (fun reft_name _53_2139 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _119_1480 = (let _119_1479 = (let _119_1478 = (FStar_ToSMT_Term.mkFreeV aa)
in (_119_1478)::[])
in (reft_name, _119_1479))
in (FStar_ToSMT_Term.mkApp _119_1480))
in (let refb = (let _119_1483 = (let _119_1482 = (let _119_1481 = (FStar_ToSMT_Term.mkFreeV bb)
in (_119_1481)::[])
in (reft_name, _119_1482))
in (FStar_ToSMT_Term.mkApp _119_1483))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _119_1502 = (let _119_1489 = (let _119_1488 = (let _119_1487 = (let _119_1486 = (let _119_1485 = (let _119_1484 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _119_1484))
in (FStar_ToSMT_Term.mkImp _119_1485))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _119_1486))
in (mkForall_fuel _119_1487))
in (_119_1488, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_119_1489))
in (let _119_1501 = (let _119_1500 = (let _119_1499 = (let _119_1498 = (let _119_1497 = (let _119_1496 = (let _119_1495 = (let _119_1494 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _119_1493 = (let _119_1492 = (let _119_1491 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _119_1490 = (FStar_ToSMT_Term.mkFreeV bb)
in (_119_1491, _119_1490)))
in (FStar_ToSMT_Term.mkEq _119_1492))
in (_119_1494, _119_1493)))
in (FStar_ToSMT_Term.mkImp _119_1495))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _119_1496))
in (mkForall_fuel' 2 _119_1497))
in (_119_1498, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_119_1499))
in (_119_1500)::[])
in (_119_1502)::_119_1501))))))))))
in (let mk_false_interp = (fun _53_2149 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _119_1509 = (let _119_1508 = (let _119_1507 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_119_1507, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_119_1508))
in (_119_1509)::[])))
in (let mk_and_interp = (fun conj _53_2155 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1516 = (let _119_1515 = (let _119_1514 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_119_1514)::[])
in ("Valid", _119_1515))
in (FStar_ToSMT_Term.mkApp _119_1516))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1523 = (let _119_1522 = (let _119_1521 = (let _119_1520 = (let _119_1519 = (let _119_1518 = (let _119_1517 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_119_1517, valid))
in (FStar_ToSMT_Term.mkIff _119_1518))
in (((valid)::[])::[], (aa)::(bb)::[], _119_1519))
in (FStar_ToSMT_Term.mkForall _119_1520))
in (_119_1521, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_119_1522))
in (_119_1523)::[])))))))))
in (let mk_or_interp = (fun disj _53_2166 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1530 = (let _119_1529 = (let _119_1528 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_119_1528)::[])
in ("Valid", _119_1529))
in (FStar_ToSMT_Term.mkApp _119_1530))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1537 = (let _119_1536 = (let _119_1535 = (let _119_1534 = (let _119_1533 = (let _119_1532 = (let _119_1531 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_119_1531, valid))
in (FStar_ToSMT_Term.mkIff _119_1532))
in (((valid)::[])::[], (aa)::(bb)::[], _119_1533))
in (FStar_ToSMT_Term.mkForall _119_1534))
in (_119_1535, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_119_1536))
in (_119_1537)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _119_1544 = (let _119_1543 = (let _119_1542 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_119_1542)::[])
in ("Valid", _119_1543))
in (FStar_ToSMT_Term.mkApp _119_1544))
in (let _119_1551 = (let _119_1550 = (let _119_1549 = (let _119_1548 = (let _119_1547 = (let _119_1546 = (let _119_1545 = (FStar_ToSMT_Term.mkEq (x, y))
in (_119_1545, valid))
in (FStar_ToSMT_Term.mkIff _119_1546))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _119_1547))
in (FStar_ToSMT_Term.mkForall _119_1548))
in (_119_1549, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_119_1550))
in (_119_1551)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1558 = (let _119_1557 = (let _119_1556 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_119_1556)::[])
in ("Valid", _119_1557))
in (FStar_ToSMT_Term.mkApp _119_1558))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1565 = (let _119_1564 = (let _119_1563 = (let _119_1562 = (let _119_1561 = (let _119_1560 = (let _119_1559 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_119_1559, valid))
in (FStar_ToSMT_Term.mkIff _119_1560))
in (((valid)::[])::[], (aa)::(bb)::[], _119_1561))
in (FStar_ToSMT_Term.mkForall _119_1562))
in (_119_1563, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_119_1564))
in (_119_1565)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1572 = (let _119_1571 = (let _119_1570 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_119_1570)::[])
in ("Valid", _119_1571))
in (FStar_ToSMT_Term.mkApp _119_1572))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1579 = (let _119_1578 = (let _119_1577 = (let _119_1576 = (let _119_1575 = (let _119_1574 = (let _119_1573 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_119_1573, valid))
in (FStar_ToSMT_Term.mkIff _119_1574))
in (((valid)::[])::[], (aa)::(bb)::[], _119_1575))
in (FStar_ToSMT_Term.mkForall _119_1576))
in (_119_1577, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_119_1578))
in (_119_1579)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _119_1586 = (let _119_1585 = (let _119_1584 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_119_1584)::[])
in ("Valid", _119_1585))
in (FStar_ToSMT_Term.mkApp _119_1586))
in (let valid_b_x = (let _119_1589 = (let _119_1588 = (let _119_1587 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_119_1587)::[])
in ("Valid", _119_1588))
in (FStar_ToSMT_Term.mkApp _119_1589))
in (let _119_1603 = (let _119_1602 = (let _119_1601 = (let _119_1600 = (let _119_1599 = (let _119_1598 = (let _119_1597 = (let _119_1596 = (let _119_1595 = (let _119_1591 = (let _119_1590 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1590)::[])
in (_119_1591)::[])
in (let _119_1594 = (let _119_1593 = (let _119_1592 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1592, valid_b_x))
in (FStar_ToSMT_Term.mkImp _119_1593))
in (_119_1595, (xx)::[], _119_1594)))
in (FStar_ToSMT_Term.mkForall _119_1596))
in (_119_1597, valid))
in (FStar_ToSMT_Term.mkIff _119_1598))
in (((valid)::[])::[], (aa)::(bb)::[], _119_1599))
in (FStar_ToSMT_Term.mkForall _119_1600))
in (_119_1601, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_119_1602))
in (_119_1603)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _119_1610 = (let _119_1609 = (let _119_1608 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_119_1608)::[])
in ("Valid", _119_1609))
in (FStar_ToSMT_Term.mkApp _119_1610))
in (let valid_b_x = (let _119_1613 = (let _119_1612 = (let _119_1611 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_119_1611)::[])
in ("Valid", _119_1612))
in (FStar_ToSMT_Term.mkApp _119_1613))
in (let _119_1627 = (let _119_1626 = (let _119_1625 = (let _119_1624 = (let _119_1623 = (let _119_1622 = (let _119_1621 = (let _119_1620 = (let _119_1619 = (let _119_1615 = (let _119_1614 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1614)::[])
in (_119_1615)::[])
in (let _119_1618 = (let _119_1617 = (let _119_1616 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1616, valid_b_x))
in (FStar_ToSMT_Term.mkImp _119_1617))
in (_119_1619, (xx)::[], _119_1618)))
in (FStar_ToSMT_Term.mkExists _119_1620))
in (_119_1621, valid))
in (FStar_ToSMT_Term.mkIff _119_1622))
in (((valid)::[])::[], (aa)::(bb)::[], _119_1623))
in (FStar_ToSMT_Term.mkForall _119_1624))
in (_119_1625, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_119_1626))
in (_119_1627)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1634 = (let _119_1633 = (let _119_1632 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_119_1632)::[])
in ("Valid", _119_1633))
in (FStar_ToSMT_Term.mkApp _119_1634))
in (let valid_a_b = (let _119_1637 = (let _119_1636 = (let _119_1635 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_119_1635)::[])
in ("Valid", _119_1636))
in (FStar_ToSMT_Term.mkApp _119_1637))
in (let _119_1651 = (let _119_1650 = (let _119_1649 = (let _119_1648 = (let _119_1647 = (let _119_1646 = (let _119_1645 = (let _119_1644 = (let _119_1643 = (let _119_1639 = (let _119_1638 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1638)::[])
in (_119_1639)::[])
in (let _119_1642 = (let _119_1641 = (let _119_1640 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1640, valid_a_b))
in (FStar_ToSMT_Term.mkImp _119_1641))
in (_119_1643, (bb)::[], _119_1642)))
in (FStar_ToSMT_Term.mkForall _119_1644))
in (_119_1645, valid))
in (FStar_ToSMT_Term.mkIff _119_1646))
in (((valid)::[])::[], (kk)::(aa)::[], _119_1647))
in (FStar_ToSMT_Term.mkForall _119_1648))
in (_119_1649, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_119_1650))
in (_119_1651)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1658 = (let _119_1657 = (let _119_1656 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_119_1656)::[])
in ("Valid", _119_1657))
in (FStar_ToSMT_Term.mkApp _119_1658))
in (let valid_a_b = (let _119_1661 = (let _119_1660 = (let _119_1659 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_119_1659)::[])
in ("Valid", _119_1660))
in (FStar_ToSMT_Term.mkApp _119_1661))
in (let _119_1675 = (let _119_1674 = (let _119_1673 = (let _119_1672 = (let _119_1671 = (let _119_1670 = (let _119_1669 = (let _119_1668 = (let _119_1667 = (let _119_1663 = (let _119_1662 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1662)::[])
in (_119_1663)::[])
in (let _119_1666 = (let _119_1665 = (let _119_1664 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1664, valid_a_b))
in (FStar_ToSMT_Term.mkImp _119_1665))
in (_119_1667, (bb)::[], _119_1666)))
in (FStar_ToSMT_Term.mkExists _119_1668))
in (_119_1669, valid))
in (FStar_ToSMT_Term.mkIff _119_1670))
in (((valid)::[])::[], (kk)::(aa)::[], _119_1671))
in (FStar_ToSMT_Term.mkForall _119_1672))
in (_119_1673, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_119_1674))
in (_119_1675)::[]))))))))))
in (let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _53_2259 -> (match (_53_2259) with
| (l, _53_2258) -> begin
(FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_53_2262, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun env se -> (let _53_2268 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _119_1818 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.fprint1 ">>>>Encoding [%s]\n") _119_1818))
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
in (let _53_2276 = (encode_sigelt' env se)
in (match (_53_2276) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _119_1821 = (let _119_1820 = (let _119_1819 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_119_1819))
in (_119_1820)::[])
in (_119_1821, e))
end
| _53_2279 -> begin
(let _119_1828 = (let _119_1827 = (let _119_1823 = (let _119_1822 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_119_1822))
in (_119_1823)::g)
in (let _119_1826 = (let _119_1825 = (let _119_1824 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_119_1824))
in (_119_1825)::[])
in (FStar_List.append _119_1827 _119_1826)))
in (_119_1828, e))
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.all_")))
in (let encode_top_level_val = (fun env lid t quals -> (let tt = (whnf env t)
in (let _53_2292 = (encode_free_var env lid t tt quals)
in (match (_53_2292) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _119_1842 = (let _119_1841 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _119_1841))
in (_119_1842, env))
end else begin
(decls, env)
end
end))))
in (let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2299 lb -> (match (_53_2299) with
| (decls, env) -> begin
(let _53_2303 = (let _119_1851 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _119_1851 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_53_2303) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_53_2305, _53_2307, _53_2309, _53_2311, FStar_Absyn_Syntax.Effect::[], _53_2315) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2320, _53_2322, _53_2324, _53_2326, _53_2328) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2333, _53_2335, _53_2337, _53_2339, _53_2341) when (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(let _53_2347 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2347) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _119_1854 = (let _119_1853 = (let _119_1852 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_119_1852)::[])
in ("Valid", _119_1853))
in (FStar_ToSMT_Term.mkApp _119_1854))
in (let decls = (let _119_1862 = (let _119_1861 = (let _119_1860 = (let _119_1859 = (let _119_1858 = (let _119_1857 = (let _119_1856 = (let _119_1855 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _119_1855))
in (FStar_ToSMT_Term.mkEq _119_1856))
in (((valid_b2t_x)::[])::[], (xx)::[], _119_1857))
in (FStar_ToSMT_Term.mkForall _119_1858))
in (_119_1859, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_119_1860))
in (_119_1861)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_119_1862)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _53_2355, t, tags, _53_2359) -> begin
(let _53_2365 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2365) with
| (tname, ttok, env) -> begin
(let _53_2374 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _53_2371 -> begin
(tps, t)
end)
in (match (_53_2374) with
| (tps, t) -> begin
(let _53_2381 = (encode_binders None tps env)
in (match (_53_2381) with
| (vars, guards, env', binder_decls, _53_2380) -> begin
(let tok_app = (let _119_1863 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _119_1863 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _119_1865 = (let _119_1864 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _119_1864))
in (FStar_ToSMT_Term.mkApp _119_1865))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _53_2387 -> begin
(let _119_1867 = (let _119_1866 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _119_1866))
in (_119_1867)::[])
end)
in (let decls = (let _119_1878 = (let _119_1871 = (let _119_1870 = (let _119_1869 = (let _119_1868 = (FStar_List.map Prims.snd vars)
in (tname, _119_1868, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_1869))
in (_119_1870)::(tok_decl)::[])
in (FStar_List.append _119_1871 fresh_tok))
in (let _119_1877 = (let _119_1876 = (let _119_1875 = (let _119_1874 = (let _119_1873 = (let _119_1872 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _119_1872))
in (FStar_ToSMT_Term.mkForall _119_1873))
in (_119_1874, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_119_1875))
in (_119_1876)::[])
in (FStar_List.append _119_1878 _119_1877)))
in (let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (let _53_2399 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _53_18 -> (match (_53_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2394 -> begin
false
end)))) then begin
(let _119_1881 = (FStar_ToSMT_Term.mk_Valid app)
in (let _119_1880 = (encode_formula t env')
in (_119_1881, _119_1880)))
end else begin
(let _119_1882 = (encode_typ_term t env')
in (app, _119_1882))
end
in (match (_53_2399) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _119_1889 = (let _119_1888 = (let _119_1887 = (let _119_1886 = (let _119_1885 = (let _119_1884 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_1883 = (FStar_ToSMT_Term.mkEq (def, body))
in (_119_1884, _119_1883)))
in (FStar_ToSMT_Term.mkImp _119_1885))
in (((def)::[])::[], vars, _119_1886))
in (FStar_ToSMT_Term.mkForall _119_1887))
in (_119_1888, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_119_1889))
in (let kindingAx = (let _53_2403 = (let _119_1890 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _119_1890 env' app))
in (match (_53_2403) with
| (k, decls) -> begin
(let _119_1898 = (let _119_1897 = (let _119_1896 = (let _119_1895 = (let _119_1894 = (let _119_1893 = (let _119_1892 = (let _119_1891 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_1891, k))
in (FStar_ToSMT_Term.mkImp _119_1892))
in (((app)::[])::[], vars, _119_1893))
in (FStar_ToSMT_Term.mkForall _119_1894))
in (_119_1895, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_119_1896))
in (_119_1897)::[])
in (FStar_List.append decls _119_1898))
end))
in (let g = (let _119_1899 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _119_1899))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _53_2410) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _53_2416, _53_2418) -> begin
(let _53_2423 = (encode_formula f env)
in (match (_53_2423) with
| (f, decls) -> begin
(let g = (let _119_1904 = (let _119_1903 = (let _119_1902 = (let _119_1901 = (let _119_1900 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _119_1900))
in Some (_119_1901))
in (f, _119_1902))
in FStar_ToSMT_Term.Assume (_119_1903))
in (_119_1904)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2429, datas, quals, _53_2433) when (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(let _53_2439 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2439) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _53_2442, _53_2444, _53_2446, _53_2448, _53_2450, _53_2452) when ((FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.FStar_Absyn_Syntax.str
in (let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _119_1906 = (let _119_1905 = (primitive_type_axioms t tname tsym)
in (decl)::_119_1905)
in (_119_1906, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2462, datas, quals, _53_2466) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_19 -> (match (_53_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _53_2473 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _53_2483 = c
in (match (_53_2483) with
| (name, args, _53_2480, _53_2482) -> begin
(let _119_1912 = (let _119_1911 = (let _119_1910 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _119_1910, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_1911))
in (_119_1912)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _119_1918 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _119_1918 FStar_Option.isNone)))))) then begin
[]
end else begin
(let _53_2490 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2490) with
| (xxsym, xx) -> begin
(let _53_2533 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _53_2493 l -> (match (_53_2493) with
| (out, decls) -> begin
(let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _53_2503 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_53_2503) with
| (args, res) -> begin
(let indices = (match ((let _119_1921 = (FStar_Absyn_Util.compress_typ res)
in _119_1921.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_53_2505, indices) -> begin
indices
end
| _53_2510 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _119_1926 = (let _119_1925 = (let _119_1924 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_119_1924, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _119_1925))
in (push_typ_var env a.FStar_Absyn_Syntax.v _119_1926))
end
| FStar_Util.Inr (x) -> begin
(let _119_1929 = (let _119_1928 = (let _119_1927 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_119_1927, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _119_1928))
in (push_term_var env x.FStar_Absyn_Syntax.v _119_1929))
end)) env))
in (let _53_2521 = (encode_args indices env)
in (match (_53_2521) with
| (indices, decls') -> begin
(let _53_2522 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (let eqs = (let _119_1936 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _119_1933 = (let _119_1932 = (FStar_ToSMT_Term.mkFreeV v)
in (_119_1932, a))
in (FStar_ToSMT_Term.mkEq _119_1933))
end
| FStar_Util.Inr (a) -> begin
(let _119_1935 = (let _119_1934 = (FStar_ToSMT_Term.mkFreeV v)
in (_119_1934, a))
in (FStar_ToSMT_Term.mkEq _119_1935))
end)) vars indices)
in (FStar_All.pipe_right _119_1936 FStar_ToSMT_Term.mk_and_l))
in (let _119_1941 = (let _119_1940 = (let _119_1939 = (let _119_1938 = (let _119_1937 = (mk_data_tester env l xx)
in (_119_1937, eqs))
in (FStar_ToSMT_Term.mkAnd _119_1938))
in (out, _119_1939))
in (FStar_ToSMT_Term.mkOr _119_1940))
in (_119_1941, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_53_2533) with
| (data_ax, decls) -> begin
(let _53_2536 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2536) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _119_1942 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _119_1942 xx tapp))
in (let _119_1949 = (let _119_1948 = (let _119_1947 = (let _119_1946 = (let _119_1945 = (let _119_1944 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _119_1943 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _119_1944, _119_1943)))
in (FStar_ToSMT_Term.mkForall _119_1945))
in (_119_1946, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_119_1947))
in (_119_1948)::[])
in (FStar_List.append decls _119_1949)))
end))
end))
end))
end)
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _53_2548 = (match ((let _119_1950 = (FStar_Absyn_Util.compress_kind k)
in _119_1950.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _53_2544 -> begin
(false, [], k)
end)
in (match (_53_2548) with
| (is_kind_arrow, formals, res) -> begin
(let _53_2555 = (encode_binders None formals env)
in (match (_53_2555) with
| (vars, guards, env', binder_decls, _53_2554) -> begin
(let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _53_20 -> (match (_53_20) with
| FStar_Absyn_Syntax.Projector (_53_2561) -> begin
true
end
| _53_2564 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _53_21 -> (match (_53_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_53_2579) -> begin
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
in (let _53_2594 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_53_2585, xx::suffix) -> begin
(xx, suffix)
end
| _53_2591 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_2594) with
| (xx, suffix) -> begin
(let dproj_app = (let _119_1964 = (let _119_1963 = (let _119_1962 = (mk_typ_projector_name d a)
in (let _119_1961 = (let _119_1960 = (FStar_ToSMT_Term.mkFreeV xx)
in (_119_1960)::[])
in (_119_1962, _119_1961)))
in (FStar_ToSMT_Term.mkApp _119_1963))
in (mk_ApplyT _119_1964 suffix))
in (let _119_1969 = (let _119_1968 = (let _119_1967 = (let _119_1966 = (let _119_1965 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _119_1965))
in (FStar_ToSMT_Term.mkForall _119_1966))
in (_119_1967, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_119_1968))
in (_119_1969)::[]))
end))))
end
| _53_2597 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _53_2603 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2603) with
| (xxsym, xx) -> begin
(let _53_2606 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2606) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _119_1982 = (let _119_1981 = (let _119_1980 = (let _119_1979 = (let _119_1978 = (let _119_1977 = (let _119_1976 = (let _119_1975 = (let _119_1974 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _119_1974))
in (FStar_ToSMT_Term.mkEq _119_1975))
in (xx_has_type, _119_1976))
in (FStar_ToSMT_Term.mkImp _119_1977))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _119_1978))
in (FStar_ToSMT_Term.mkForall _119_1979))
in (_119_1980, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_119_1981))
in (_119_1982)::[]))
end))
end)))
in (let _53_2611 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2611) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _119_1984 = (let _119_1983 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _119_1983))
in (FStar_ToSMT_Term.mkApp _119_1984))
in (let _53_2632 = (let tname_decl = (let _119_1988 = (let _119_1987 = (FStar_All.pipe_right vars (FStar_List.map (fun _53_2617 -> (match (_53_2617) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _119_1986 = (varops.next_id ())
in (tname, _119_1987, FStar_ToSMT_Term.Type_sort, _119_1986)))
in (constructor_or_logic_type_decl _119_1988))
in (let _53_2629 = (match (vars) with
| [] -> begin
(let _119_1992 = (let _119_1991 = (let _119_1990 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _119_1989 -> Some (_119_1989)) _119_1990))
in (push_free_tvar env t tname _119_1991))
in ([], _119_1992))
end
| _53_2621 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _119_1993 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _119_1993))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (let name_tok_corr = (let _119_1997 = (let _119_1996 = (let _119_1995 = (let _119_1994 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _119_1994))
in (FStar_ToSMT_Term.mkForall' _119_1995))
in (_119_1996, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_119_1997))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_53_2629) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_53_2632) with
| (decls, env) -> begin
(let kindingAx = (let _53_2635 = (encode_knd res env' tapp)
in (match (_53_2635) with
| (k, decls) -> begin
(let karr = if is_kind_arrow then begin
(let _119_2001 = (let _119_2000 = (let _119_1999 = (let _119_1998 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _119_1998))
in (_119_1999, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_119_2000))
in (_119_2001)::[])
end else begin
[]
end
in (let _119_2007 = (let _119_2006 = (let _119_2005 = (let _119_2004 = (let _119_2003 = (let _119_2002 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _119_2002))
in (FStar_ToSMT_Term.mkForall _119_2003))
in (_119_2004, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_119_2005))
in (_119_2006)::[])
in (FStar_List.append (FStar_List.append decls karr) _119_2007)))
end))
in (let aux = if is_logical then begin
(let _119_2008 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _119_2008))
end else begin
(let _119_2015 = (let _119_2013 = (let _119_2011 = (let _119_2009 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _119_2009))
in (let _119_2010 = (inversion_axioms tapp vars)
in (FStar_List.append _119_2011 _119_2010)))
in (let _119_2012 = (projection_axioms tapp vars)
in (FStar_List.append _119_2013 _119_2012)))
in (let _119_2014 = (pretype_axioms tapp vars)
in (FStar_List.append _119_2015 _119_2014)))
end
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _53_2642, _53_2644, _53_2646, _53_2648, _53_2650) when (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_53_2656, tps, _53_2659), quals, _53_2663, drange) -> begin
(let t = (let _119_2017 = (FStar_List.map (fun _53_2670 -> (match (_53_2670) with
| (x, _53_2669) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _119_2017 t))
in (let _53_2675 = (new_term_constant_and_tok_from_lid env d)
in (match (_53_2675) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _53_2684 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_53_2684) with
| (formals, t_res) -> begin
(let _53_2687 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2687) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _53_2694 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2694) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _53_22 -> (match (_53_22) with
| FStar_Util.Inl (a) -> begin
(let _119_2019 = (mk_typ_projector_name d a)
in (_119_2019, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _119_2020 = (mk_term_projector_name d x)
in (_119_2020, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _119_2022 = (let _119_2021 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _119_2021))
in (FStar_All.pipe_right _119_2022 FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _53_2708 = (encode_typ_pred None t env ddtok_tm)
in (match (_53_2708) with
| (tok_typing, decls3) -> begin
(let _53_2715 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2715) with
| (vars', guards', env'', decls_formals, _53_2714) -> begin
(let _53_2720 = (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_53_2720) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _53_2724 -> begin
(let _119_2024 = (let _119_2023 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _119_2023))
in (_119_2024)::[])
end)
in (let encode_elim = (fun _53_2727 -> (match (()) with
| () -> begin
(let _53_2730 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_53_2730) with
| (head, args) -> begin
(match ((let _119_2027 = (FStar_Absyn_Util.compress_typ head)
in _119_2027.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _53_2736 = (encode_args args env')
in (match (_53_2736) with
| (encoded_args, arg_decls) -> begin
(let _53_2760 = (FStar_List.fold_left (fun _53_2740 arg -> (match (_53_2740) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _53_2748 = (let _119_2030 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _119_2030))
in (match (_53_2748) with
| (_53_2745, tv, env) -> begin
(let _119_2032 = (let _119_2031 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_119_2031)::eqns)
in (env, (tv)::arg_vars, _119_2032))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _53_2755 = (let _119_2033 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _119_2033))
in (match (_53_2755) with
| (_53_2752, xv, env) -> begin
(let _119_2035 = (let _119_2034 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_119_2034)::eqns)
in (env, (xv)::arg_vars, _119_2035))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_53_2760) with
| (_53_2757, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _119_2042 = (let _119_2041 = (let _119_2040 = (let _119_2039 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _119_2038 = (let _119_2037 = (let _119_2036 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _119_2036))
in (FStar_ToSMT_Term.mkImp _119_2037))
in (((ty_pred)::[])::[], _119_2039, _119_2038)))
in (FStar_ToSMT_Term.mkForall _119_2040))
in (_119_2041, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_119_2042))
in (let subterm_ordering = if (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(let x = (let _119_2043 = (varops.fresh "x")
in (_119_2043, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _119_2053 = (let _119_2052 = (let _119_2051 = (let _119_2050 = (let _119_2045 = (let _119_2044 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_119_2044)::[])
in (_119_2045)::[])
in (let _119_2049 = (let _119_2048 = (let _119_2047 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _119_2046 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_119_2047, _119_2046)))
in (FStar_ToSMT_Term.mkImp _119_2048))
in (_119_2050, (x)::[], _119_2049)))
in (FStar_ToSMT_Term.mkForall _119_2051))
in (_119_2052, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_119_2053))))
end else begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _119_2056 = (let _119_2055 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _119_2055 dapp))
in (_119_2056)::[])
end
| _53_2775 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _119_2063 = (let _119_2062 = (let _119_2061 = (let _119_2060 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _119_2059 = (let _119_2058 = (let _119_2057 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _119_2057))
in (FStar_ToSMT_Term.mkImp _119_2058))
in (((ty_pred)::[])::[], _119_2060, _119_2059)))
in (FStar_ToSMT_Term.mkForall _119_2061))
in (_119_2062, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_119_2063)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _53_2779 -> begin
(let _53_2780 = (let _119_2066 = (let _119_2065 = (FStar_Absyn_Print.sli d)
in (let _119_2064 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _119_2065 _119_2064)))
in (FStar_Tc_Errors.warn drange _119_2066))
in ([], []))
end)
end))
end))
in (let _53_2784 = (encode_elim ())
in (match (_53_2784) with
| (decls2, elim) -> begin
(let g = (let _119_2091 = (let _119_2090 = (let _119_2075 = (let _119_2074 = (let _119_2073 = (let _119_2072 = (let _119_2071 = (let _119_2070 = (let _119_2069 = (let _119_2068 = (let _119_2067 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _119_2067))
in Some (_119_2068))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _119_2069))
in FStar_ToSMT_Term.DeclFun (_119_2070))
in (_119_2071)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _119_2072))
in (FStar_List.append _119_2073 proxy_fresh))
in (FStar_List.append _119_2074 decls_formals))
in (FStar_List.append _119_2075 decls_pred))
in (let _119_2089 = (let _119_2088 = (let _119_2087 = (let _119_2079 = (let _119_2078 = (let _119_2077 = (let _119_2076 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _119_2076))
in (FStar_ToSMT_Term.mkForall _119_2077))
in (_119_2078, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_119_2079))
in (let _119_2086 = (let _119_2085 = (let _119_2084 = (let _119_2083 = (let _119_2082 = (let _119_2081 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _119_2080 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _119_2081, _119_2080)))
in (FStar_ToSMT_Term.mkForall _119_2082))
in (_119_2083, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_119_2084))
in (_119_2085)::[])
in (_119_2087)::_119_2086))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_119_2088)
in (FStar_List.append _119_2090 _119_2089)))
in (FStar_List.append _119_2091 elim))
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
| FStar_Absyn_Syntax.Sig_bundle (ses, _53_2788, _53_2790, _53_2792) -> begin
(let _53_2797 = (encode_signature env ses)
in (match (_53_2797) with
| (g, env) -> begin
(let _53_2809 = (FStar_All.pipe_right g (FStar_List.partition (fun _53_23 -> (match (_53_23) with
| FStar_ToSMT_Term.Assume (_53_2800, Some ("inversion axiom")) -> begin
false
end
| _53_2806 -> begin
true
end))))
in (match (_53_2809) with
| (g', inversions) -> begin
(let _53_2818 = (FStar_All.pipe_right g' (FStar_List.partition (fun _53_24 -> (match (_53_24) with
| FStar_ToSMT_Term.DeclFun (_53_2812) -> begin
true
end
| _53_2815 -> begin
false
end))))
in (match (_53_2818) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_53_2820, _53_2822, _53_2824, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_25 -> (match (_53_25) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _53_2836 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _53_2841, _53_2843, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _53_2855 = (FStar_Util.first_N nbinders formals)
in (match (_53_2855) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _119_2106 = (let _119_2105 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _119_2105))
in FStar_Util.Inl (_119_2106))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _119_2108 = (let _119_2107 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _119_2107))
in FStar_Util.Inr (_119_2108))
end
| _53_2869 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _119_2109 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _119_2109 FStar_Absyn_Util.name_binders))
in (let body = (let _119_2115 = (let _119_2111 = (let _119_2110 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _119_2110))
in (body, _119_2111))
in (let _119_2114 = (let _119_2113 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _119_2112 -> Some (_119_2112)) _119_2113))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _119_2115 _119_2114 body.FStar_Absyn_Syntax.pos)))
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
(let _53_2907 = (FStar_Util.first_N nformals binders)
in (match (_53_2907) with
| (bs0, rest) -> begin
(let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _53_2911 -> begin
(FStar_All.failwith "impossible")
end)
in (let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(let _53_2916 = (eta_expand binders formals body tres)
in (match (_53_2916) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _53_2918 -> begin
(let _119_2124 = (let _119_2123 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_2122 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Absyn_Syntax.str _119_2123 _119_2122)))
in (FStar_All.failwith _119_2124))
end)
end
| _53_2920 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (FStar_Absyn_Util.comp_result c)
in (let _53_2928 = (eta_expand [] formals e tres)
in (match (_53_2928) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _53_2930 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _53_2932 -> (match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_26 -> (match (_53_26) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2943 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(let _53_2962 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2949 lb -> (match (_53_2949) with
| (toks, typs, decls, env) -> begin
(let _53_2951 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (let t_norm = (let _119_2130 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _119_2130 FStar_Absyn_Util.compress_typ))
in (let _53_2957 = (let _119_2131 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _119_2131 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_53_2957) with
| (tok, decl, env) -> begin
(let _119_2134 = (let _119_2133 = (let _119_2132 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_119_2132, tok))
in (_119_2133)::toks)
in (_119_2134, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_53_2962) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_27 -> (match (_53_27) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _53_2969 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _119_2137 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _119_2137))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _53_2977; FStar_Absyn_Syntax.lbtyp = _53_2975; FStar_Absyn_Syntax.lbeff = _53_2973; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _53_2993 = (destruct_bound_function flid t_norm e)
in (match (_53_2993) with
| (binders, body, formals, tres) -> begin
(let _53_3000 = (encode_binders None binders env)
in (match (_53_3000) with
| (vars, guards, env', binder_decls, _53_2999) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _53_3003 -> begin
(let _119_2139 = (let _119_2138 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _119_2138))
in (FStar_ToSMT_Term.mkApp _119_2139))
end)
in (let _53_3007 = (encode_exp body env')
in (match (_53_3007) with
| (body, decls2) -> begin
(let eqn = (let _119_2148 = (let _119_2147 = (let _119_2144 = (let _119_2143 = (let _119_2142 = (let _119_2141 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_2140 = (FStar_ToSMT_Term.mkEq (app, body))
in (_119_2141, _119_2140)))
in (FStar_ToSMT_Term.mkImp _119_2142))
in (((app)::[])::[], vars, _119_2143))
in (FStar_ToSMT_Term.mkForall _119_2144))
in (let _119_2146 = (let _119_2145 = (FStar_Util.format1 "Equation for %s" flid.FStar_Absyn_Syntax.str)
in Some (_119_2145))
in (_119_2147, _119_2146)))
in FStar_ToSMT_Term.Assume (_119_2148))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _53_3010 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let fuel = (let _119_2149 = (varops.fresh "fuel")
in (_119_2149, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _53_3027 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _53_3016 _53_3021 -> (match ((_53_3016, _53_3021)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _119_2154 = (let _119_2153 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _119_2152 -> Some (_119_2152)) _119_2153))
in (push_free_var env flid gtok _119_2154))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_53_3027) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _53_3036 t_norm _53_3045 -> (match ((_53_3036, _53_3045)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _53_3044; FStar_Absyn_Syntax.lbtyp = _53_3042; FStar_Absyn_Syntax.lbeff = _53_3040; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _53_3050 = (destruct_bound_function flid t_norm e)
in (match (_53_3050) with
| (binders, body, formals, tres) -> begin
(let _53_3057 = (encode_binders None binders env)
in (match (_53_3057) with
| (vars, guards, env', binder_decls, _53_3056) -> begin
(let decl_g = (let _119_2165 = (let _119_2164 = (let _119_2163 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_119_2163)
in (g, _119_2164, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_119_2165))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _119_2168 = (let _119_2167 = (let _119_2166 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_119_2166)::vars_tm)
in (g, _119_2167))
in (FStar_ToSMT_Term.mkApp _119_2168))
in (let gmax = (let _119_2171 = (let _119_2170 = (let _119_2169 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_119_2169)::vars_tm)
in (g, _119_2170))
in (FStar_ToSMT_Term.mkApp _119_2171))
in (let _53_3067 = (encode_exp body env')
in (match (_53_3067) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _119_2180 = (let _119_2179 = (let _119_2176 = (let _119_2175 = (let _119_2174 = (let _119_2173 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_2172 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_119_2173, _119_2172)))
in (FStar_ToSMT_Term.mkImp _119_2174))
in (((gsapp)::[])::[], (fuel)::vars, _119_2175))
in (FStar_ToSMT_Term.mkForall _119_2176))
in (let _119_2178 = (let _119_2177 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Absyn_Syntax.str)
in Some (_119_2177))
in (_119_2179, _119_2178)))
in FStar_ToSMT_Term.Assume (_119_2180))
in (let eqn_f = (let _119_2184 = (let _119_2183 = (let _119_2182 = (let _119_2181 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _119_2181))
in (FStar_ToSMT_Term.mkForall _119_2182))
in (_119_2183, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_119_2184))
in (let eqn_g' = (let _119_2193 = (let _119_2192 = (let _119_2191 = (let _119_2190 = (let _119_2189 = (let _119_2188 = (let _119_2187 = (let _119_2186 = (let _119_2185 = (FStar_ToSMT_Term.n_fuel 0)
in (_119_2185)::vars_tm)
in (g, _119_2186))
in (FStar_ToSMT_Term.mkApp _119_2187))
in (gsapp, _119_2188))
in (FStar_ToSMT_Term.mkEq _119_2189))
in (((gsapp)::[])::[], (fuel)::vars, _119_2190))
in (FStar_ToSMT_Term.mkForall _119_2191))
in (_119_2192, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_119_2193))
in (let _53_3090 = (let _53_3077 = (encode_binders None formals env0)
in (match (_53_3077) with
| (vars, v_guards, env, binder_decls, _53_3076) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _119_2194 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _119_2194 ((fuel)::vars)))
in (let _119_2198 = (let _119_2197 = (let _119_2196 = (let _119_2195 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _119_2195))
in (FStar_ToSMT_Term.mkForall _119_2196))
in (_119_2197, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_119_2198)))
in (let _53_3087 = (let _53_3084 = (encode_typ_pred None tres env gapp)
in (match (_53_3084) with
| (g_typing, d3) -> begin
(let _119_2206 = (let _119_2205 = (let _119_2204 = (let _119_2203 = (let _119_2202 = (let _119_2201 = (let _119_2200 = (let _119_2199 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_119_2199, g_typing))
in (FStar_ToSMT_Term.mkImp _119_2200))
in (((gapp)::[])::[], (fuel)::vars, _119_2201))
in (FStar_ToSMT_Term.mkForall _119_2202))
in (_119_2203, None))
in FStar_ToSMT_Term.Assume (_119_2204))
in (_119_2205)::[])
in (d3, _119_2206))
end))
in (match (_53_3087) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_53_3090) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _53_3106 = (let _119_2209 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _53_3094 _53_3098 -> (match ((_53_3094, _53_3098)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _53_3102 = (encode_one_binding env0 gtok ty bs)
in (match (_53_3102) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _119_2209))
in (match (_53_3106) with
| (decls, eqns, env0) -> begin
(let _53_3115 = (let _119_2211 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _119_2211 (FStar_List.partition (fun _53_28 -> (match (_53_28) with
| FStar_ToSMT_Term.DeclFun (_53_3109) -> begin
true
end
| _53_3112 -> begin
false
end)))))
in (match (_53_3115) with
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
end)) (fun _53_2931 -> (match (_53_2931) with
| Let_rec_unencodeable -> begin
(let msg = (let _119_2214 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _119_2214 (FStar_String.concat " and ")))
in (let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _53_3142 = (encode_free_var env x t t_norm [])
in (match (_53_3142) with
| (decls, env) -> begin
(let _53_3147 = (lookup_lid env x)
in (match (_53_3147) with
| (n, x', _53_3146) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _53_3151) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _53_3159 = (encode_function_type_as_formula None None t env)
in (match (_53_3159) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> if ((let _119_2227 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _119_2227)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(let _53_3168 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3168) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_3171) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _53_29 -> (match (_53_29) with
| (FStar_Util.Inl (_53_3176), _53_3179) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3182 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _53_3184 -> begin
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
in (let _53_3201 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _119_2229 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _119_2229))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_53_3201) with
| (formals, (pre_opt, res_t)) -> begin
(let _53_3205 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3205) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _53_3208 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _53_30 -> (match (_53_30) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _53_3224 = (FStar_Util.prefix vars)
in (match (_53_3224) with
| (_53_3219, (xxsym, _53_3222)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _119_2246 = (let _119_2245 = (let _119_2244 = (let _119_2243 = (let _119_2242 = (let _119_2241 = (let _119_2240 = (let _119_2239 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Absyn_Syntax.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_2239))
in (vapp, _119_2240))
in (FStar_ToSMT_Term.mkEq _119_2241))
in (((vapp)::[])::[], vars, _119_2242))
in (FStar_ToSMT_Term.mkForall _119_2243))
in (_119_2244, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_119_2245))
in (_119_2246)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _53_3237 = (FStar_Util.prefix vars)
in (match (_53_3237) with
| (_53_3232, (xxsym, _53_3235)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _119_2248 = (let _119_2247 = (mk_term_projector_name d f)
in (_119_2247, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _119_2248))
in (let _119_2253 = (let _119_2252 = (let _119_2251 = (let _119_2250 = (let _119_2249 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _119_2249))
in (FStar_ToSMT_Term.mkForall _119_2250))
in (_119_2251, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_119_2252))
in (_119_2253)::[])))
end))
end
| _53_3241 -> begin
[]
end)))))
in (let _53_3248 = (encode_binders None formals env)
in (match (_53_3248) with
| (vars, guards, env', decls1, _53_3247) -> begin
(let _53_3257 = (match (pre_opt) with
| None -> begin
(let _119_2254 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_2254, decls1))
end
| Some (p) -> begin
(let _53_3254 = (encode_formula p env')
in (match (_53_3254) with
| (g, ds) -> begin
(let _119_2255 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_119_2255, (FStar_List.append decls1 ds)))
end))
end)
in (match (_53_3257) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _119_2257 = (let _119_2256 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _119_2256))
in (FStar_ToSMT_Term.mkApp _119_2257))
in (let _53_3288 = (let vname_decl = (let _119_2260 = (let _119_2259 = (FStar_All.pipe_right formals (FStar_List.map (fun _53_31 -> (match (_53_31) with
| (FStar_Util.Inl (_53_3262), _53_3265) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3268 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _119_2259, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_2260))
in (let _53_3275 = (let env = (let _53_3270 = env
in {bindings = _53_3270.bindings; depth = _53_3270.depth; tcenv = _53_3270.tcenv; warn = _53_3270.warn; cache = _53_3270.cache; nolabels = _53_3270.nolabels; use_zfuel_name = _53_3270.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_53_3275) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _53_3285 = (match (formals) with
| [] -> begin
(let _119_2264 = (let _119_2263 = (let _119_2262 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _119_2261 -> Some (_119_2261)) _119_2262))
in (push_free_var env lid vname _119_2263))
in ((FStar_List.append decls2 ((tok_typing)::[])), _119_2264))
end
| _53_3279 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _119_2265 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _119_2265))
in (let name_tok_corr = (let _119_2269 = (let _119_2268 = (let _119_2267 = (let _119_2266 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _119_2266))
in (FStar_ToSMT_Term.mkForall _119_2267))
in (_119_2268, None))
in FStar_ToSMT_Term.Assume (_119_2269))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_53_3285) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_53_3288) with
| (decls2, env) -> begin
(let _53_3296 = (let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (let _53_3292 = (encode_typ_term res_t env')
in (match (_53_3292) with
| (encoded_res_t, decls) -> begin
(let _119_2270 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _119_2270, decls))
end)))
in (match (_53_3296) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _119_2274 = (let _119_2273 = (let _119_2272 = (let _119_2271 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _119_2271))
in (FStar_ToSMT_Term.mkForall _119_2272))
in (_119_2273, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_119_2274))
in (let g = (let _119_2276 = (let _119_2275 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_119_2275)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _119_2276))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _53_3303 se -> (match (_53_3303) with
| (g, env) -> begin
(let _53_3307 = (encode_sigelt env se)
in (match (_53_3307) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _53_3314 -> (match (_53_3314) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _53_3322 = (new_term_constant env x)
in (match (_53_3322) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _53_3324 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _119_2291 = (FStar_Absyn_Print.strBvd x)
in (let _119_2290 = (FStar_Absyn_Print.typ_to_string t0)
in (let _119_2289 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.fprint3 "Normalized %s : %s to %s\n" _119_2291 _119_2290 _119_2289))))
end else begin
()
end
in (let _53_3328 = (encode_typ_pred None t1 env xx)
in (match (_53_3328) with
| (t, decls') -> begin
(let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _119_2295 = (let _119_2294 = (FStar_Absyn_Print.strBvd x)
in (let _119_2293 = (FStar_Absyn_Print.typ_to_string t0)
in (let _119_2292 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _119_2294 _119_2293 _119_2292))))
in Some (_119_2295))
end else begin
None
end
in (let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let _53_3338 = (new_typ_constant env a)
in (match (_53_3338) with
| (aasym, aa, env') -> begin
(let _53_3341 = (encode_knd k env aa)
in (match (_53_3341) with
| (k, decls') -> begin
(let g = (let _119_2301 = (let _119_2300 = (let _119_2299 = (let _119_2298 = (let _119_2297 = (let _119_2296 = (FStar_Absyn_Print.strBvd a)
in Some (_119_2296))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _119_2297))
in FStar_ToSMT_Term.DeclFun (_119_2298))
in (_119_2299)::[])
in (FStar_List.append _119_2300 decls'))
in (FStar_List.append _119_2301 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _53_3350 = (encode_free_var env x t t_norm [])
in (match (_53_3350) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(let _53_3355 = (encode_sigelt env se)
in (match (_53_3355) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _53_3362 -> (match (_53_3362) with
| (l, _53_3359, _53_3361) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _53_3369 -> (match (_53_3369) with
| (l, _53_3366, _53_3368) -> begin
(let _119_2309 = (FStar_All.pipe_left (fun _119_2305 -> FStar_ToSMT_Term.Echo (_119_2305)) (Prims.fst l))
in (let _119_2308 = (let _119_2307 = (let _119_2306 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_119_2306))
in (_119_2307)::[])
in (_119_2309)::_119_2308))
end))))
in (prefix, suffix))))

let last_env = (FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _119_2314 = (let _119_2313 = (let _119_2312 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _119_2312; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_119_2313)::[])
in (FStar_ST.op_Colon_Equals last_env _119_2314)))

let get_env = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_53_3375 -> begin
(let _53_3378 = e
in {bindings = _53_3378.bindings; depth = _53_3378.depth; tcenv = tcenv; warn = _53_3378.warn; cache = _53_3378.cache; nolabels = _53_3378.nolabels; use_zfuel_name = _53_3378.use_zfuel_name; encode_non_total_function_typ = _53_3378.encode_non_total_function_typ})
end))

let set_env = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _53_3384::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun _53_3386 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _53_3392 = hd
in {bindings = _53_3392.bindings; depth = _53_3392.depth; tcenv = _53_3392.tcenv; warn = _53_3392.warn; cache = refs; nolabels = _53_3392.nolabels; use_zfuel_name = _53_3392.use_zfuel_name; encode_non_total_function_typ = _53_3392.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun _53_3395 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _53_3399::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun _53_3401 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _53_3402 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _53_3403 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_53_3406::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _53_3411 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init = (fun tcenv -> (let _53_3413 = (init_env tcenv)
in (let _53_3415 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _53_3418 = (push_env ())
in (let _53_3420 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _53_3423 = (let _119_2335 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _119_2335))
in (let _53_3425 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _53_3428 = (mark_env ())
in (let _53_3430 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _53_3433 = (reset_mark_env ())
in (let _53_3435 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _53_3438 = (commit_mark_env ())
in (let _53_3440 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _119_2349 = (let _119_2348 = (let _119_2347 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _119_2347))
in FStar_ToSMT_Term.Caption (_119_2348))
in (_119_2349)::decls)
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _53_3449 = (encode_sigelt env se)
in (match (_53_3449) with
| (decls, env) -> begin
(let _53_3450 = (set_env env)
in (let _119_2350 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _119_2350)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let _53_3455 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _119_2355 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.fprint2 "Encoding externals for %s ... %s exports\n" name _119_2355))
end else begin
()
end
in (let env = (get_env tcenv)
in (let _53_3462 = (encode_signature (let _53_3458 = env
in {bindings = _53_3458.bindings; depth = _53_3458.depth; tcenv = _53_3458.tcenv; warn = false; cache = _53_3458.cache; nolabels = _53_3458.nolabels; use_zfuel_name = _53_3458.use_zfuel_name; encode_non_total_function_typ = _53_3458.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_53_3462) with
| (decls, env) -> begin
(let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _53_3468 = (set_env (let _53_3466 = env
in {bindings = _53_3466.bindings; depth = _53_3466.depth; tcenv = _53_3466.tcenv; warn = true; cache = _53_3466.cache; nolabels = _53_3466.nolabels; use_zfuel_name = _53_3466.use_zfuel_name; encode_non_total_function_typ = _53_3466.encode_non_total_function_typ}))
in (let _53_3470 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.fprint1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _53_3475 = (let _119_2364 = (let _119_2363 = (let _119_2362 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _119_2362))
in (FStar_Util.format1 "Starting query at %s" _119_2363))
in (push _119_2364))
in (let pop = (fun _53_3478 -> (match (()) with
| () -> begin
(let _119_2369 = (let _119_2368 = (let _119_2367 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _119_2367))
in (FStar_Util.format1 "Ending query at %s" _119_2368))
in (pop _119_2369))
end))
in (let _53_3508 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _53_3491 = (let _119_2373 = (FStar_List.filter (fun _53_32 -> (match (_53_32) with
| FStar_Tc_Env.Binding_sig (_53_3485) -> begin
false
end
| _53_3488 -> begin
true
end)) bindings)
in (encode_env_bindings env _119_2373))
in (match (_53_3491) with
| (env_decls, env) -> begin
(let _53_3492 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _119_2374 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.fprint1 "Encoding query formula: %s\n" _119_2374))
end else begin
()
end
in (let _53_3497 = (encode_formula_with_labels q env)
in (match (_53_3497) with
| (phi, labels, qdecls) -> begin
(let _53_3500 = (encode_labels labels)
in (match (_53_3500) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _119_2376 = (let _119_2375 = (FStar_ToSMT_Term.mkNot phi)
in (_119_2375, Some ("query")))
in FStar_ToSMT_Term.Assume (_119_2376))
in (let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_53_3508) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _53_3515); FStar_ToSMT_Term.hash = _53_3512; FStar_ToSMT_Term.freevars = _53_3510}, _53_3520) -> begin
(let _53_3523 = (pop ())
in ())
end
| _53_3526 when tcenv.FStar_Tc_Env.admit -> begin
(let _53_3527 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _53_3531) -> begin
(let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (let _53_3535 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _53_3541 -> (match (_53_3541) with
| (n, i) -> begin
(let _119_2399 = (let _119_2398 = (let _119_2383 = (let _119_2382 = (FStar_Util.string_of_int n)
in (let _119_2381 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _119_2382 _119_2381)))
in FStar_ToSMT_Term.Caption (_119_2383))
in (let _119_2397 = (let _119_2396 = (let _119_2388 = (let _119_2387 = (let _119_2386 = (let _119_2385 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _119_2384 = (FStar_ToSMT_Term.n_fuel n)
in (_119_2385, _119_2384)))
in (FStar_ToSMT_Term.mkEq _119_2386))
in (_119_2387, None))
in FStar_ToSMT_Term.Assume (_119_2388))
in (let _119_2395 = (let _119_2394 = (let _119_2393 = (let _119_2392 = (let _119_2391 = (let _119_2390 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _119_2389 = (FStar_ToSMT_Term.n_fuel i)
in (_119_2390, _119_2389)))
in (FStar_ToSMT_Term.mkEq _119_2391))
in (_119_2392, None))
in FStar_ToSMT_Term.Assume (_119_2393))
in (_119_2394)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_119_2396)::_119_2395))
in (_119_2398)::_119_2397))
in (FStar_List.append _119_2399 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _119_2403 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _119_2402 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_119_2403, _119_2402)))
in (let alt_configs = (let _119_2422 = (let _119_2421 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _119_2406 = (let _119_2405 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _119_2404 = (FStar_ST.read FStar_Options.max_ifuel)
in (_119_2405, _119_2404)))
in (_119_2406)::[])
end else begin
[]
end
in (let _119_2420 = (let _119_2419 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _119_2409 = (let _119_2408 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _119_2407 = (FStar_ST.read FStar_Options.max_ifuel)
in (_119_2408, _119_2407)))
in (_119_2409)::[])
end else begin
[]
end
in (let _119_2418 = (let _119_2417 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _119_2412 = (let _119_2411 = (FStar_ST.read FStar_Options.max_fuel)
in (let _119_2410 = (FStar_ST.read FStar_Options.max_ifuel)
in (_119_2411, _119_2410)))
in (_119_2412)::[])
end else begin
[]
end
in (let _119_2416 = (let _119_2415 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _119_2414 = (let _119_2413 = (FStar_ST.read FStar_Options.min_fuel)
in (_119_2413, 1))
in (_119_2414)::[])
end else begin
[]
end
in (_119_2415)::[])
in (_119_2417)::_119_2416))
in (_119_2419)::_119_2418))
in (_119_2421)::_119_2420))
in (FStar_List.flatten _119_2422))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _53_3550 -> begin
errs
end)
in (let _53_3552 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _119_2430 = (let _119_2425 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _119_2425))
in (let _119_2429 = (let _119_2426 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _119_2426 FStar_Util.string_of_int))
in (let _119_2428 = (let _119_2427 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _119_2427 FStar_Util.string_of_int))
in (FStar_Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _119_2430 _119_2429 _119_2428))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _53_33 -> (match (_53_33) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _119_2441 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _119_2441 (cb mi p [])))
end
| _53_3564 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _119_2443 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _119_2443 (fun _53_3570 -> (match (_53_3570) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _53_3573 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _53_3576 p alt _53_3581 -> (match ((_53_3576, _53_3581)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _119_2451 = (let _119_2448 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _119_2448))
in (let _119_2450 = (FStar_Util.string_of_int prev_fuel)
in (let _119_2449 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _119_2451 _119_2450 _119_2449))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _119_2452 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _119_2452 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let _53_3586 = (let _119_2458 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _119_2458 q))
in (match (_53_3586) with
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
in (let _53_3587 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _53_3592 = (push "query")
in (let _53_3599 = (encode_formula_with_labels q env)
in (match (_53_3599) with
| (f, _53_3596, _53_3598) -> begin
(let _53_3600 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_3604) -> begin
true
end
| _53_3608 -> begin
false
end))
end)))))

let solver = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

let dummy = {FStar_Tc_Env.init = (fun _53_3609 -> ()); FStar_Tc_Env.push = (fun _53_3611 -> ()); FStar_Tc_Env.pop = (fun _53_3613 -> ()); FStar_Tc_Env.mark = (fun _53_3615 -> ()); FStar_Tc_Env.reset_mark = (fun _53_3617 -> ()); FStar_Tc_Env.commit_mark = (fun _53_3619 -> ()); FStar_Tc_Env.encode_modul = (fun _53_3621 _53_3623 -> ()); FStar_Tc_Env.encode_sig = (fun _53_3625 _53_3627 -> ()); FStar_Tc_Env.solve = (fun _53_3629 _53_3631 -> ()); FStar_Tc_Env.is_trivial = (fun _53_3633 _53_3635 -> false); FStar_Tc_Env.finish = (fun _53_3637 -> ()); FStar_Tc_Env.refresh = (fun _53_3638 -> ())}




