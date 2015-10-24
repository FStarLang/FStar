
open Prims
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _53_40 -> (match (_53_40) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (FStar_List.filter (fun _53_1 -> (match (_53_1) with
| (FStar_Util.Inl (_53_44), _53_47) -> begin
false
end
| _53_50 -> begin
true
end)) args))

let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText a.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end)

let mk_typ_projector_name = (fun lid a -> (let _118_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _118_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _118_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _118_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _118_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _118_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _53_62 -> (match (()) with
| () -> begin
(let _118_30 = (let _118_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _118_29 lid.FStar_Absyn_Syntax.str))
in (FStar_All.failwith _118_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _118_31 = (FStar_Absyn_Util.compress_typ t)
in _118_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_66) -> begin
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
| _53_75 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun lid i -> (let _118_37 = (let _118_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str _118_36))
in (FStar_All.pipe_left escape _118_37)))

let mk_typ_projector = (fun lid a -> (let _118_43 = (let _118_42 = (mk_typ_projector_name lid a)
in (_118_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _118_43)))

let mk_term_projector = (fun lid a -> (let _118_49 = (let _118_48 = (mk_term_projector_name lid a)
in (_118_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _118_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _118_55 = (let _118_54 = (mk_term_projector_name_by_pos lid i)
in (_118_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _118_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t")))

let varops = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _53_101 -> (match (()) with
| () -> begin
(let _118_159 = (FStar_Util.smap_create 100)
in (let _118_158 = (FStar_Util.smap_create 100)
in (_118_159, _118_158)))
end))
in (let scopes = (let _118_161 = (let _118_160 = (new_scope ())
in (_118_160)::[])
in (FStar_Util.mk_ref _118_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _118_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _118_165 (fun _53_109 -> (match (_53_109) with
| (names, _53_108) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_53_112) -> begin
(let _53_114 = (FStar_Util.incr ctr)
in (let _118_167 = (let _118_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _118_166))
in (Prims.strcat (Prims.strcat y "__") _118_167)))
end)
in (let top_scope = (let _118_169 = (let _118_168 = (FStar_ST.read scopes)
in (FStar_List.hd _118_168))
in (FStar_All.pipe_left Prims.fst _118_169))
in (let _53_118 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _118_175 = (let _118_174 = (FStar_All.pipe_left mk_unique pp.FStar_Absyn_Syntax.idText)
in (Prims.strcat _118_174 "__"))
in (Prims.strcat _118_175 rn.FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Absyn_Syntax.str))
in (let next_id = (fun _53_126 -> (match (()) with
| () -> begin
(let _53_127 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _118_183 = (let _118_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _118_182))
in (FStar_Util.format2 "%s_%s" pfx _118_183)))
in (let string_const = (fun s -> (match ((let _118_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _118_187 (fun _53_136 -> (match (_53_136) with
| (_53_134, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _118_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _118_188))
in (let top_scope = (let _118_190 = (let _118_189 = (FStar_ST.read scopes)
in (FStar_List.hd _118_189))
in (FStar_All.pipe_left Prims.snd _118_190))
in (let _53_143 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _53_146 -> (match (()) with
| () -> begin
(let _118_195 = (let _118_194 = (new_scope ())
in (let _118_193 = (FStar_ST.read scopes)
in (_118_194)::_118_193))
in (FStar_ST.op_Colon_Equals scopes _118_195))
end))
in (let pop = (fun _53_148 -> (match (()) with
| () -> begin
(let _118_199 = (let _118_198 = (FStar_ST.read scopes)
in (FStar_List.tl _118_198))
in (FStar_ST.op_Colon_Equals scopes _118_199))
end))
in (let mark = (fun _53_150 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _53_152 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _53_154 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _53_167 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _53_172 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _53_175 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (let _118_215 = (let _118_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _118_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_118_214, _118_213)))
in (FStar_Absyn_Util.mkbvd _118_215)))

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
| Binding_var (_53_180) -> begin
_53_180
end))

let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_53_183) -> begin
_53_183
end))

let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_53_186) -> begin
_53_186
end))

let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_53_189) -> begin
_53_189
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t")))

let print_env = (fun e -> (let _118_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _53_2 -> (match (_53_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _53_214) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _118_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _118_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_118_311))
end else begin
None
end)

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _118_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _118_316))))

let gen_term_var = (fun env x -> (let ysym = (let _118_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _118_321))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _53_233 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _53_233.tcenv; warn = _53_233.warn; cache = _53_233.cache; nolabels = _53_233.nolabels; use_zfuel_name = _53_233.use_zfuel_name; encode_non_total_function_typ = _53_233.encode_non_total_function_typ})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _53_239 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _53_239.depth; tcenv = _53_239.tcenv; warn = _53_239.warn; cache = _53_239.cache; nolabels = _53_239.nolabels; use_zfuel_name = _53_239.use_zfuel_name; encode_non_total_function_typ = _53_239.encode_non_total_function_typ})))))

let push_term_var = (fun env x t -> (let _53_244 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _53_244.depth; tcenv = _53_244.tcenv; warn = _53_244.warn; cache = _53_244.cache; nolabels = _53_244.nolabels; use_zfuel_name = _53_244.use_zfuel_name; encode_non_total_function_typ = _53_244.encode_non_total_function_typ}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _53_3 -> (match (_53_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _53_254 -> begin
None
end)))) with
| None -> begin
(let _118_336 = (let _118_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _118_335))
in (FStar_All.failwith _118_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _118_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _118_341))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _53_264 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _53_264.tcenv; warn = _53_264.warn; cache = _53_264.cache; nolabels = _53_264.nolabels; use_zfuel_name = _53_264.use_zfuel_name; encode_non_total_function_typ = _53_264.encode_non_total_function_typ})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _53_270 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _53_270.depth; tcenv = _53_270.tcenv; warn = _53_270.warn; cache = _53_270.cache; nolabels = _53_270.nolabels; use_zfuel_name = _53_270.use_zfuel_name; encode_non_total_function_typ = _53_270.encode_non_total_function_typ})))))

let push_typ_var = (fun env x t -> (let _53_275 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _53_275.depth; tcenv = _53_275.tcenv; warn = _53_275.warn; cache = _53_275.cache; nolabels = _53_275.nolabels; use_zfuel_name = _53_275.use_zfuel_name; encode_non_total_function_typ = _53_275.encode_non_total_function_typ}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _53_4 -> (match (_53_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _53_285 -> begin
None
end)))) with
| None -> begin
(let _118_356 = (let _118_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _118_355))
in (FStar_All.failwith _118_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _118_367 = (let _53_295 = env
in (let _118_366 = (let _118_365 = (let _118_364 = (let _118_363 = (let _118_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _118_361 -> Some (_118_361)) _118_362))
in (x, fname, _118_363, None))
in Binding_fvar (_118_364))
in (_118_365)::env.bindings)
in {bindings = _118_366; depth = _53_295.depth; tcenv = _53_295.tcenv; warn = _53_295.warn; cache = _53_295.cache; nolabels = _53_295.nolabels; use_zfuel_name = _53_295.use_zfuel_name; encode_non_total_function_typ = _53_295.encode_non_total_function_typ}))
in (fname, ftok, _118_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _53_5 -> (match (_53_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _53_307 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _118_378 = (let _118_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _118_377))
in (FStar_All.failwith _118_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _53_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _53_317.depth; tcenv = _53_317.tcenv; warn = _53_317.warn; cache = _53_317.cache; nolabels = _53_317.nolabels; use_zfuel_name = _53_317.use_zfuel_name; encode_non_total_function_typ = _53_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _53_326 = (lookup_lid env x)
in (match (_53_326) with
| (t1, t2, _53_325) -> begin
(let t3 = (let _118_395 = (let _118_394 = (let _118_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_118_393)::[])
in (f, _118_394))
in (FStar_ToSMT_Term.mkApp _118_395))
in (let _53_328 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _53_328.depth; tcenv = _53_328.tcenv; warn = _53_328.warn; cache = _53_328.cache; nolabels = _53_328.nolabels; use_zfuel_name = _53_328.use_zfuel_name; encode_non_total_function_typ = _53_328.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun env a -> (let _53_335 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _53_339 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_53_343, fuel::[]) -> begin
if (let _118_399 = (let _118_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _118_398 Prims.fst))
in (FStar_Util.starts_with _118_399 "fuel")) then begin
(let _118_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _118_400 fuel))
end else begin
t
end
end
| _53_349 -> begin
t
end)
end
| _53_351 -> begin
(let _118_402 = (let _118_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _118_401))
in (FStar_All.failwith _118_402))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _53_359 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_359) with
| (x, _53_356, _53_358) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _53_365 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_365) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _53_369; FStar_ToSMT_Term.freevars = _53_367}) when env.use_zfuel_name -> begin
(g, zf)
end
| _53_377 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _53_387 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _118_417 = (let _53_392 = env
in (let _118_416 = (let _118_415 = (let _118_414 = (let _118_413 = (let _118_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _118_411 -> Some (_118_411)) _118_412))
in (x, fname, _118_413))
in Binding_ftvar (_118_414))
in (_118_415)::env.bindings)
in {bindings = _118_416; depth = _53_392.depth; tcenv = _53_392.tcenv; warn = _53_392.warn; cache = _53_392.cache; nolabels = _53_392.nolabels; use_zfuel_name = _53_392.use_zfuel_name; encode_non_total_function_typ = _53_392.encode_non_total_function_typ}))
in (fname, ftok, _118_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _53_6 -> (match (_53_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _53_403 -> begin
None
end)))) with
| None -> begin
(let _118_424 = (let _118_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _118_423))
in (FStar_All.failwith _118_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _53_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _53_411.depth; tcenv = _53_411.tcenv; warn = _53_411.warn; cache = _53_411.cache; nolabels = _53_411.nolabels; use_zfuel_name = _53_411.use_zfuel_name; encode_non_total_function_typ = _53_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _118_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _118_435 Prims.snd))) with
| None -> begin
(let _118_437 = (let _118_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _118_436))
in (FStar_All.failwith _118_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _118_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _118_440 Prims.fst)))

let tok_of_name = (fun env nm -> (FStar_Util.find_map env.bindings (fun _53_7 -> (match (_53_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _53_436 -> begin
None
end))))

let mkForall_fuel' = (fun n _53_441 -> (match (_53_441) with
| (pats, vars, body) -> begin
(let fallback = (fun _53_443 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(let _53_446 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_446) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _53_456 -> begin
p
end)))))
in (let pats = (FStar_List.map add_fuel pats)
in (let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _118_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _118_453))
end
| _53_469 -> begin
(let _118_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _118_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _53_472 -> begin
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
(let _118_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _118_460 FStar_Option.isNone))
end
| _53_510 -> begin
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

let trivial_post = (fun t -> (let _118_482 = (let _118_481 = (let _118_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_118_479)::[])
in (let _118_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_118_481, _118_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _118_482 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _118_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _118_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _118_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _118_490))
end
| _53_527 -> begin
(let _118_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _118_491))
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
(let _118_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _118_504))
end
| _53_542 -> begin
(let _118_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _118_505))
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
| _53_561 -> begin
false
end))

let is_eta = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _53_572; FStar_ToSMT_Term.freevars = _53_570}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _53_590) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _53_597 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_53_599, []) -> begin
(let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _53_605 -> begin
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
(let _118_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _118_561))
end
| FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _118_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _118_562))
end
| FStar_Absyn_Syntax.Const_int (i) -> begin
(let _118_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _118_563))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _118_567 = (let _118_566 = (let _118_565 = (let _118_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _118_564))
in (_118_565)::[])
in ("FStar.Int32.Int32", _118_566))
in (FStar_ToSMT_Term.mkApp _118_567))
end
| FStar_Absyn_Syntax.Const_string (bytes, _53_627) -> begin
(let _118_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _118_568))
end
| c -> begin
(let _118_570 = (let _118_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _118_569))
in (FStar_All.failwith _118_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_638) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_53_641) -> begin
(let _118_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _118_579))
end
| _53_644 -> begin
if norm then begin
(let _118_580 = (whnf env t)
in (aux false _118_580))
end else begin
(let _118_583 = (let _118_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _118_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _118_582 _118_581)))
in (FStar_All.failwith _118_583))
end
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _118_620 = (FStar_Absyn_Util.compress_kind k)
in _118_620.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_649, k0) -> begin
(let _53_653 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _118_622 = (FStar_Absyn_Print.kind_to_string k)
in (let _118_621 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _118_622 _118_621)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _53_657) -> begin
(let _118_624 = (let _118_623 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _118_623))
in (_118_624, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _118_625 = (varops.fresh "t")
in (_118_625, FStar_ToSMT_Term.Type_sort))
in (let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (let _53_672 = (encode_binders None bs env)
in (match (_53_672) with
| (vars, guards, env', decls, _53_671) -> begin
(let app = (mk_ApplyT t vars)
in (let _53_676 = (encode_knd kbody env' app)
in (match (_53_676) with
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
| _53_695 -> begin
(let _118_634 = (let _118_633 = (let _118_632 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_632))
in (_118_633, body))
in (FStar_ToSMT_Term.mkAnd _118_634))
end)
in (let _118_636 = (let _118_635 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _118_635))
in (FStar_ToSMT_Term.mkForall _118_636)))))
end
| _53_698 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _118_638 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _118_638 (FStar_List.filter (fun _53_703 -> (match (_53_703) with
| (x, _53_702) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _53_709) -> begin
(let _118_641 = (let _118_640 = (let _118_639 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _118_639))
in (FStar_ToSMT_Term.mkApp _118_640))
in (_118_641, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _118_642 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_118_642))
end else begin
None
end
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _118_644 = (let _118_643 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _118_643))
in (FStar_ToSMT_Term.mkApp _118_644))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _118_653 = (let _118_652 = (let _118_651 = (let _118_650 = (let _118_649 = (let _118_648 = (let _118_647 = (let _118_646 = (let _118_645 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_645))
in (_118_646, k_interp))
in (FStar_ToSMT_Term.mkAnd _118_647))
in (t_has_k, _118_648))
in (FStar_ToSMT_Term.mkIff _118_649))
in (((t_has_k)::[])::[], (tsym)::cvars, _118_650))
in (FStar_ToSMT_Term.mkForall _118_651))
in (_118_652, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_118_653))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _53_721 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _53_724 -> begin
(let _118_655 = (let _118_654 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _118_654))
in (FStar_All.failwith _118_655))
end))
and encode_knd = (fun k env t -> (let _53_730 = (encode_knd_term k env)
in (match (_53_730) with
| (k, decls) -> begin
(let _118_659 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_118_659, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _53_734 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _118_663 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.fprint1 "Encoding binders %s\n" _118_663))
end else begin
()
end
in (let _53_784 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_741 b -> (match (_53_741) with
| (vars, guards, env, decls, names) -> begin
(let _53_778 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_744}) -> begin
(let a = (unmangle a)
in (let _53_753 = (gen_typ_var env a)
in (match (_53_753) with
| (aasym, aa, env') -> begin
(let _53_754 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _118_667 = (FStar_Absyn_Print.strBvd a)
in (let _118_666 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _118_667 aasym _118_666)))
end else begin
()
end
in (let _53_758 = (encode_knd k env aa)
in (match (_53_758) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_760}) -> begin
(let x = (unmangle x)
in (let _53_769 = (gen_term_var env x)
in (match (_53_769) with
| (xxsym, xx, env') -> begin
(let _53_772 = (let _118_668 = (norm_t env t)
in (encode_typ_pred fuel_opt _118_668 env xx))
in (match (_53_772) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_53_778) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_53_784) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_792 = (encode_typ_term t env)
in (match (_53_792) with
| (t, decls) -> begin
(let _118_673 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_118_673, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_800 = (encode_typ_term t env)
in (match (_53_800) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _118_678 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_118_678, decls))
end
| Some (f) -> begin
(let _118_679 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_118_679, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _118_682 = (lookup_typ_var env a)
in (_118_682, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _118_683 = (lookup_free_tvar env fv)
in (_118_683, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(let _53_821 = (encode_binders None binders env)
in (match (_53_821) with
| (vars, guards, env', decls, _53_820) -> begin
(let fsym = (let _118_684 = (varops.fresh "f")
in (_118_684, FStar_ToSMT_Term.Term_sort))
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _53_827 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_53_827) with
| (pre_opt, res_t) -> begin
(let _53_830 = (encode_typ_pred None res_t env' app)
in (match (_53_830) with
| (res_pred, decls') -> begin
(let _53_839 = (match (pre_opt) with
| None -> begin
(let _118_685 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_685, decls))
end
| Some (pre) -> begin
(let _53_836 = (encode_formula pre env')
in (match (_53_836) with
| (guard, decls0) -> begin
(let _118_686 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_118_686, (FStar_List.append decls decls0)))
end))
end)
in (match (_53_839) with
| (guards, guard_decls) -> begin
(let t_interp = (let _118_688 = (let _118_687 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _118_687))
in (FStar_ToSMT_Term.mkForall _118_688))
in (let cvars = (let _118_690 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _118_690 (FStar_List.filter (fun _53_844 -> (match (_53_844) with
| (x, _53_843) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _53_850) -> begin
(let _118_693 = (let _118_692 = (let _118_691 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _118_691))
in (FStar_ToSMT_Term.mkApp _118_692))
in (_118_693, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _118_694 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_118_694))
end else begin
None
end
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _118_696 = (let _118_695 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_695))
in (FStar_ToSMT_Term.mkApp _118_696))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _118_698 = (let _118_697 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_118_697, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_118_698))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _118_705 = (let _118_704 = (let _118_703 = (let _118_702 = (let _118_701 = (let _118_700 = (let _118_699 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _118_699))
in (f_has_t, _118_700))
in (FStar_ToSMT_Term.mkImp _118_701))
in (((f_has_t)::[])::[], (fsym)::cvars, _118_702))
in (mkForall_fuel _118_703))
in (_118_704, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_118_705))
in (let t_interp = (let _118_709 = (let _118_708 = (let _118_707 = (let _118_706 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _118_706))
in (FStar_ToSMT_Term.mkForall _118_707))
in (_118_708, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_118_709))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _53_866 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let t_kinding = (let _118_711 = (let _118_710 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_118_710, None))
in FStar_ToSMT_Term.Assume (_118_711))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _118_718 = (let _118_717 = (let _118_716 = (let _118_715 = (let _118_714 = (let _118_713 = (let _118_712 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _118_712))
in (f_has_t, _118_713))
in (FStar_ToSMT_Term.mkImp _118_714))
in (((f_has_t)::[])::[], (fsym)::[], _118_715))
in (mkForall_fuel _118_716))
in (_118_717, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_118_718))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_53_877) -> begin
(let _53_896 = (match ((FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _53_886; FStar_Absyn_Syntax.pos = _53_884; FStar_Absyn_Syntax.fvs = _53_882; FStar_Absyn_Syntax.uvs = _53_880} -> begin
(x, f)
end
| _53_893 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_896) with
| (x, f) -> begin
(let _53_899 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_53_899) with
| (base_t, decls) -> begin
(let _53_903 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_903) with
| (x, xtm, env') -> begin
(let _53_906 = (encode_formula f env')
in (match (_53_906) with
| (refinement, decls') -> begin
(let _53_909 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_909) with
| (fsym, fterm) -> begin
(let encoding = (let _118_720 = (let _118_719 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_118_719, refinement))
in (FStar_ToSMT_Term.mkAnd _118_720))
in (let cvars = (let _118_722 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _118_722 (FStar_List.filter (fun _53_914 -> (match (_53_914) with
| (y, _53_913) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_921, _53_923) -> begin
(let _118_725 = (let _118_724 = (let _118_723 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _118_723))
in (FStar_ToSMT_Term.mkApp _118_724))
in (_118_725, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _118_727 = (let _118_726 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_726))
in (FStar_ToSMT_Term.mkApp _118_727))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (let assumption = (let _118_729 = (let _118_728 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _118_728))
in (FStar_ToSMT_Term.mkForall _118_729))
in (let t_decls = (let _118_736 = (let _118_735 = (let _118_734 = (let _118_733 = (let _118_732 = (let _118_731 = (let _118_730 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_118_730))
in (assumption, _118_731))
in FStar_ToSMT_Term.Assume (_118_732))
in (_118_733)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_118_734)
in (tdecl)::_118_735)
in (FStar_List.append (FStar_List.append decls decls') _118_736))
in (let _53_936 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _118_737 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _118_737))
in (let _53_945 = (encode_knd k env ttm)
in (match (_53_945) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let is_full_app = (fun _53_952 -> (match (()) with
| () -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind head)
in (let _53_957 = (FStar_Absyn_Util.kind_formals kk)
in (match (_53_957) with
| (formals, _53_956) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _53_964 = (encode_args args env)
in (match (_53_964) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _53_970 = (encode_args args env)
in (match (_53_970) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _118_742 = (let _118_741 = (FStar_List.map (fun _53_10 -> (match (_53_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _118_741))
in (FStar_ToSMT_Term.mkApp _118_742))
in (t, decls)))
end else begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _118_743 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _118_743))
in (let _53_986 = (encode_knd k env ttm)
in (match (_53_986) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _53_989 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(let _53_1001 = (encode_binders None bs env)
in (match (_53_1001) with
| (vars, guards, env, decls, _53_1000) -> begin
(let _53_1004 = (encode_typ_term body env)
in (match (_53_1004) with
| (body, decls') -> begin
(let key_body = (let _118_747 = (let _118_746 = (let _118_745 = (let _118_744 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_744, body))
in (FStar_ToSMT_Term.mkImp _118_745))
in ([], vars, _118_746))
in (FStar_ToSMT_Term.mkForall _118_747))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1010, _53_1012) -> begin
(let _118_750 = (let _118_749 = (let _118_748 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _118_748))
in (FStar_ToSMT_Term.mkApp _118_749))
in (_118_750, []))
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
in (let t = (let _118_752 = (let _118_751 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_751))
in (FStar_ToSMT_Term.mkApp _118_752))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _118_759 = (let _118_758 = (let _118_757 = (let _118_756 = (let _118_755 = (let _118_754 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_753 = (FStar_ToSMT_Term.mkEq (app, body))
in (_118_754, _118_753)))
in (FStar_ToSMT_Term.mkImp _118_755))
in (((app)::[])::[], (FStar_List.append vars cvars), _118_756))
in (FStar_ToSMT_Term.mkForall _118_757))
in (_118_758, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_118_759))
in (let kinding = (let _53_1027 = (let _118_760 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _118_760 env t))
in (match (_53_1027) with
| (ktm, decls'') -> begin
(let _118_764 = (let _118_763 = (let _118_762 = (let _118_761 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_118_761, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_118_762))
in (_118_763)::[])
in (FStar_List.append decls'' _118_764))
end))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _53_1030 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _53_1034) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_53_1038) -> begin
(let _118_765 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _118_765 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _118_770 = (let _118_769 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _118_768 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _118_767 = (FStar_Absyn_Print.typ_to_string t0)
in (let _118_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _118_769 _118_768 _118_767 _118_766)))))
in (FStar_All.failwith _118_770))
end)))
and encode_exp = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1049) -> begin
(let _118_773 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _118_773 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1056) -> begin
(let _118_774 = (lookup_free_var env v)
in (_118_774, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _118_775 = (encode_const c)
in (_118_775, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_1064) -> begin
(let _53_1067 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_1071)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _53_1077) -> begin
(let e = (let _118_776 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _118_776))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _53_1086 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _118_779 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_118_779, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _53_1090 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _118_780 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _118_780)) then begin
(fallback ())
end else begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(let _53_1102 = (FStar_Util.first_N nformals bs)
in (match (_53_1102) with
| (bs0, rest) -> begin
(let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _53_1106 -> begin
(FStar_All.failwith "Impossible")
end)
in (let e = (let _118_782 = (let _118_781 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _118_781))
in (FStar_Absyn_Syntax.mk_Exp_abs _118_782 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(let _53_1115 = (encode_binders None bs env)
in (match (_53_1115) with
| (vars, guards, envbody, decls, _53_1114) -> begin
(let _53_1118 = (encode_exp body envbody)
in (match (_53_1118) with
| (body, decls') -> begin
(let key_body = (let _118_786 = (let _118_785 = (let _118_784 = (let _118_783 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_783, body))
in (FStar_ToSMT_Term.mkImp _118_784))
in ([], vars, _118_785))
in (FStar_ToSMT_Term.mkForall _118_786))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1124, _53_1126) -> begin
(let _118_789 = (let _118_788 = (let _118_787 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _118_787))
in (FStar_ToSMT_Term.mkApp _118_788))
in (_118_789, []))
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
in (let f = (let _118_791 = (let _118_790 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _118_790))
in (FStar_ToSMT_Term.mkApp _118_791))
in (let app = (mk_ApplyE f vars)
in (let _53_1140 = (encode_typ_pred None tfun env f)
in (match (_53_1140) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _118_793 = (let _118_792 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_118_792, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_118_793))
in (let interp_f = (let _118_800 = (let _118_799 = (let _118_798 = (let _118_797 = (let _118_796 = (let _118_795 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _118_794 = (FStar_ToSMT_Term.mkEq (app, body))
in (_118_795, _118_794)))
in (FStar_ToSMT_Term.mkImp _118_796))
in (((app)::[])::[], (FStar_List.append vars cvars), _118_797))
in (FStar_ToSMT_Term.mkForall _118_798))
in (_118_799, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_118_800))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _53_1144 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _53_1147 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _53_1158); FStar_Absyn_Syntax.tk = _53_1155; FStar_Absyn_Syntax.pos = _53_1153; FStar_Absyn_Syntax.fvs = _53_1151; FStar_Absyn_Syntax.uvs = _53_1149}, (FStar_Util.Inl (_53_1173), _53_1176)::(FStar_Util.Inr (v1), _53_1170)::(FStar_Util.Inr (v2), _53_1165)::[]) when (FStar_Absyn_Syntax.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(let _53_1183 = (encode_exp v1 env)
in (match (_53_1183) with
| (v1, decls1) -> begin
(let _53_1186 = (encode_exp v2 env)
in (match (_53_1186) with
| (v2, decls2) -> begin
(let _118_801 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_118_801, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_53_1196); FStar_Absyn_Syntax.tk = _53_1194; FStar_Absyn_Syntax.pos = _53_1192; FStar_Absyn_Syntax.fvs = _53_1190; FStar_Absyn_Syntax.uvs = _53_1188}, _53_1200) -> begin
(let _118_802 = (whnf_e env e)
in (encode_exp _118_802 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(let _53_1209 = (encode_args args_e env)
in (match (_53_1209) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _53_1214 = (encode_exp head env)
in (match (_53_1214) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _53_1223 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_53_1223) with
| (formals, rest) -> begin
(let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _118_805 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _118_805 (FStar_Absyn_Util.subst_typ subst)))
in (let _53_1228 = (encode_typ_pred None ty env app_tm)
in (match (_53_1228) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _118_807 = (let _118_806 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_118_806, None))
in FStar_ToSMT_Term.Assume (_118_807))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _53_1235 = (lookup_free_var_sym env fv)
in (match (_53_1235) with
| (fname, fuel_args) -> begin
(let tm = (let _118_813 = (let _118_812 = (let _118_811 = (FStar_List.map (fun _53_11 -> (match (_53_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _118_811))
in (fname, _118_812))
in (FStar_ToSMT_Term.mkApp' _118_813))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _53_1242 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _118_815 = (FStar_Absyn_Print.exp_to_string head)
in (let _118_814 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _118_815 _118_814)))
end else begin
()
end
in (let head_type = (let _118_818 = (let _118_817 = (let _118_816 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _118_816))
in (whnf env _118_817))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _118_818))
in (let _53_1245 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _118_821 = (FStar_Absyn_Print.exp_to_string head)
in (let _118_820 = (FStar_Absyn_Print.tag_of_exp head)
in (let _118_819 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _118_821 _118_820 _118_819))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _118_825 = (let _118_824 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _118_823 = (FStar_Absyn_Print.exp_to_string e0)
in (let _118_822 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _118_824 _118_823 _118_822))))
in (FStar_All.failwith _118_825))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1254) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _53_1258 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_53_1267); FStar_Absyn_Syntax.lbtyp = _53_1265; FStar_Absyn_Syntax.lbeff = _53_1263; FStar_Absyn_Syntax.lbdef = _53_1261}::[]), _53_1273) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _53_1279; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _53_1291 = (encode_exp e1 env)
in (match (_53_1291) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _53_1295 = (encode_exp e2 env')
in (match (_53_1295) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_53_1297) -> begin
(let _53_1299 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _118_826 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_118_826, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _53_1309 = (encode_exp e env)
in (match (_53_1309) with
| (scr, decls) -> begin
(let _53_1349 = (FStar_List.fold_right (fun _53_1313 _53_1316 -> (match ((_53_1313, _53_1316)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _53_1320 _53_1323 -> (match ((_53_1320, _53_1323)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _53_1329 -> (match (_53_1329) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _53_1343 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _53_1340 = (encode_exp w env)
in (match (_53_1340) with
| (w, decls2) -> begin
(let _118_837 = (let _118_836 = (let _118_835 = (let _118_834 = (let _118_833 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _118_833))
in (FStar_ToSMT_Term.mkEq _118_834))
in (guard, _118_835))
in (FStar_ToSMT_Term.mkAnd _118_836))
in (_118_837, decls2))
end))
end)
in (match (_53_1343) with
| (guard, decls2) -> begin
(let _53_1346 = (encode_exp br env)
in (match (_53_1346) with
| (br, decls3) -> begin
(let _118_838 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_118_838, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_53_1349) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_53_1351) -> begin
(let _118_841 = (let _118_840 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _118_839 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _118_840 _118_839)))
in (FStar_All.failwith _118_841))
end))))
and encode_pat = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _53_1358 -> begin
(let _118_844 = (encode_one_pat env pat)
in (_118_844)::[])
end))
and encode_one_pat = (fun env pat -> (let _53_1361 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _118_847 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.fprint1 "Encoding pattern %s\n" _118_847))
end else begin
()
end
in (let _53_1365 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_53_1365) with
| (vars, pat_exp_or_typ) -> begin
(let _53_1386 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _53_1368 v -> (match (_53_1368) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(let _53_1376 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_53_1376) with
| (aa, _53_1374, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(let _53_1383 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_1383) with
| (xx, _53_1381, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_53_1386) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1391) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _118_855 = (let _118_854 = (encode_const c)
in (scrutinee, _118_854))
in (FStar_ToSMT_Term.mkEq _118_855))
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1415, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1424 -> (match (_53_1424) with
| (arg, _53_1423) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _118_858 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _118_858)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1431) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_53_1448) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1452, args) -> begin
(let _118_866 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1460 -> (match (_53_1460) with
| (arg, _53_1459) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _118_865 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _118_865)))
end))))
in (FStar_All.pipe_right _118_866 FStar_List.flatten))
end))
in (let pat_term = (fun _53_1463 -> (match (()) with
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
and encode_args = (fun l env -> (let _53_1493 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _53_1473 x -> (match (_53_1473) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _53_1478) -> begin
(let _53_1482 = (encode_typ_term t env)
in (match (_53_1482) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _53_1486) -> begin
(let _53_1490 = (encode_exp e env)
in (match (_53_1490) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_53_1493) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _53_1499 = (encode_formula_with_labels phi env)
in (match (_53_1499) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _53_1502 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun induction_on new_pats t env -> (let rec list_elements = (fun e -> (match ((let _118_881 = (FStar_Absyn_Util.unmeta_exp e)
in _118_881.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1519); FStar_Absyn_Syntax.tk = _53_1516; FStar_Absyn_Syntax.pos = _53_1514; FStar_Absyn_Syntax.fvs = _53_1512; FStar_Absyn_Syntax.uvs = _53_1510}, _53_1524) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1537); FStar_Absyn_Syntax.tk = _53_1534; FStar_Absyn_Syntax.pos = _53_1532; FStar_Absyn_Syntax.fvs = _53_1530; FStar_Absyn_Syntax.uvs = _53_1528}, _53_1552::(FStar_Util.Inr (hd), _53_1549)::(FStar_Util.Inr (tl), _53_1544)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _118_882 = (list_elements tl)
in (hd)::_118_882)
end
| _53_1557 -> begin
(let _53_1558 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (let v_or_t_pat = (fun p -> (match ((let _118_885 = (FStar_Absyn_Util.unmeta_exp p)
in _118_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1572); FStar_Absyn_Syntax.tk = _53_1569; FStar_Absyn_Syntax.pos = _53_1567; FStar_Absyn_Syntax.fvs = _53_1565; FStar_Absyn_Syntax.uvs = _53_1563}, (FStar_Util.Inl (_53_1582), _53_1585)::(FStar_Util.Inr (e), _53_1579)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1600); FStar_Absyn_Syntax.tk = _53_1597; FStar_Absyn_Syntax.pos = _53_1595; FStar_Absyn_Syntax.fvs = _53_1593; FStar_Absyn_Syntax.uvs = _53_1591}, (FStar_Util.Inl (t), _53_1607)::[]) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _53_1613 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let lemma_pats = (fun p -> (let elts = (list_elements p)
in (match (elts) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1635); FStar_Absyn_Syntax.tk = _53_1632; FStar_Absyn_Syntax.pos = _53_1630; FStar_Absyn_Syntax.fvs = _53_1628; FStar_Absyn_Syntax.uvs = _53_1626}, (FStar_Util.Inr (e), _53_1642)::[]); FStar_Absyn_Syntax.tk = _53_1624; FStar_Absyn_Syntax.pos = _53_1622; FStar_Absyn_Syntax.fvs = _53_1620; FStar_Absyn_Syntax.uvs = _53_1618}::[] when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _118_890 = (list_elements e)
in (FStar_All.pipe_right _118_890 (FStar_List.map (fun branch -> (let _118_889 = (list_elements branch)
in (FStar_All.pipe_right _118_889 (FStar_List.map v_or_t_pat)))))))
end
| _53_1651 -> begin
(let _118_891 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_118_891)::[])
end)))
in (let _53_1694 = (match ((let _118_892 = (FStar_Absyn_Util.compress_typ t)
in _118_892.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _53_1660; FStar_Absyn_Syntax.pos = _53_1658; FStar_Absyn_Syntax.fvs = _53_1656; FStar_Absyn_Syntax.uvs = _53_1654}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _53_1679)::(FStar_Util.Inl (post), _53_1674)::(FStar_Util.Inr (pats), _53_1669)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _118_893 = (lemma_pats pats')
in (binders, pre, post, _118_893)))
end
| _53_1687 -> begin
(FStar_All.failwith "impos")
end)
end
| _53_1689 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_53_1694) with
| (binders, pre, post, patterns) -> begin
(let _53_1701 = (encode_binders None binders env)
in (match (_53_1701) with
| (vars, guards, env, decls, _53_1700) -> begin
(let _53_1721 = (let _118_897 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (let _53_1718 = (let _118_896 = (FStar_All.pipe_right branch (FStar_List.map (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (t), _53_1707) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _53_1712) -> begin
(encode_exp e (let _53_1714 = env
in {bindings = _53_1714.bindings; depth = _53_1714.depth; tcenv = _53_1714.tcenv; warn = _53_1714.warn; cache = _53_1714.cache; nolabels = _53_1714.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1714.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _118_896 FStar_List.unzip))
in (match (_53_1718) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _118_897 FStar_List.unzip))
in (match (_53_1721) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _118_900 = (let _118_899 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _118_899 e))
in (_118_900)::p))))
end
| _53_1731 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _118_906 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_118_906)::p))))
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _118_908 = (let _118_907 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _118_907 tl))
in (aux _118_908 vars))
end
| _53_1743 -> begin
pats
end))
in (let _118_909 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _118_909 vars)))
end)
end)
in (let env = (let _53_1745 = env
in {bindings = _53_1745.bindings; depth = _53_1745.depth; tcenv = _53_1745.tcenv; warn = _53_1745.warn; cache = _53_1745.cache; nolabels = true; use_zfuel_name = _53_1745.use_zfuel_name; encode_non_total_function_typ = _53_1745.encode_non_total_function_typ})
in (let _53_1750 = (let _118_910 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _118_910 env))
in (match (_53_1750) with
| (pre, decls'') -> begin
(let _53_1753 = (let _118_911 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _118_911 env))
in (match (_53_1753) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _118_916 = (let _118_915 = (let _118_914 = (let _118_913 = (let _118_912 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_118_912, post))
in (FStar_ToSMT_Term.mkImp _118_913))
in (pats, vars, _118_914))
in (FStar_ToSMT_Term.mkForall _118_915))
in (_118_916, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f l -> (let _53_1774 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(let _53_1766 = (encode_typ_term t env)
in (match (_53_1766) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(let _53_1771 = (encode_exp e env)
in (match (_53_1771) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_53_1774) with
| (decls, args) -> begin
(let _118_934 = (f args)
in (_118_934, [], decls))
end)))
in (let enc_prop_c = (fun f l -> (let _53_1794 = (FStar_List.fold_right (fun t _53_1782 -> (match (_53_1782) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(let _53_1788 = (encode_formula_with_labels t env)
in (match (_53_1788) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _53_1790 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_53_1794) with
| (phis, labs, decls) -> begin
(let _118_950 = (f phis)
in (_118_950, labs, decls))
end)))
in (let const_op = (fun f _53_1797 -> (f, [], []))
in (let un_op = (fun f l -> (let _118_964 = (FStar_List.hd l)
in (FStar_All.pipe_left f _118_964)))
in (let bin_op = (fun f _53_13 -> (match (_53_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _53_1808 -> begin
(FStar_All.failwith "Impossible")
end))
in (let eq_op = (fun _53_14 -> (match (_53_14) with
| _53_1816::_53_1814::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _53_15 -> (match (_53_15) with
| (FStar_Util.Inl (lhs), _53_1829)::(FStar_Util.Inl (rhs), _53_1824)::[] -> begin
(let _53_1835 = (encode_formula_with_labels rhs env)
in (match (_53_1835) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_1838) -> begin
(l1, labs1, decls1)
end
| _53_1842 -> begin
(let _53_1846 = (encode_formula_with_labels lhs env)
in (match (_53_1846) with
| (l2, labs2, decls2) -> begin
(let _118_978 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_118_978, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _53_1848 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _53_16 -> (match (_53_16) with
| (FStar_Util.Inl (guard), _53_1864)::(FStar_Util.Inl (_then), _53_1859)::(FStar_Util.Inl (_else), _53_1854)::[] -> begin
(let _53_1870 = (encode_formula_with_labels guard env)
in (match (_53_1870) with
| (g, labs1, decls1) -> begin
(let _53_1874 = (encode_formula_with_labels _then env)
in (match (_53_1874) with
| (t, labs2, decls2) -> begin
(let _53_1878 = (encode_formula_with_labels _else env)
in (match (_53_1878) with
| (e, labs3, decls3) -> begin
(let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _53_1881 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _118_990 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _118_990)))
in (let connectives = (let _118_1051 = (let _118_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _118_999))
in (let _118_1050 = (let _118_1049 = (let _118_1005 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _118_1005))
in (let _118_1048 = (let _118_1047 = (let _118_1046 = (let _118_1014 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _118_1014))
in (let _118_1045 = (let _118_1044 = (let _118_1043 = (let _118_1023 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _118_1023))
in (let _118_1042 = (let _118_1041 = (let _118_1029 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _118_1029))
in (_118_1041)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_118_1043)::_118_1042))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_118_1044)
in (_118_1046)::_118_1045))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_118_1047)
in (_118_1049)::_118_1048))
in (_118_1051)::_118_1050))
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _53_1899 = (encode_formula_with_labels phi' env)
in (match (_53_1899) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(let lvar = (let _118_1054 = (varops.fresh "label")
in (_118_1054, FStar_ToSMT_Term.Bool_sort))
in (let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1910; FStar_Absyn_Syntax.pos = _53_1908; FStar_Absyn_Syntax.fvs = _53_1906; FStar_Absyn_Syntax.uvs = _53_1904}, _53_1925::(FStar_Util.Inr (l), _53_1922)::(FStar_Util.Inl (phi), _53_1917)::[]) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let _53_1931 = (encode_exp l env)
in (match (_53_1931) with
| (e, decls) -> begin
(let _53_1934 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_53_1934) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1942; FStar_Absyn_Syntax.pos = _53_1940; FStar_Absyn_Syntax.fvs = _53_1938; FStar_Absyn_Syntax.uvs = _53_1936}, _53_1954::(FStar_Util.Inl (phi), _53_1950)::tl) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _53_1962)::[] -> begin
Some (pat)
end)
in (let _53_1968 = (encode_function_type_as_formula None pat phi env)
in (match (_53_1968) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _53_1970 -> begin
(let _53_1973 = (encode_typ_term phi env)
in (match (_53_1973) with
| (tt, decls) -> begin
(let _118_1055 = (FStar_ToSMT_Term.mk_Valid tt)
in (_118_1055, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _53_1985 = (encode_binders None bs env)
in (match (_53_1985) with
| (vars, guards, env, decls, _53_1984) -> begin
(let _53_2005 = (let _118_1067 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (let _53_2002 = (let _118_1066 = (FStar_All.pipe_right p (FStar_List.map (fun _53_17 -> (match (_53_17) with
| (FStar_Util.Inl (t), _53_1991) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _53_1996) -> begin
(encode_exp e (let _53_1998 = env
in {bindings = _53_1998.bindings; depth = _53_1998.depth; tcenv = _53_1998.tcenv; warn = _53_1998.warn; cache = _53_1998.cache; nolabels = _53_1998.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1998.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _118_1066 FStar_List.unzip))
in (match (_53_2002) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _118_1067 FStar_List.unzip))
in (match (_53_2005) with
| (pats, decls') -> begin
(let _53_2009 = (encode_formula_with_labels body env)
in (match (_53_2009) with
| (body, labs, decls'') -> begin
(let _118_1068 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _118_1068, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _53_2010 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _118_1069 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.fprint1 ">>>> Destructing as formula ... %s\n" _118_1069))
end else begin
()
end
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _53_2022 -> (match (_53_2022) with
| (l, _53_2021) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_53_2025, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _53_2035 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _118_1086 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.fprint1 ">>>> Got QALL [%s]\n" _118_1086))
end else begin
()
end
in (let _53_2043 = (encode_q_body env vars pats body)
in (match (_53_2043) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _118_1089 = (let _118_1088 = (let _118_1087 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _118_1087))
in (FStar_ToSMT_Term.mkForall _118_1088))
in (_118_1089, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _53_2056 = (encode_q_body env vars pats body)
in (match (_53_2056) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _118_1092 = (let _118_1091 = (let _118_1090 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _118_1090))
in (FStar_ToSMT_Term.mkExists _118_1091))
in (_118_1092, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Absyn_Syntax.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Absyn_Syntax.lident  ->  Prims.bool}

let is_Mkprims_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t")))

let prims = (let _53_2062 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_53_2062) with
| (asym, a) -> begin
(let _53_2065 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2065) with
| (xsym, x) -> begin
(let _53_2068 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_53_2068) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_ToSMT_Term.DefineFun ((x, vars, FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (let _118_1135 = (let _118_1134 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _118_1134))
in (FStar_ToSMT_Term.mkApp _118_1135))
in (let vname_decl = (let _118_1137 = (let _118_1136 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _118_1136, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_1137))
in (let _118_1143 = (let _118_1142 = (let _118_1141 = (let _118_1140 = (let _118_1139 = (let _118_1138 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _118_1138))
in (FStar_ToSMT_Term.mkForall _118_1139))
in (_118_1140, None))
in FStar_ToSMT_Term.Assume (_118_1141))
in (_118_1142)::[])
in (vname_decl)::_118_1143))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _118_1303 = (let _118_1152 = (let _118_1151 = (let _118_1150 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1150))
in (quant axy _118_1151))
in (FStar_Absyn_Const.op_Eq, _118_1152))
in (let _118_1302 = (let _118_1301 = (let _118_1159 = (let _118_1158 = (let _118_1157 = (let _118_1156 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _118_1156))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1157))
in (quant axy _118_1158))
in (FStar_Absyn_Const.op_notEq, _118_1159))
in (let _118_1300 = (let _118_1299 = (let _118_1168 = (let _118_1167 = (let _118_1166 = (let _118_1165 = (let _118_1164 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1163 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1164, _118_1163)))
in (FStar_ToSMT_Term.mkLT _118_1165))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1166))
in (quant xy _118_1167))
in (FStar_Absyn_Const.op_LT, _118_1168))
in (let _118_1298 = (let _118_1297 = (let _118_1177 = (let _118_1176 = (let _118_1175 = (let _118_1174 = (let _118_1173 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1172 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1173, _118_1172)))
in (FStar_ToSMT_Term.mkLTE _118_1174))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1175))
in (quant xy _118_1176))
in (FStar_Absyn_Const.op_LTE, _118_1177))
in (let _118_1296 = (let _118_1295 = (let _118_1186 = (let _118_1185 = (let _118_1184 = (let _118_1183 = (let _118_1182 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1181 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1182, _118_1181)))
in (FStar_ToSMT_Term.mkGT _118_1183))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1184))
in (quant xy _118_1185))
in (FStar_Absyn_Const.op_GT, _118_1186))
in (let _118_1294 = (let _118_1293 = (let _118_1195 = (let _118_1194 = (let _118_1193 = (let _118_1192 = (let _118_1191 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1190 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1191, _118_1190)))
in (FStar_ToSMT_Term.mkGTE _118_1192))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1193))
in (quant xy _118_1194))
in (FStar_Absyn_Const.op_GTE, _118_1195))
in (let _118_1292 = (let _118_1291 = (let _118_1204 = (let _118_1203 = (let _118_1202 = (let _118_1201 = (let _118_1200 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1199 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1200, _118_1199)))
in (FStar_ToSMT_Term.mkSub _118_1201))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1202))
in (quant xy _118_1203))
in (FStar_Absyn_Const.op_Subtraction, _118_1204))
in (let _118_1290 = (let _118_1289 = (let _118_1211 = (let _118_1210 = (let _118_1209 = (let _118_1208 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _118_1208))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1209))
in (quant qx _118_1210))
in (FStar_Absyn_Const.op_Minus, _118_1211))
in (let _118_1288 = (let _118_1287 = (let _118_1220 = (let _118_1219 = (let _118_1218 = (let _118_1217 = (let _118_1216 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1215 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1216, _118_1215)))
in (FStar_ToSMT_Term.mkAdd _118_1217))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1218))
in (quant xy _118_1219))
in (FStar_Absyn_Const.op_Addition, _118_1220))
in (let _118_1286 = (let _118_1285 = (let _118_1229 = (let _118_1228 = (let _118_1227 = (let _118_1226 = (let _118_1225 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1224 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1225, _118_1224)))
in (FStar_ToSMT_Term.mkMul _118_1226))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1227))
in (quant xy _118_1228))
in (FStar_Absyn_Const.op_Multiply, _118_1229))
in (let _118_1284 = (let _118_1283 = (let _118_1238 = (let _118_1237 = (let _118_1236 = (let _118_1235 = (let _118_1234 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1233 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1234, _118_1233)))
in (FStar_ToSMT_Term.mkDiv _118_1235))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1236))
in (quant xy _118_1237))
in (FStar_Absyn_Const.op_Division, _118_1238))
in (let _118_1282 = (let _118_1281 = (let _118_1247 = (let _118_1246 = (let _118_1245 = (let _118_1244 = (let _118_1243 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1242 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1243, _118_1242)))
in (FStar_ToSMT_Term.mkMod _118_1244))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1245))
in (quant xy _118_1246))
in (FStar_Absyn_Const.op_Modulus, _118_1247))
in (let _118_1280 = (let _118_1279 = (let _118_1256 = (let _118_1255 = (let _118_1254 = (let _118_1253 = (let _118_1252 = (FStar_ToSMT_Term.unboxBool x)
in (let _118_1251 = (FStar_ToSMT_Term.unboxBool y)
in (_118_1252, _118_1251)))
in (FStar_ToSMT_Term.mkAnd _118_1253))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1254))
in (quant xy _118_1255))
in (FStar_Absyn_Const.op_And, _118_1256))
in (let _118_1278 = (let _118_1277 = (let _118_1265 = (let _118_1264 = (let _118_1263 = (let _118_1262 = (let _118_1261 = (FStar_ToSMT_Term.unboxBool x)
in (let _118_1260 = (FStar_ToSMT_Term.unboxBool y)
in (_118_1261, _118_1260)))
in (FStar_ToSMT_Term.mkOr _118_1262))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1263))
in (quant xy _118_1264))
in (FStar_Absyn_Const.op_Or, _118_1265))
in (let _118_1276 = (let _118_1275 = (let _118_1272 = (let _118_1271 = (let _118_1270 = (let _118_1269 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _118_1269))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1270))
in (quant qx _118_1271))
in (FStar_Absyn_Const.op_Negation, _118_1272))
in (_118_1275)::[])
in (_118_1277)::_118_1276))
in (_118_1279)::_118_1278))
in (_118_1281)::_118_1280))
in (_118_1283)::_118_1282))
in (_118_1285)::_118_1284))
in (_118_1287)::_118_1286))
in (_118_1289)::_118_1288))
in (_118_1291)::_118_1290))
in (_118_1293)::_118_1292))
in (_118_1295)::_118_1294))
in (_118_1297)::_118_1296))
in (_118_1299)::_118_1298))
in (_118_1301)::_118_1300))
in (_118_1303)::_118_1302))
in (let mk = (fun l v -> (let _118_1335 = (FStar_All.pipe_right prims (FStar_List.filter (fun _53_2088 -> (match (_53_2088) with
| (l', _53_2087) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end))))
in (FStar_All.pipe_right _118_1335 (FStar_List.collect (fun _53_2092 -> (match (_53_2092) with
| (_53_2090, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _53_2098 -> (match (_53_2098) with
| (l', _53_2097) -> begin
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
in (let mk_unit = (fun _53_2104 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _118_1367 = (let _118_1358 = (let _118_1357 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_118_1357, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_118_1358))
in (let _118_1366 = (let _118_1365 = (let _118_1364 = (let _118_1363 = (let _118_1362 = (let _118_1361 = (let _118_1360 = (let _118_1359 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _118_1359))
in (FStar_ToSMT_Term.mkImp _118_1360))
in (((typing_pred)::[])::[], (xx)::[], _118_1361))
in (mkForall_fuel _118_1362))
in (_118_1363, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_118_1364))
in (_118_1365)::[])
in (_118_1367)::_118_1366))))
in (let mk_bool = (fun _53_2109 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _118_1388 = (let _118_1377 = (let _118_1376 = (let _118_1375 = (let _118_1374 = (let _118_1373 = (let _118_1372 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _118_1372))
in (FStar_ToSMT_Term.mkImp _118_1373))
in (((typing_pred)::[])::[], (xx)::[], _118_1374))
in (mkForall_fuel _118_1375))
in (_118_1376, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_118_1377))
in (let _118_1387 = (let _118_1386 = (let _118_1385 = (let _118_1384 = (let _118_1383 = (let _118_1382 = (let _118_1379 = (let _118_1378 = (FStar_ToSMT_Term.boxBool b)
in (_118_1378)::[])
in (_118_1379)::[])
in (let _118_1381 = (let _118_1380 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _118_1380 tt))
in (_118_1382, (bb)::[], _118_1381)))
in (FStar_ToSMT_Term.mkForall _118_1383))
in (_118_1384, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_118_1385))
in (_118_1386)::[])
in (_118_1388)::_118_1387))))))
in (let mk_int = (fun _53_2116 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _118_1400 = (let _118_1399 = (let _118_1398 = (let _118_1397 = (let _118_1396 = (let _118_1395 = (FStar_ToSMT_Term.boxInt a)
in (let _118_1394 = (let _118_1393 = (FStar_ToSMT_Term.boxInt b)
in (_118_1393)::[])
in (_118_1395)::_118_1394))
in (tt)::_118_1396)
in (tt)::_118_1397)
in ("Prims.Precedes", _118_1398))
in (FStar_ToSMT_Term.mkApp _118_1399))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _118_1400))
in (let precedes_y_x = (let _118_1401 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _118_1401))
in (let _118_1443 = (let _118_1407 = (let _118_1406 = (let _118_1405 = (let _118_1404 = (let _118_1403 = (let _118_1402 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _118_1402))
in (FStar_ToSMT_Term.mkImp _118_1403))
in (((typing_pred)::[])::[], (xx)::[], _118_1404))
in (mkForall_fuel _118_1405))
in (_118_1406, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_118_1407))
in (let _118_1442 = (let _118_1441 = (let _118_1415 = (let _118_1414 = (let _118_1413 = (let _118_1412 = (let _118_1409 = (let _118_1408 = (FStar_ToSMT_Term.boxInt b)
in (_118_1408)::[])
in (_118_1409)::[])
in (let _118_1411 = (let _118_1410 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _118_1410 tt))
in (_118_1412, (bb)::[], _118_1411)))
in (FStar_ToSMT_Term.mkForall _118_1413))
in (_118_1414, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_118_1415))
in (let _118_1440 = (let _118_1439 = (let _118_1438 = (let _118_1437 = (let _118_1436 = (let _118_1435 = (let _118_1434 = (let _118_1433 = (let _118_1432 = (let _118_1431 = (let _118_1430 = (let _118_1429 = (let _118_1418 = (let _118_1417 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1416 = (FStar_ToSMT_Term.mkInteger' 0)
in (_118_1417, _118_1416)))
in (FStar_ToSMT_Term.mkGT _118_1418))
in (let _118_1428 = (let _118_1427 = (let _118_1421 = (let _118_1420 = (FStar_ToSMT_Term.unboxInt y)
in (let _118_1419 = (FStar_ToSMT_Term.mkInteger' 0)
in (_118_1420, _118_1419)))
in (FStar_ToSMT_Term.mkGTE _118_1421))
in (let _118_1426 = (let _118_1425 = (let _118_1424 = (let _118_1423 = (FStar_ToSMT_Term.unboxInt y)
in (let _118_1422 = (FStar_ToSMT_Term.unboxInt x)
in (_118_1423, _118_1422)))
in (FStar_ToSMT_Term.mkLT _118_1424))
in (_118_1425)::[])
in (_118_1427)::_118_1426))
in (_118_1429)::_118_1428))
in (typing_pred_y)::_118_1430)
in (typing_pred)::_118_1431)
in (FStar_ToSMT_Term.mk_and_l _118_1432))
in (_118_1433, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _118_1434))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _118_1435))
in (mkForall_fuel _118_1436))
in (_118_1437, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_118_1438))
in (_118_1439)::[])
in (_118_1441)::_118_1440))
in (_118_1443)::_118_1442)))))))))))
in (let mk_int_alias = (fun _53_2128 tt -> (let _118_1452 = (let _118_1451 = (let _118_1450 = (let _118_1449 = (let _118_1448 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Absyn_Syntax.str, []))
in (tt, _118_1448))
in (FStar_ToSMT_Term.mkEq _118_1449))
in (_118_1450, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_118_1451))
in (_118_1452)::[]))
in (let mk_str = (fun _53_2132 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _118_1473 = (let _118_1462 = (let _118_1461 = (let _118_1460 = (let _118_1459 = (let _118_1458 = (let _118_1457 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _118_1457))
in (FStar_ToSMT_Term.mkImp _118_1458))
in (((typing_pred)::[])::[], (xx)::[], _118_1459))
in (mkForall_fuel _118_1460))
in (_118_1461, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_118_1462))
in (let _118_1472 = (let _118_1471 = (let _118_1470 = (let _118_1469 = (let _118_1468 = (let _118_1467 = (let _118_1464 = (let _118_1463 = (FStar_ToSMT_Term.boxString b)
in (_118_1463)::[])
in (_118_1464)::[])
in (let _118_1466 = (let _118_1465 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _118_1465 tt))
in (_118_1467, (bb)::[], _118_1466)))
in (FStar_ToSMT_Term.mkForall _118_1468))
in (_118_1469, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_118_1470))
in (_118_1471)::[])
in (_118_1473)::_118_1472))))))
in (let mk_ref = (fun reft_name _53_2140 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _118_1480 = (let _118_1479 = (let _118_1478 = (FStar_ToSMT_Term.mkFreeV aa)
in (_118_1478)::[])
in (reft_name, _118_1479))
in (FStar_ToSMT_Term.mkApp _118_1480))
in (let refb = (let _118_1483 = (let _118_1482 = (let _118_1481 = (FStar_ToSMT_Term.mkFreeV bb)
in (_118_1481)::[])
in (reft_name, _118_1482))
in (FStar_ToSMT_Term.mkApp _118_1483))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _118_1502 = (let _118_1489 = (let _118_1488 = (let _118_1487 = (let _118_1486 = (let _118_1485 = (let _118_1484 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _118_1484))
in (FStar_ToSMT_Term.mkImp _118_1485))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _118_1486))
in (mkForall_fuel _118_1487))
in (_118_1488, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_118_1489))
in (let _118_1501 = (let _118_1500 = (let _118_1499 = (let _118_1498 = (let _118_1497 = (let _118_1496 = (let _118_1495 = (let _118_1494 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _118_1493 = (let _118_1492 = (let _118_1491 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _118_1490 = (FStar_ToSMT_Term.mkFreeV bb)
in (_118_1491, _118_1490)))
in (FStar_ToSMT_Term.mkEq _118_1492))
in (_118_1494, _118_1493)))
in (FStar_ToSMT_Term.mkImp _118_1495))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _118_1496))
in (mkForall_fuel' 2 _118_1497))
in (_118_1498, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_118_1499))
in (_118_1500)::[])
in (_118_1502)::_118_1501))))))))))
in (let mk_false_interp = (fun _53_2150 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _118_1509 = (let _118_1508 = (let _118_1507 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_118_1507, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_118_1508))
in (_118_1509)::[])))
in (let mk_and_interp = (fun conj _53_2156 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1516 = (let _118_1515 = (let _118_1514 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_118_1514)::[])
in ("Valid", _118_1515))
in (FStar_ToSMT_Term.mkApp _118_1516))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1523 = (let _118_1522 = (let _118_1521 = (let _118_1520 = (let _118_1519 = (let _118_1518 = (let _118_1517 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_118_1517, valid))
in (FStar_ToSMT_Term.mkIff _118_1518))
in (((valid)::[])::[], (aa)::(bb)::[], _118_1519))
in (FStar_ToSMT_Term.mkForall _118_1520))
in (_118_1521, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_118_1522))
in (_118_1523)::[])))))))))
in (let mk_or_interp = (fun disj _53_2167 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1530 = (let _118_1529 = (let _118_1528 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_118_1528)::[])
in ("Valid", _118_1529))
in (FStar_ToSMT_Term.mkApp _118_1530))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1537 = (let _118_1536 = (let _118_1535 = (let _118_1534 = (let _118_1533 = (let _118_1532 = (let _118_1531 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_118_1531, valid))
in (FStar_ToSMT_Term.mkIff _118_1532))
in (((valid)::[])::[], (aa)::(bb)::[], _118_1533))
in (FStar_ToSMT_Term.mkForall _118_1534))
in (_118_1535, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_118_1536))
in (_118_1537)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _118_1544 = (let _118_1543 = (let _118_1542 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_118_1542)::[])
in ("Valid", _118_1543))
in (FStar_ToSMT_Term.mkApp _118_1544))
in (let _118_1551 = (let _118_1550 = (let _118_1549 = (let _118_1548 = (let _118_1547 = (let _118_1546 = (let _118_1545 = (FStar_ToSMT_Term.mkEq (x, y))
in (_118_1545, valid))
in (FStar_ToSMT_Term.mkIff _118_1546))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _118_1547))
in (FStar_ToSMT_Term.mkForall _118_1548))
in (_118_1549, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_118_1550))
in (_118_1551)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1558 = (let _118_1557 = (let _118_1556 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_118_1556)::[])
in ("Valid", _118_1557))
in (FStar_ToSMT_Term.mkApp _118_1558))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1565 = (let _118_1564 = (let _118_1563 = (let _118_1562 = (let _118_1561 = (let _118_1560 = (let _118_1559 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_118_1559, valid))
in (FStar_ToSMT_Term.mkIff _118_1560))
in (((valid)::[])::[], (aa)::(bb)::[], _118_1561))
in (FStar_ToSMT_Term.mkForall _118_1562))
in (_118_1563, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_118_1564))
in (_118_1565)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1572 = (let _118_1571 = (let _118_1570 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_118_1570)::[])
in ("Valid", _118_1571))
in (FStar_ToSMT_Term.mkApp _118_1572))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1579 = (let _118_1578 = (let _118_1577 = (let _118_1576 = (let _118_1575 = (let _118_1574 = (let _118_1573 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_118_1573, valid))
in (FStar_ToSMT_Term.mkIff _118_1574))
in (((valid)::[])::[], (aa)::(bb)::[], _118_1575))
in (FStar_ToSMT_Term.mkForall _118_1576))
in (_118_1577, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_118_1578))
in (_118_1579)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _118_1586 = (let _118_1585 = (let _118_1584 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_118_1584)::[])
in ("Valid", _118_1585))
in (FStar_ToSMT_Term.mkApp _118_1586))
in (let valid_b_x = (let _118_1589 = (let _118_1588 = (let _118_1587 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_118_1587)::[])
in ("Valid", _118_1588))
in (FStar_ToSMT_Term.mkApp _118_1589))
in (let _118_1603 = (let _118_1602 = (let _118_1601 = (let _118_1600 = (let _118_1599 = (let _118_1598 = (let _118_1597 = (let _118_1596 = (let _118_1595 = (let _118_1591 = (let _118_1590 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1590)::[])
in (_118_1591)::[])
in (let _118_1594 = (let _118_1593 = (let _118_1592 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1592, valid_b_x))
in (FStar_ToSMT_Term.mkImp _118_1593))
in (_118_1595, (xx)::[], _118_1594)))
in (FStar_ToSMT_Term.mkForall _118_1596))
in (_118_1597, valid))
in (FStar_ToSMT_Term.mkIff _118_1598))
in (((valid)::[])::[], (aa)::(bb)::[], _118_1599))
in (FStar_ToSMT_Term.mkForall _118_1600))
in (_118_1601, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_118_1602))
in (_118_1603)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _118_1610 = (let _118_1609 = (let _118_1608 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_118_1608)::[])
in ("Valid", _118_1609))
in (FStar_ToSMT_Term.mkApp _118_1610))
in (let valid_b_x = (let _118_1613 = (let _118_1612 = (let _118_1611 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_118_1611)::[])
in ("Valid", _118_1612))
in (FStar_ToSMT_Term.mkApp _118_1613))
in (let _118_1627 = (let _118_1626 = (let _118_1625 = (let _118_1624 = (let _118_1623 = (let _118_1622 = (let _118_1621 = (let _118_1620 = (let _118_1619 = (let _118_1615 = (let _118_1614 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1614)::[])
in (_118_1615)::[])
in (let _118_1618 = (let _118_1617 = (let _118_1616 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1616, valid_b_x))
in (FStar_ToSMT_Term.mkImp _118_1617))
in (_118_1619, (xx)::[], _118_1618)))
in (FStar_ToSMT_Term.mkExists _118_1620))
in (_118_1621, valid))
in (FStar_ToSMT_Term.mkIff _118_1622))
in (((valid)::[])::[], (aa)::(bb)::[], _118_1623))
in (FStar_ToSMT_Term.mkForall _118_1624))
in (_118_1625, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_118_1626))
in (_118_1627)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1634 = (let _118_1633 = (let _118_1632 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_118_1632)::[])
in ("Valid", _118_1633))
in (FStar_ToSMT_Term.mkApp _118_1634))
in (let valid_a_b = (let _118_1637 = (let _118_1636 = (let _118_1635 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_118_1635)::[])
in ("Valid", _118_1636))
in (FStar_ToSMT_Term.mkApp _118_1637))
in (let _118_1651 = (let _118_1650 = (let _118_1649 = (let _118_1648 = (let _118_1647 = (let _118_1646 = (let _118_1645 = (let _118_1644 = (let _118_1643 = (let _118_1639 = (let _118_1638 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1638)::[])
in (_118_1639)::[])
in (let _118_1642 = (let _118_1641 = (let _118_1640 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1640, valid_a_b))
in (FStar_ToSMT_Term.mkImp _118_1641))
in (_118_1643, (bb)::[], _118_1642)))
in (FStar_ToSMT_Term.mkForall _118_1644))
in (_118_1645, valid))
in (FStar_ToSMT_Term.mkIff _118_1646))
in (((valid)::[])::[], (kk)::(aa)::[], _118_1647))
in (FStar_ToSMT_Term.mkForall _118_1648))
in (_118_1649, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_118_1650))
in (_118_1651)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1658 = (let _118_1657 = (let _118_1656 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_118_1656)::[])
in ("Valid", _118_1657))
in (FStar_ToSMT_Term.mkApp _118_1658))
in (let valid_a_b = (let _118_1661 = (let _118_1660 = (let _118_1659 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_118_1659)::[])
in ("Valid", _118_1660))
in (FStar_ToSMT_Term.mkApp _118_1661))
in (let _118_1675 = (let _118_1674 = (let _118_1673 = (let _118_1672 = (let _118_1671 = (let _118_1670 = (let _118_1669 = (let _118_1668 = (let _118_1667 = (let _118_1663 = (let _118_1662 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1662)::[])
in (_118_1663)::[])
in (let _118_1666 = (let _118_1665 = (let _118_1664 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1664, valid_a_b))
in (FStar_ToSMT_Term.mkImp _118_1665))
in (_118_1667, (bb)::[], _118_1666)))
in (FStar_ToSMT_Term.mkExists _118_1668))
in (_118_1669, valid))
in (FStar_ToSMT_Term.mkIff _118_1670))
in (((valid)::[])::[], (kk)::(aa)::[], _118_1671))
in (FStar_ToSMT_Term.mkForall _118_1672))
in (_118_1673, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_118_1674))
in (_118_1675)::[]))))))))))
in (let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _53_2260 -> (match (_53_2260) with
| (l, _53_2259) -> begin
(FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_53_2263, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun env se -> (let _53_2269 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _118_1818 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.fprint1 ">>>>Encoding [%s]\n") _118_1818))
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
in (let _53_2277 = (encode_sigelt' env se)
in (match (_53_2277) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _118_1821 = (let _118_1820 = (let _118_1819 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_118_1819))
in (_118_1820)::[])
in (_118_1821, e))
end
| _53_2280 -> begin
(let _118_1828 = (let _118_1827 = (let _118_1823 = (let _118_1822 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_118_1822))
in (_118_1823)::g)
in (let _118_1826 = (let _118_1825 = (let _118_1824 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_118_1824))
in (_118_1825)::[])
in (FStar_List.append _118_1827 _118_1826)))
in (_118_1828, e))
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.all_")))
in (let encode_top_level_val = (fun env lid t quals -> (let tt = (whnf env t)
in (let _53_2293 = (encode_free_var env lid t tt quals)
in (match (_53_2293) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _118_1842 = (let _118_1841 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _118_1841))
in (_118_1842, env))
end else begin
(decls, env)
end
end))))
in (let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2300 lb -> (match (_53_2300) with
| (decls, env) -> begin
(let _53_2304 = (let _118_1851 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _118_1851 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_53_2304) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_53_2306, _53_2308, _53_2310, _53_2312, FStar_Absyn_Syntax.Effect::[], _53_2316) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2321, _53_2323, _53_2325, _53_2327, _53_2329) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2334, _53_2336, _53_2338, _53_2340, _53_2342) when (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(let _53_2348 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2348) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _118_1854 = (let _118_1853 = (let _118_1852 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_118_1852)::[])
in ("Valid", _118_1853))
in (FStar_ToSMT_Term.mkApp _118_1854))
in (let decls = (let _118_1862 = (let _118_1861 = (let _118_1860 = (let _118_1859 = (let _118_1858 = (let _118_1857 = (let _118_1856 = (let _118_1855 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _118_1855))
in (FStar_ToSMT_Term.mkEq _118_1856))
in (((valid_b2t_x)::[])::[], (xx)::[], _118_1857))
in (FStar_ToSMT_Term.mkForall _118_1858))
in (_118_1859, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_118_1860))
in (_118_1861)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_118_1862)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _53_2356, t, tags, _53_2360) -> begin
(let _53_2366 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2366) with
| (tname, ttok, env) -> begin
(let _53_2375 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _53_2372 -> begin
(tps, t)
end)
in (match (_53_2375) with
| (tps, t) -> begin
(let _53_2382 = (encode_binders None tps env)
in (match (_53_2382) with
| (vars, guards, env', binder_decls, _53_2381) -> begin
(let tok_app = (let _118_1863 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _118_1863 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _118_1865 = (let _118_1864 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _118_1864))
in (FStar_ToSMT_Term.mkApp _118_1865))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _53_2388 -> begin
(let _118_1867 = (let _118_1866 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _118_1866))
in (_118_1867)::[])
end)
in (let decls = (let _118_1878 = (let _118_1871 = (let _118_1870 = (let _118_1869 = (let _118_1868 = (FStar_List.map Prims.snd vars)
in (tname, _118_1868, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_1869))
in (_118_1870)::(tok_decl)::[])
in (FStar_List.append _118_1871 fresh_tok))
in (let _118_1877 = (let _118_1876 = (let _118_1875 = (let _118_1874 = (let _118_1873 = (let _118_1872 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _118_1872))
in (FStar_ToSMT_Term.mkForall _118_1873))
in (_118_1874, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_118_1875))
in (_118_1876)::[])
in (FStar_List.append _118_1878 _118_1877)))
in (let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (let _53_2400 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _53_18 -> (match (_53_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2395 -> begin
false
end)))) then begin
(let _118_1881 = (FStar_ToSMT_Term.mk_Valid app)
in (let _118_1880 = (encode_formula t env')
in (_118_1881, _118_1880)))
end else begin
(let _118_1882 = (encode_typ_term t env')
in (app, _118_1882))
end
in (match (_53_2400) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _118_1889 = (let _118_1888 = (let _118_1887 = (let _118_1886 = (let _118_1885 = (let _118_1884 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_1883 = (FStar_ToSMT_Term.mkEq (def, body))
in (_118_1884, _118_1883)))
in (FStar_ToSMT_Term.mkImp _118_1885))
in (((def)::[])::[], vars, _118_1886))
in (FStar_ToSMT_Term.mkForall _118_1887))
in (_118_1888, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_118_1889))
in (let kindingAx = (let _53_2404 = (let _118_1890 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _118_1890 env' app))
in (match (_53_2404) with
| (k, decls) -> begin
(let _118_1898 = (let _118_1897 = (let _118_1896 = (let _118_1895 = (let _118_1894 = (let _118_1893 = (let _118_1892 = (let _118_1891 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_1891, k))
in (FStar_ToSMT_Term.mkImp _118_1892))
in (((app)::[])::[], vars, _118_1893))
in (FStar_ToSMT_Term.mkForall _118_1894))
in (_118_1895, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_118_1896))
in (_118_1897)::[])
in (FStar_List.append decls _118_1898))
end))
in (let g = (let _118_1899 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _118_1899))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _53_2411) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _53_2417, _53_2419) -> begin
(let _53_2424 = (encode_formula f env)
in (match (_53_2424) with
| (f, decls) -> begin
(let g = (let _118_1904 = (let _118_1903 = (let _118_1902 = (let _118_1901 = (let _118_1900 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _118_1900))
in Some (_118_1901))
in (f, _118_1902))
in FStar_ToSMT_Term.Assume (_118_1903))
in (_118_1904)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2430, datas, quals, _53_2434) when (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(let _53_2440 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2440) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _53_2443, _53_2445, _53_2447, _53_2449, _53_2451, _53_2453) when ((FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.FStar_Absyn_Syntax.str
in (let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _118_1906 = (let _118_1905 = (primitive_type_axioms t tname tsym)
in (decl)::_118_1905)
in (_118_1906, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2463, datas, quals, _53_2467) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_19 -> (match (_53_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _53_2474 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _53_2484 = c
in (match (_53_2484) with
| (name, args, _53_2481, _53_2483) -> begin
(let _118_1912 = (let _118_1911 = (let _118_1910 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _118_1910, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_1911))
in (_118_1912)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _118_1918 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _118_1918 FStar_Option.isNone)))))) then begin
[]
end else begin
(let _53_2491 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2491) with
| (xxsym, xx) -> begin
(let _53_2534 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _53_2494 l -> (match (_53_2494) with
| (out, decls) -> begin
(let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _53_2504 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_53_2504) with
| (args, res) -> begin
(let indices = (match ((let _118_1921 = (FStar_Absyn_Util.compress_typ res)
in _118_1921.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_53_2506, indices) -> begin
indices
end
| _53_2511 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _118_1926 = (let _118_1925 = (let _118_1924 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_118_1924, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _118_1925))
in (push_typ_var env a.FStar_Absyn_Syntax.v _118_1926))
end
| FStar_Util.Inr (x) -> begin
(let _118_1929 = (let _118_1928 = (let _118_1927 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_118_1927, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _118_1928))
in (push_term_var env x.FStar_Absyn_Syntax.v _118_1929))
end)) env))
in (let _53_2522 = (encode_args indices env)
in (match (_53_2522) with
| (indices, decls') -> begin
(let _53_2523 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (let eqs = (let _118_1936 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _118_1933 = (let _118_1932 = (FStar_ToSMT_Term.mkFreeV v)
in (_118_1932, a))
in (FStar_ToSMT_Term.mkEq _118_1933))
end
| FStar_Util.Inr (a) -> begin
(let _118_1935 = (let _118_1934 = (FStar_ToSMT_Term.mkFreeV v)
in (_118_1934, a))
in (FStar_ToSMT_Term.mkEq _118_1935))
end)) vars indices)
in (FStar_All.pipe_right _118_1936 FStar_ToSMT_Term.mk_and_l))
in (let _118_1941 = (let _118_1940 = (let _118_1939 = (let _118_1938 = (let _118_1937 = (mk_data_tester env l xx)
in (_118_1937, eqs))
in (FStar_ToSMT_Term.mkAnd _118_1938))
in (out, _118_1939))
in (FStar_ToSMT_Term.mkOr _118_1940))
in (_118_1941, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_53_2534) with
| (data_ax, decls) -> begin
(let _53_2537 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2537) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _118_1942 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _118_1942 xx tapp))
in (let _118_1949 = (let _118_1948 = (let _118_1947 = (let _118_1946 = (let _118_1945 = (let _118_1944 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _118_1943 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _118_1944, _118_1943)))
in (FStar_ToSMT_Term.mkForall _118_1945))
in (_118_1946, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_118_1947))
in (_118_1948)::[])
in (FStar_List.append decls _118_1949)))
end))
end))
end))
end)
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _53_2549 = (match ((let _118_1950 = (FStar_Absyn_Util.compress_kind k)
in _118_1950.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _53_2545 -> begin
(false, [], k)
end)
in (match (_53_2549) with
| (is_kind_arrow, formals, res) -> begin
(let _53_2556 = (encode_binders None formals env)
in (match (_53_2556) with
| (vars, guards, env', binder_decls, _53_2555) -> begin
(let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _53_20 -> (match (_53_20) with
| FStar_Absyn_Syntax.Projector (_53_2562) -> begin
true
end
| _53_2565 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _53_21 -> (match (_53_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_53_2580) -> begin
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
in (let _53_2595 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_53_2586, xx::suffix) -> begin
(xx, suffix)
end
| _53_2592 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_2595) with
| (xx, suffix) -> begin
(let dproj_app = (let _118_1964 = (let _118_1963 = (let _118_1962 = (mk_typ_projector_name d a)
in (let _118_1961 = (let _118_1960 = (FStar_ToSMT_Term.mkFreeV xx)
in (_118_1960)::[])
in (_118_1962, _118_1961)))
in (FStar_ToSMT_Term.mkApp _118_1963))
in (mk_ApplyT _118_1964 suffix))
in (let _118_1969 = (let _118_1968 = (let _118_1967 = (let _118_1966 = (let _118_1965 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _118_1965))
in (FStar_ToSMT_Term.mkForall _118_1966))
in (_118_1967, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_118_1968))
in (_118_1969)::[]))
end))))
end
| _53_2598 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _53_2604 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2604) with
| (xxsym, xx) -> begin
(let _53_2607 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2607) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _118_1982 = (let _118_1981 = (let _118_1980 = (let _118_1979 = (let _118_1978 = (let _118_1977 = (let _118_1976 = (let _118_1975 = (let _118_1974 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _118_1974))
in (FStar_ToSMT_Term.mkEq _118_1975))
in (xx_has_type, _118_1976))
in (FStar_ToSMT_Term.mkImp _118_1977))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _118_1978))
in (FStar_ToSMT_Term.mkForall _118_1979))
in (_118_1980, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_118_1981))
in (_118_1982)::[]))
end))
end)))
in (let _53_2612 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2612) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _118_1984 = (let _118_1983 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _118_1983))
in (FStar_ToSMT_Term.mkApp _118_1984))
in (let _53_2637 = (let tname_decl = (let _118_1988 = (let _118_1987 = (FStar_All.pipe_right vars (FStar_List.map (fun _53_2618 -> (match (_53_2618) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _118_1986 = (varops.next_id ())
in (tname, _118_1987, FStar_ToSMT_Term.Type_sort, _118_1986)))
in (constructor_or_logic_type_decl _118_1988))
in (let _53_2634 = (match (vars) with
| [] -> begin
(let _118_1992 = (let _118_1991 = (let _118_1990 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _118_1989 -> Some (_118_1989)) _118_1990))
in (push_free_tvar env t tname _118_1991))
in ([], _118_1992))
end
| _53_2622 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _118_1993 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _118_1993))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = if ((not (is_logical)) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_22 -> (match (_53_22) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2629 -> begin
false
end))))) then begin
((ttok_app)::[])::((tapp)::[])::[]
end else begin
((ttok_app)::[])::[]
end
in (let name_tok_corr = (let _118_1998 = (let _118_1997 = (let _118_1996 = (let _118_1995 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _118_1995))
in (FStar_ToSMT_Term.mkForall' _118_1996))
in (_118_1997, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_118_1998))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_53_2634) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_53_2637) with
| (decls, env) -> begin
(let kindingAx = (let _53_2640 = (encode_knd res env' tapp)
in (match (_53_2640) with
| (k, decls) -> begin
(let karr = if is_kind_arrow then begin
(let _118_2002 = (let _118_2001 = (let _118_2000 = (let _118_1999 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_1999))
in (_118_2000, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_118_2001))
in (_118_2002)::[])
end else begin
[]
end
in (let _118_2008 = (let _118_2007 = (let _118_2006 = (let _118_2005 = (let _118_2004 = (let _118_2003 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _118_2003))
in (FStar_ToSMT_Term.mkForall _118_2004))
in (_118_2005, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_118_2006))
in (_118_2007)::[])
in (FStar_List.append (FStar_List.append decls karr) _118_2008)))
end))
in (let aux = if is_logical then begin
(let _118_2009 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _118_2009))
end else begin
(let _118_2016 = (let _118_2014 = (let _118_2012 = (let _118_2010 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _118_2010))
in (let _118_2011 = (inversion_axioms tapp vars)
in (FStar_List.append _118_2012 _118_2011)))
in (let _118_2013 = (projection_axioms tapp vars)
in (FStar_List.append _118_2014 _118_2013)))
in (let _118_2015 = (pretype_axioms tapp vars)
in (FStar_List.append _118_2016 _118_2015)))
end
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _53_2647, _53_2649, _53_2651, _53_2653, _53_2655) when (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_53_2661, tps, _53_2664), quals, _53_2668, drange) -> begin
(let t = (let _118_2018 = (FStar_List.map (fun _53_2675 -> (match (_53_2675) with
| (x, _53_2674) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _118_2018 t))
in (let _53_2680 = (new_term_constant_and_tok_from_lid env d)
in (match (_53_2680) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _53_2689 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_53_2689) with
| (formals, t_res) -> begin
(let _53_2692 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2692) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _53_2699 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2699) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _53_23 -> (match (_53_23) with
| FStar_Util.Inl (a) -> begin
(let _118_2020 = (mk_typ_projector_name d a)
in (_118_2020, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _118_2021 = (mk_term_projector_name d x)
in (_118_2021, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _118_2023 = (let _118_2022 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _118_2022))
in (FStar_All.pipe_right _118_2023 FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _53_2713 = (encode_typ_pred None t env ddtok_tm)
in (match (_53_2713) with
| (tok_typing, decls3) -> begin
(let _53_2720 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2720) with
| (vars', guards', env'', decls_formals, _53_2719) -> begin
(let _53_2725 = (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_53_2725) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _53_2729 -> begin
(let _118_2025 = (let _118_2024 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _118_2024))
in (_118_2025)::[])
end)
in (let encode_elim = (fun _53_2732 -> (match (()) with
| () -> begin
(let _53_2735 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_53_2735) with
| (head, args) -> begin
(match ((let _118_2028 = (FStar_Absyn_Util.compress_typ head)
in _118_2028.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _53_2741 = (encode_args args env')
in (match (_53_2741) with
| (encoded_args, arg_decls) -> begin
(let _53_2765 = (FStar_List.fold_left (fun _53_2745 arg -> (match (_53_2745) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _53_2753 = (let _118_2031 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _118_2031))
in (match (_53_2753) with
| (_53_2750, tv, env) -> begin
(let _118_2033 = (let _118_2032 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_118_2032)::eqns)
in (env, (tv)::arg_vars, _118_2033))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _53_2760 = (let _118_2034 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _118_2034))
in (match (_53_2760) with
| (_53_2757, xv, env) -> begin
(let _118_2036 = (let _118_2035 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_118_2035)::eqns)
in (env, (xv)::arg_vars, _118_2036))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_53_2765) with
| (_53_2762, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _118_2043 = (let _118_2042 = (let _118_2041 = (let _118_2040 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _118_2039 = (let _118_2038 = (let _118_2037 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _118_2037))
in (FStar_ToSMT_Term.mkImp _118_2038))
in (((ty_pred)::[])::[], _118_2040, _118_2039)))
in (FStar_ToSMT_Term.mkForall _118_2041))
in (_118_2042, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_118_2043))
in (let subterm_ordering = if (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(let x = (let _118_2044 = (varops.fresh "x")
in (_118_2044, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _118_2054 = (let _118_2053 = (let _118_2052 = (let _118_2051 = (let _118_2046 = (let _118_2045 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_118_2045)::[])
in (_118_2046)::[])
in (let _118_2050 = (let _118_2049 = (let _118_2048 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _118_2047 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_118_2048, _118_2047)))
in (FStar_ToSMT_Term.mkImp _118_2049))
in (_118_2051, (x)::[], _118_2050)))
in (FStar_ToSMT_Term.mkForall _118_2052))
in (_118_2053, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_118_2054))))
end else begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _118_2057 = (let _118_2056 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _118_2056 dapp))
in (_118_2057)::[])
end
| _53_2780 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _118_2064 = (let _118_2063 = (let _118_2062 = (let _118_2061 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _118_2060 = (let _118_2059 = (let _118_2058 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _118_2058))
in (FStar_ToSMT_Term.mkImp _118_2059))
in (((ty_pred)::[])::[], _118_2061, _118_2060)))
in (FStar_ToSMT_Term.mkForall _118_2062))
in (_118_2063, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_118_2064)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _53_2784 -> begin
(let _53_2785 = (let _118_2067 = (let _118_2066 = (FStar_Absyn_Print.sli d)
in (let _118_2065 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _118_2066 _118_2065)))
in (FStar_Tc_Errors.warn drange _118_2067))
in ([], []))
end)
end))
end))
in (let _53_2789 = (encode_elim ())
in (match (_53_2789) with
| (decls2, elim) -> begin
(let g = (let _118_2092 = (let _118_2091 = (let _118_2076 = (let _118_2075 = (let _118_2074 = (let _118_2073 = (let _118_2072 = (let _118_2071 = (let _118_2070 = (let _118_2069 = (let _118_2068 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _118_2068))
in Some (_118_2069))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _118_2070))
in FStar_ToSMT_Term.DeclFun (_118_2071))
in (_118_2072)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _118_2073))
in (FStar_List.append _118_2074 proxy_fresh))
in (FStar_List.append _118_2075 decls_formals))
in (FStar_List.append _118_2076 decls_pred))
in (let _118_2090 = (let _118_2089 = (let _118_2088 = (let _118_2080 = (let _118_2079 = (let _118_2078 = (let _118_2077 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _118_2077))
in (FStar_ToSMT_Term.mkForall _118_2078))
in (_118_2079, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_118_2080))
in (let _118_2087 = (let _118_2086 = (let _118_2085 = (let _118_2084 = (let _118_2083 = (let _118_2082 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _118_2081 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _118_2082, _118_2081)))
in (FStar_ToSMT_Term.mkForall _118_2083))
in (_118_2084, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_118_2085))
in (_118_2086)::[])
in (_118_2088)::_118_2087))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_118_2089)
in (FStar_List.append _118_2091 _118_2090)))
in (FStar_List.append _118_2092 elim))
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
| FStar_Absyn_Syntax.Sig_bundle (ses, _53_2793, _53_2795, _53_2797) -> begin
(let _53_2802 = (encode_signature env ses)
in (match (_53_2802) with
| (g, env) -> begin
(let _53_2814 = (FStar_All.pipe_right g (FStar_List.partition (fun _53_24 -> (match (_53_24) with
| FStar_ToSMT_Term.Assume (_53_2805, Some ("inversion axiom")) -> begin
false
end
| _53_2811 -> begin
true
end))))
in (match (_53_2814) with
| (g', inversions) -> begin
(let _53_2823 = (FStar_All.pipe_right g' (FStar_List.partition (fun _53_25 -> (match (_53_25) with
| FStar_ToSMT_Term.DeclFun (_53_2817) -> begin
true
end
| _53_2820 -> begin
false
end))))
in (match (_53_2823) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_53_2825, _53_2827, _53_2829, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_26 -> (match (_53_26) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _53_2841 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _53_2846, _53_2848, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _53_2860 = (FStar_Util.first_N nbinders formals)
in (match (_53_2860) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _118_2107 = (let _118_2106 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _118_2106))
in FStar_Util.Inl (_118_2107))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _118_2109 = (let _118_2108 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _118_2108))
in FStar_Util.Inr (_118_2109))
end
| _53_2874 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _118_2110 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _118_2110 FStar_Absyn_Util.name_binders))
in (let body = (let _118_2116 = (let _118_2112 = (let _118_2111 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _118_2111))
in (body, _118_2112))
in (let _118_2115 = (let _118_2114 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _118_2113 -> Some (_118_2113)) _118_2114))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _118_2116 _118_2115 body.FStar_Absyn_Syntax.pos)))
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
(let _53_2912 = (FStar_Util.first_N nformals binders)
in (match (_53_2912) with
| (bs0, rest) -> begin
(let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _53_2916 -> begin
(FStar_All.failwith "impossible")
end)
in (let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(let _53_2921 = (eta_expand binders formals body tres)
in (match (_53_2921) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _53_2923 -> begin
(let _118_2125 = (let _118_2124 = (FStar_Absyn_Print.exp_to_string e)
in (let _118_2123 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Absyn_Syntax.str _118_2124 _118_2123)))
in (FStar_All.failwith _118_2125))
end)
end
| _53_2925 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (FStar_Absyn_Util.comp_result c)
in (let _53_2933 = (eta_expand [] formals e tres)
in (match (_53_2933) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _53_2935 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _53_2937 -> (match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_27 -> (match (_53_27) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2948 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(let _53_2967 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2954 lb -> (match (_53_2954) with
| (toks, typs, decls, env) -> begin
(let _53_2956 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (let t_norm = (let _118_2131 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _118_2131 FStar_Absyn_Util.compress_typ))
in (let _53_2962 = (let _118_2132 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _118_2132 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_53_2962) with
| (tok, decl, env) -> begin
(let _118_2135 = (let _118_2134 = (let _118_2133 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_118_2133, tok))
in (_118_2134)::toks)
in (_118_2135, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_53_2967) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_28 -> (match (_53_28) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _53_2974 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _118_2138 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _118_2138))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _53_2982; FStar_Absyn_Syntax.lbtyp = _53_2980; FStar_Absyn_Syntax.lbeff = _53_2978; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _53_2998 = (destruct_bound_function flid t_norm e)
in (match (_53_2998) with
| (binders, body, formals, tres) -> begin
(let _53_3005 = (encode_binders None binders env)
in (match (_53_3005) with
| (vars, guards, env', binder_decls, _53_3004) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _53_3008 -> begin
(let _118_2140 = (let _118_2139 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _118_2139))
in (FStar_ToSMT_Term.mkApp _118_2140))
end)
in (let _53_3012 = (encode_exp body env')
in (match (_53_3012) with
| (body, decls2) -> begin
(let eqn = (let _118_2149 = (let _118_2148 = (let _118_2145 = (let _118_2144 = (let _118_2143 = (let _118_2142 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_2141 = (FStar_ToSMT_Term.mkEq (app, body))
in (_118_2142, _118_2141)))
in (FStar_ToSMT_Term.mkImp _118_2143))
in (((app)::[])::[], vars, _118_2144))
in (FStar_ToSMT_Term.mkForall _118_2145))
in (let _118_2147 = (let _118_2146 = (FStar_Util.format1 "Equation for %s" flid.FStar_Absyn_Syntax.str)
in Some (_118_2146))
in (_118_2148, _118_2147)))
in FStar_ToSMT_Term.Assume (_118_2149))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _53_3015 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let fuel = (let _118_2150 = (varops.fresh "fuel")
in (_118_2150, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _53_3032 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _53_3021 _53_3026 -> (match ((_53_3021, _53_3026)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _118_2155 = (let _118_2154 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _118_2153 -> Some (_118_2153)) _118_2154))
in (push_free_var env flid gtok _118_2155))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_53_3032) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _53_3041 t_norm _53_3050 -> (match ((_53_3041, _53_3050)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _53_3049; FStar_Absyn_Syntax.lbtyp = _53_3047; FStar_Absyn_Syntax.lbeff = _53_3045; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _53_3055 = (destruct_bound_function flid t_norm e)
in (match (_53_3055) with
| (binders, body, formals, tres) -> begin
(let _53_3062 = (encode_binders None binders env)
in (match (_53_3062) with
| (vars, guards, env', binder_decls, _53_3061) -> begin
(let decl_g = (let _118_2166 = (let _118_2165 = (let _118_2164 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_118_2164)
in (g, _118_2165, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_118_2166))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _118_2169 = (let _118_2168 = (let _118_2167 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_118_2167)::vars_tm)
in (g, _118_2168))
in (FStar_ToSMT_Term.mkApp _118_2169))
in (let gmax = (let _118_2172 = (let _118_2171 = (let _118_2170 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_118_2170)::vars_tm)
in (g, _118_2171))
in (FStar_ToSMT_Term.mkApp _118_2172))
in (let _53_3072 = (encode_exp body env')
in (match (_53_3072) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _118_2181 = (let _118_2180 = (let _118_2177 = (let _118_2176 = (let _118_2175 = (let _118_2174 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_2173 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_118_2174, _118_2173)))
in (FStar_ToSMT_Term.mkImp _118_2175))
in (((gsapp)::[])::[], (fuel)::vars, _118_2176))
in (FStar_ToSMT_Term.mkForall _118_2177))
in (let _118_2179 = (let _118_2178 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Absyn_Syntax.str)
in Some (_118_2178))
in (_118_2180, _118_2179)))
in FStar_ToSMT_Term.Assume (_118_2181))
in (let eqn_f = (let _118_2185 = (let _118_2184 = (let _118_2183 = (let _118_2182 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _118_2182))
in (FStar_ToSMT_Term.mkForall _118_2183))
in (_118_2184, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_118_2185))
in (let eqn_g' = (let _118_2194 = (let _118_2193 = (let _118_2192 = (let _118_2191 = (let _118_2190 = (let _118_2189 = (let _118_2188 = (let _118_2187 = (let _118_2186 = (FStar_ToSMT_Term.n_fuel 0)
in (_118_2186)::vars_tm)
in (g, _118_2187))
in (FStar_ToSMT_Term.mkApp _118_2188))
in (gsapp, _118_2189))
in (FStar_ToSMT_Term.mkEq _118_2190))
in (((gsapp)::[])::[], (fuel)::vars, _118_2191))
in (FStar_ToSMT_Term.mkForall _118_2192))
in (_118_2193, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_118_2194))
in (let _53_3095 = (let _53_3082 = (encode_binders None formals env0)
in (match (_53_3082) with
| (vars, v_guards, env, binder_decls, _53_3081) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _118_2195 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _118_2195 ((fuel)::vars)))
in (let _118_2199 = (let _118_2198 = (let _118_2197 = (let _118_2196 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _118_2196))
in (FStar_ToSMT_Term.mkForall _118_2197))
in (_118_2198, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_118_2199)))
in (let _53_3092 = (let _53_3089 = (encode_typ_pred None tres env gapp)
in (match (_53_3089) with
| (g_typing, d3) -> begin
(let _118_2207 = (let _118_2206 = (let _118_2205 = (let _118_2204 = (let _118_2203 = (let _118_2202 = (let _118_2201 = (let _118_2200 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_118_2200, g_typing))
in (FStar_ToSMT_Term.mkImp _118_2201))
in (((gapp)::[])::[], (fuel)::vars, _118_2202))
in (FStar_ToSMT_Term.mkForall _118_2203))
in (_118_2204, None))
in FStar_ToSMT_Term.Assume (_118_2205))
in (_118_2206)::[])
in (d3, _118_2207))
end))
in (match (_53_3092) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_53_3095) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _53_3111 = (let _118_2210 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _53_3099 _53_3103 -> (match ((_53_3099, _53_3103)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _53_3107 = (encode_one_binding env0 gtok ty bs)
in (match (_53_3107) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _118_2210))
in (match (_53_3111) with
| (decls, eqns, env0) -> begin
(let _53_3120 = (let _118_2212 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _118_2212 (FStar_List.partition (fun _53_29 -> (match (_53_29) with
| FStar_ToSMT_Term.DeclFun (_53_3114) -> begin
true
end
| _53_3117 -> begin
false
end)))))
in (match (_53_3120) with
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
end)) (fun _53_2936 -> (match (_53_2936) with
| Let_rec_unencodeable -> begin
(let msg = (let _118_2215 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _118_2215 (FStar_String.concat " and ")))
in (let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _53_3147 = (encode_free_var env x t t_norm [])
in (match (_53_3147) with
| (decls, env) -> begin
(let _53_3152 = (lookup_lid env x)
in (match (_53_3152) with
| (n, x', _53_3151) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _53_3156) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _53_3164 = (encode_function_type_as_formula None None t env)
in (match (_53_3164) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> if ((let _118_2228 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _118_2228)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(let _53_3173 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3173) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_3176) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _53_30 -> (match (_53_30) with
| (FStar_Util.Inl (_53_3181), _53_3184) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3187 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _53_3189 -> begin
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
in (let _53_3206 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _118_2230 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _118_2230))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_53_3206) with
| (formals, (pre_opt, res_t)) -> begin
(let _53_3210 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3210) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _53_3213 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _53_31 -> (match (_53_31) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _53_3229 = (FStar_Util.prefix vars)
in (match (_53_3229) with
| (_53_3224, (xxsym, _53_3227)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _118_2247 = (let _118_2246 = (let _118_2245 = (let _118_2244 = (let _118_2243 = (let _118_2242 = (let _118_2241 = (let _118_2240 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Absyn_Syntax.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_2240))
in (vapp, _118_2241))
in (FStar_ToSMT_Term.mkEq _118_2242))
in (((vapp)::[])::[], vars, _118_2243))
in (FStar_ToSMT_Term.mkForall _118_2244))
in (_118_2245, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_118_2246))
in (_118_2247)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _53_3242 = (FStar_Util.prefix vars)
in (match (_53_3242) with
| (_53_3237, (xxsym, _53_3240)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _118_2249 = (let _118_2248 = (mk_term_projector_name d f)
in (_118_2248, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _118_2249))
in (let _118_2254 = (let _118_2253 = (let _118_2252 = (let _118_2251 = (let _118_2250 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _118_2250))
in (FStar_ToSMT_Term.mkForall _118_2251))
in (_118_2252, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_118_2253))
in (_118_2254)::[])))
end))
end
| _53_3246 -> begin
[]
end)))))
in (let _53_3253 = (encode_binders None formals env)
in (match (_53_3253) with
| (vars, guards, env', decls1, _53_3252) -> begin
(let _53_3262 = (match (pre_opt) with
| None -> begin
(let _118_2255 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_2255, decls1))
end
| Some (p) -> begin
(let _53_3259 = (encode_formula p env')
in (match (_53_3259) with
| (g, ds) -> begin
(let _118_2256 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_118_2256, (FStar_List.append decls1 ds)))
end))
end)
in (match (_53_3262) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _118_2258 = (let _118_2257 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _118_2257))
in (FStar_ToSMT_Term.mkApp _118_2258))
in (let _53_3293 = (let vname_decl = (let _118_2261 = (let _118_2260 = (FStar_All.pipe_right formals (FStar_List.map (fun _53_32 -> (match (_53_32) with
| (FStar_Util.Inl (_53_3267), _53_3270) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3273 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _118_2260, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_2261))
in (let _53_3280 = (let env = (let _53_3275 = env
in {bindings = _53_3275.bindings; depth = _53_3275.depth; tcenv = _53_3275.tcenv; warn = _53_3275.warn; cache = _53_3275.cache; nolabels = _53_3275.nolabels; use_zfuel_name = _53_3275.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_53_3280) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _53_3290 = (match (formals) with
| [] -> begin
(let _118_2265 = (let _118_2264 = (let _118_2263 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _118_2262 -> Some (_118_2262)) _118_2263))
in (push_free_var env lid vname _118_2264))
in ((FStar_List.append decls2 ((tok_typing)::[])), _118_2265))
end
| _53_3284 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _118_2266 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _118_2266))
in (let name_tok_corr = (let _118_2270 = (let _118_2269 = (let _118_2268 = (let _118_2267 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _118_2267))
in (FStar_ToSMT_Term.mkForall _118_2268))
in (_118_2269, None))
in FStar_ToSMT_Term.Assume (_118_2270))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_53_3290) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_53_3293) with
| (decls2, env) -> begin
(let _53_3301 = (let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (let _53_3297 = (encode_typ_term res_t env')
in (match (_53_3297) with
| (encoded_res_t, decls) -> begin
(let _118_2271 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _118_2271, decls))
end)))
in (match (_53_3301) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _118_2275 = (let _118_2274 = (let _118_2273 = (let _118_2272 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _118_2272))
in (FStar_ToSMT_Term.mkForall _118_2273))
in (_118_2274, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_118_2275))
in (let g = (let _118_2277 = (let _118_2276 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_118_2276)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _118_2277))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _53_3308 se -> (match (_53_3308) with
| (g, env) -> begin
(let _53_3312 = (encode_sigelt env se)
in (match (_53_3312) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _53_3319 -> (match (_53_3319) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _53_3327 = (new_term_constant env x)
in (match (_53_3327) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _53_3329 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _118_2292 = (FStar_Absyn_Print.strBvd x)
in (let _118_2291 = (FStar_Absyn_Print.typ_to_string t0)
in (let _118_2290 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.fprint3 "Normalized %s : %s to %s\n" _118_2292 _118_2291 _118_2290))))
end else begin
()
end
in (let _53_3333 = (encode_typ_pred None t1 env xx)
in (match (_53_3333) with
| (t, decls') -> begin
(let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _118_2296 = (let _118_2295 = (FStar_Absyn_Print.strBvd x)
in (let _118_2294 = (FStar_Absyn_Print.typ_to_string t0)
in (let _118_2293 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _118_2295 _118_2294 _118_2293))))
in Some (_118_2296))
end else begin
None
end
in (let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let _53_3343 = (new_typ_constant env a)
in (match (_53_3343) with
| (aasym, aa, env') -> begin
(let _53_3346 = (encode_knd k env aa)
in (match (_53_3346) with
| (k, decls') -> begin
(let g = (let _118_2302 = (let _118_2301 = (let _118_2300 = (let _118_2299 = (let _118_2298 = (let _118_2297 = (FStar_Absyn_Print.strBvd a)
in Some (_118_2297))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _118_2298))
in FStar_ToSMT_Term.DeclFun (_118_2299))
in (_118_2300)::[])
in (FStar_List.append _118_2301 decls'))
in (FStar_List.append _118_2302 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _53_3355 = (encode_free_var env x t t_norm [])
in (match (_53_3355) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(let _53_3360 = (encode_sigelt env se)
in (match (_53_3360) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _53_3367 -> (match (_53_3367) with
| (l, _53_3364, _53_3366) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _53_3374 -> (match (_53_3374) with
| (l, _53_3371, _53_3373) -> begin
(let _118_2310 = (FStar_All.pipe_left (fun _118_2306 -> FStar_ToSMT_Term.Echo (_118_2306)) (Prims.fst l))
in (let _118_2309 = (let _118_2308 = (let _118_2307 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_118_2307))
in (_118_2308)::[])
in (_118_2310)::_118_2309))
end))))
in (prefix, suffix))))

let last_env = (FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _118_2315 = (let _118_2314 = (let _118_2313 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _118_2313; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_118_2314)::[])
in (FStar_ST.op_Colon_Equals last_env _118_2315)))

let get_env = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_53_3380 -> begin
(let _53_3383 = e
in {bindings = _53_3383.bindings; depth = _53_3383.depth; tcenv = tcenv; warn = _53_3383.warn; cache = _53_3383.cache; nolabels = _53_3383.nolabels; use_zfuel_name = _53_3383.use_zfuel_name; encode_non_total_function_typ = _53_3383.encode_non_total_function_typ})
end))

let set_env = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _53_3389::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun _53_3391 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _53_3397 = hd
in {bindings = _53_3397.bindings; depth = _53_3397.depth; tcenv = _53_3397.tcenv; warn = _53_3397.warn; cache = refs; nolabels = _53_3397.nolabels; use_zfuel_name = _53_3397.use_zfuel_name; encode_non_total_function_typ = _53_3397.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun _53_3400 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _53_3404::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun _53_3406 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _53_3407 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _53_3408 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_53_3411::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _53_3416 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init = (fun tcenv -> (let _53_3418 = (init_env tcenv)
in (let _53_3420 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _53_3423 = (push_env ())
in (let _53_3425 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _53_3428 = (let _118_2336 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _118_2336))
in (let _53_3430 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _53_3433 = (mark_env ())
in (let _53_3435 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _53_3438 = (reset_mark_env ())
in (let _53_3440 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _53_3443 = (commit_mark_env ())
in (let _53_3445 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _118_2350 = (let _118_2349 = (let _118_2348 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _118_2348))
in FStar_ToSMT_Term.Caption (_118_2349))
in (_118_2350)::decls)
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _53_3454 = (encode_sigelt env se)
in (match (_53_3454) with
| (decls, env) -> begin
(let _53_3455 = (set_env env)
in (let _118_2351 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _118_2351)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let _53_3460 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _118_2356 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.fprint2 "Encoding externals for %s ... %s exports\n" name _118_2356))
end else begin
()
end
in (let env = (get_env tcenv)
in (let _53_3467 = (encode_signature (let _53_3463 = env
in {bindings = _53_3463.bindings; depth = _53_3463.depth; tcenv = _53_3463.tcenv; warn = false; cache = _53_3463.cache; nolabels = _53_3463.nolabels; use_zfuel_name = _53_3463.use_zfuel_name; encode_non_total_function_typ = _53_3463.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_53_3467) with
| (decls, env) -> begin
(let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _53_3473 = (set_env (let _53_3471 = env
in {bindings = _53_3471.bindings; depth = _53_3471.depth; tcenv = _53_3471.tcenv; warn = true; cache = _53_3471.cache; nolabels = _53_3471.nolabels; use_zfuel_name = _53_3471.use_zfuel_name; encode_non_total_function_typ = _53_3471.encode_non_total_function_typ}))
in (let _53_3475 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.fprint1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _53_3480 = (let _118_2365 = (let _118_2364 = (let _118_2363 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _118_2363))
in (FStar_Util.format1 "Starting query at %s" _118_2364))
in (push _118_2365))
in (let pop = (fun _53_3483 -> (match (()) with
| () -> begin
(let _118_2370 = (let _118_2369 = (let _118_2368 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _118_2368))
in (FStar_Util.format1 "Ending query at %s" _118_2369))
in (pop _118_2370))
end))
in (let _53_3513 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _53_3496 = (let _118_2374 = (FStar_List.filter (fun _53_33 -> (match (_53_33) with
| FStar_Tc_Env.Binding_sig (_53_3490) -> begin
false
end
| _53_3493 -> begin
true
end)) bindings)
in (encode_env_bindings env _118_2374))
in (match (_53_3496) with
| (env_decls, env) -> begin
(let _53_3497 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _118_2375 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.fprint1 "Encoding query formula: %s\n" _118_2375))
end else begin
()
end
in (let _53_3502 = (encode_formula_with_labels q env)
in (match (_53_3502) with
| (phi, labels, qdecls) -> begin
(let _53_3505 = (encode_labels labels)
in (match (_53_3505) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _118_2377 = (let _118_2376 = (FStar_ToSMT_Term.mkNot phi)
in (_118_2376, Some ("query")))
in FStar_ToSMT_Term.Assume (_118_2377))
in (let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_53_3513) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _53_3520); FStar_ToSMT_Term.hash = _53_3517; FStar_ToSMT_Term.freevars = _53_3515}, _53_3525) -> begin
(let _53_3528 = (pop ())
in ())
end
| _53_3531 when tcenv.FStar_Tc_Env.admit -> begin
(let _53_3532 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _53_3536) -> begin
(let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (let _53_3540 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _53_3546 -> (match (_53_3546) with
| (n, i) -> begin
(let _118_2400 = (let _118_2399 = (let _118_2384 = (let _118_2383 = (FStar_Util.string_of_int n)
in (let _118_2382 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _118_2383 _118_2382)))
in FStar_ToSMT_Term.Caption (_118_2384))
in (let _118_2398 = (let _118_2397 = (let _118_2389 = (let _118_2388 = (let _118_2387 = (let _118_2386 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _118_2385 = (FStar_ToSMT_Term.n_fuel n)
in (_118_2386, _118_2385)))
in (FStar_ToSMT_Term.mkEq _118_2387))
in (_118_2388, None))
in FStar_ToSMT_Term.Assume (_118_2389))
in (let _118_2396 = (let _118_2395 = (let _118_2394 = (let _118_2393 = (let _118_2392 = (let _118_2391 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _118_2390 = (FStar_ToSMT_Term.n_fuel i)
in (_118_2391, _118_2390)))
in (FStar_ToSMT_Term.mkEq _118_2392))
in (_118_2393, None))
in FStar_ToSMT_Term.Assume (_118_2394))
in (_118_2395)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_118_2397)::_118_2396))
in (_118_2399)::_118_2398))
in (FStar_List.append _118_2400 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _118_2404 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _118_2403 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_118_2404, _118_2403)))
in (let alt_configs = (let _118_2423 = (let _118_2422 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _118_2407 = (let _118_2406 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _118_2405 = (FStar_ST.read FStar_Options.max_ifuel)
in (_118_2406, _118_2405)))
in (_118_2407)::[])
end else begin
[]
end
in (let _118_2421 = (let _118_2420 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _118_2410 = (let _118_2409 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _118_2408 = (FStar_ST.read FStar_Options.max_ifuel)
in (_118_2409, _118_2408)))
in (_118_2410)::[])
end else begin
[]
end
in (let _118_2419 = (let _118_2418 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _118_2413 = (let _118_2412 = (FStar_ST.read FStar_Options.max_fuel)
in (let _118_2411 = (FStar_ST.read FStar_Options.max_ifuel)
in (_118_2412, _118_2411)))
in (_118_2413)::[])
end else begin
[]
end
in (let _118_2417 = (let _118_2416 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _118_2415 = (let _118_2414 = (FStar_ST.read FStar_Options.min_fuel)
in (_118_2414, 1))
in (_118_2415)::[])
end else begin
[]
end
in (_118_2416)::[])
in (_118_2418)::_118_2417))
in (_118_2420)::_118_2419))
in (_118_2422)::_118_2421))
in (FStar_List.flatten _118_2423))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _53_3555 -> begin
errs
end)
in (let _53_3557 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _118_2431 = (let _118_2426 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _118_2426))
in (let _118_2430 = (let _118_2427 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _118_2427 FStar_Util.string_of_int))
in (let _118_2429 = (let _118_2428 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _118_2428 FStar_Util.string_of_int))
in (FStar_Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _118_2431 _118_2430 _118_2429))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _53_34 -> (match (_53_34) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _118_2442 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _118_2442 (cb mi p [])))
end
| _53_3569 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _118_2444 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _118_2444 (fun _53_3575 -> (match (_53_3575) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _53_3578 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _53_3581 p alt _53_3586 -> (match ((_53_3581, _53_3586)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _118_2452 = (let _118_2449 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _118_2449))
in (let _118_2451 = (FStar_Util.string_of_int prev_fuel)
in (let _118_2450 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _118_2452 _118_2451 _118_2450))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _118_2453 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _118_2453 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let _53_3591 = (let _118_2459 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _118_2459 q))
in (match (_53_3591) with
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
in (let _53_3592 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _53_3597 = (push "query")
in (let _53_3604 = (encode_formula_with_labels q env)
in (match (_53_3604) with
| (f, _53_3601, _53_3603) -> begin
(let _53_3605 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_3609) -> begin
true
end
| _53_3613 -> begin
false
end))
end)))))

let solver = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

let dummy = {FStar_Tc_Env.init = (fun _53_3614 -> ()); FStar_Tc_Env.push = (fun _53_3616 -> ()); FStar_Tc_Env.pop = (fun _53_3618 -> ()); FStar_Tc_Env.mark = (fun _53_3620 -> ()); FStar_Tc_Env.reset_mark = (fun _53_3622 -> ()); FStar_Tc_Env.commit_mark = (fun _53_3624 -> ()); FStar_Tc_Env.encode_modul = (fun _53_3626 _53_3628 -> ()); FStar_Tc_Env.encode_sig = (fun _53_3630 _53_3632 -> ()); FStar_Tc_Env.solve = (fun _53_3634 _53_3636 -> ()); FStar_Tc_Env.is_trivial = (fun _53_3638 _53_3640 -> false); FStar_Tc_Env.finish = (fun _53_3642 -> ()); FStar_Tc_Env.refresh = (fun _53_3643 -> ())}




