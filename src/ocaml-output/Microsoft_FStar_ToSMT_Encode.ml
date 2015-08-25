
let add_fuel = (fun x tl -> (match ((ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
tl
end
| false -> begin
(x)::tl
end))

let withenv = (fun c _52_40 -> (match (_52_40) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (Microsoft_FStar_List.filter (fun _52_1 -> (match (_52_1) with
| (Microsoft_FStar_Util.Inl (_52_44), _52_47) -> begin
false
end
| _52_50 -> begin
true
end)) args))

let escape = (fun s -> (Microsoft_FStar_Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> (match ((a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = "_")) with
| true -> begin
(Prims.strcat a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end
| false -> begin
a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end))

let mk_typ_projector_name = (fun lid a -> (let _118_14 = (Microsoft_FStar_Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (All.pipe_left escape _118_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _118_19 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _118_19; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _118_20 = (Microsoft_FStar_Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (All.pipe_left escape _118_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _52_62 -> (match (()) with
| () -> begin
(let _118_30 = (let _118_29 = (Microsoft_FStar_Util.string_of_int i)
in (Microsoft_FStar_Util.format2 "Projector %s on data constructor %s not found" _118_29 lid.Microsoft_FStar_Absyn_Syntax.str))
in (All.failwith _118_30))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _118_31 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _118_31.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (binders, _52_66) -> begin
(match (((i < 0) || (i >= (Microsoft_FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| false -> begin
(let b = (Microsoft_FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| Microsoft_FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.Microsoft_FStar_Absyn_Syntax.v)
end))
end)
end
| _52_75 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun lid i -> (let _118_37 = (let _118_36 = (Microsoft_FStar_Util.string_of_int i)
in (Microsoft_FStar_Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _118_36))
in (All.pipe_left escape _118_37)))

let mk_typ_projector = (fun lid a -> (let _118_43 = (let _118_42 = (mk_typ_projector_name lid a)
in (_118_42, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _118_43)))

let mk_term_projector = (fun lid a -> (let _118_49 = (let _118_48 = (mk_term_projector_name lid a)
in (_118_48, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _118_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _118_55 = (let _118_54 = (mk_term_projector_name_by_pos lid i)
in (_118_54, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _118_55)))

let mk_data_tester = (fun env l x -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (fun _ -> (All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (Microsoft_FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _52_101 -> (match (()) with
| () -> begin
(let _118_159 = (Microsoft_FStar_Util.smap_create 100)
in (let _118_158 = (Microsoft_FStar_Util.smap_create 100)
in (_118_159, _118_158)))
end))
in (let scopes = (let _118_161 = (let _118_160 = (new_scope ())
in (_118_160)::[])
in (Microsoft_FStar_Util.mk_ref _118_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _118_165 = (ST.read scopes)
in (Microsoft_FStar_Util.find_map _118_165 (fun _52_109 -> (match (_52_109) with
| (names, _52_108) -> begin
(Microsoft_FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_52_112) -> begin
(let _52_114 = (Microsoft_FStar_Util.incr ctr)
in (let _118_167 = (let _118_166 = (ST.read ctr)
in (Microsoft_FStar_Util.string_of_int _118_166))
in (Prims.strcat (Prims.strcat y "__") _118_167)))
end)
in (let top_scope = (let _118_169 = (let _118_168 = (ST.read scopes)
in (Microsoft_FStar_List.hd _118_168))
in (All.pipe_left Prims.fst _118_169))
in (let _52_118 = (Microsoft_FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _118_175 = (let _118_174 = (All.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Prims.strcat _118_174 "__"))
in (Prims.strcat _118_175 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun _52_126 -> (match (()) with
| () -> begin
(let _52_127 = (Microsoft_FStar_Util.incr ctr)
in (ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _118_183 = (let _118_182 = (next_id ())
in (All.pipe_left Microsoft_FStar_Util.string_of_int _118_182))
in (Microsoft_FStar_Util.format2 "%s_%s" pfx _118_183)))
in (let string_const = (fun s -> (match ((let _118_187 = (ST.read scopes)
in (Microsoft_FStar_Util.find_map _118_187 (fun _52_136 -> (match (_52_136) with
| (_52_134, strings) -> begin
(Microsoft_FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _118_188 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxString _118_188))
in (let top_scope = (let _118_190 = (let _118_189 = (ST.read scopes)
in (Microsoft_FStar_List.hd _118_189))
in (All.pipe_left Prims.snd _118_190))
in (let _52_143 = (Microsoft_FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _52_146 -> (match (()) with
| () -> begin
(let _118_195 = (let _118_194 = (new_scope ())
in (let _118_193 = (ST.read scopes)
in (_118_194)::_118_193))
in (ST.op_Colon_Equals scopes _118_195))
end))
in (let pop = (fun _52_148 -> (match (()) with
| () -> begin
(let _118_199 = (let _118_198 = (ST.read scopes)
in (Microsoft_FStar_List.tl _118_198))
in (ST.op_Colon_Equals scopes _118_199))
end))
in (let mark = (fun _52_150 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _52_152 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _52_154 -> (match (()) with
| () -> begin
(match ((ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _52_167 = (Microsoft_FStar_Util.smap_fold hd1 (fun key value v -> (Microsoft_FStar_Util.smap_add next1 key value)) ())
in (let _52_172 = (Microsoft_FStar_Util.smap_fold hd2 (fun key value v -> (Microsoft_FStar_Util.smap_add next2 key value)) ())
in (ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _52_175 -> begin
(All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (let _118_215 = (let _118_214 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _118_213 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_118_214, _118_213)))
in (Microsoft_FStar_Absyn_Util.mkbvd _118_215)))

type binding =
| Binding_var of (Microsoft_FStar_Absyn_Syntax.bvvdef * Microsoft_FStar_ToSMT_Term.term)
| Binding_tvar of (Microsoft_FStar_Absyn_Syntax.btvdef * Microsoft_FStar_ToSMT_Term.term)
| Binding_fvar of (Microsoft_FStar_Absyn_Syntax.lident * Prims.string * Microsoft_FStar_ToSMT_Term.term Prims.option * Microsoft_FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (Microsoft_FStar_Absyn_Syntax.lident * Prims.string * Microsoft_FStar_ToSMT_Term.term Prims.option)

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
| Binding_var (_52_180) -> begin
_52_180
end))

let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_52_183) -> begin
_52_183
end))

let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_52_186) -> begin
_52_186
end))

let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_52_189) -> begin
_52_189
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : Microsoft_FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * Microsoft_FStar_ToSMT_Term.sort Prims.list * Microsoft_FStar_ToSMT_Term.decl Prims.list) Microsoft_FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t = (fun _ -> (All.failwith "Not yet implemented:is_Mkenv_t"))

let print_env = (fun e -> (let _118_301 = (All.pipe_right e.bindings (Microsoft_FStar_List.map (fun _52_2 -> (match (_52_2) with
| Binding_var (x, t) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _52_214) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end))))
in (All.pipe_right _118_301 (Microsoft_FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (Microsoft_FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_311 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_118_311))
end
| false -> begin
None
end))

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _118_316 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _118_316))))

let gen_term_var = (fun env x -> (let ysym = (let _118_321 = (Microsoft_FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _118_321))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _52_233 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _52_233.tcenv; warn = _52_233.warn; cache = _52_233.cache; nolabels = _52_233.nolabels; use_zfuel_name = _52_233.use_zfuel_name; encode_non_total_function_typ = _52_233.encode_non_total_function_typ})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _52_239 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _52_239.depth; tcenv = _52_239.tcenv; warn = _52_239.warn; cache = _52_239.cache; nolabels = _52_239.nolabels; use_zfuel_name = _52_239.use_zfuel_name; encode_non_total_function_typ = _52_239.encode_non_total_function_typ})))))

let push_term_var = (fun env x t -> (let _52_244 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _52_244.depth; tcenv = _52_244.tcenv; warn = _52_244.warn; cache = _52_244.cache; nolabels = _52_244.nolabels; use_zfuel_name = _52_244.use_zfuel_name; encode_non_total_function_typ = _52_244.encode_non_total_function_typ}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _52_3 -> (match (_52_3) with
| Binding_var (b, t) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _52_254 -> begin
None
end)))) with
| None -> begin
(let _118_336 = (let _118_335 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Util.format1 "Bound term variable not found: %s" _118_335))
in (All.failwith _118_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _118_341 = (Microsoft_FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _118_341))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _52_264 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _52_264.tcenv; warn = _52_264.warn; cache = _52_264.cache; nolabels = _52_264.nolabels; use_zfuel_name = _52_264.use_zfuel_name; encode_non_total_function_typ = _52_264.encode_non_total_function_typ})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _52_270 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _52_270.depth; tcenv = _52_270.tcenv; warn = _52_270.warn; cache = _52_270.cache; nolabels = _52_270.nolabels; use_zfuel_name = _52_270.use_zfuel_name; encode_non_total_function_typ = _52_270.encode_non_total_function_typ})))))

let push_typ_var = (fun env x t -> (let _52_275 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _52_275.depth; tcenv = _52_275.tcenv; warn = _52_275.warn; cache = _52_275.cache; nolabels = _52_275.nolabels; use_zfuel_name = _52_275.use_zfuel_name; encode_non_total_function_typ = _52_275.encode_non_total_function_typ}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _52_4 -> (match (_52_4) with
| Binding_tvar (b, t) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _52_285 -> begin
None
end)))) with
| None -> begin
(let _118_356 = (let _118_355 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Util.format1 "Bound type variable not found: %s" _118_355))
in (All.failwith _118_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _118_367 = (let _52_295 = env
in (let _118_366 = (let _118_365 = (let _118_364 = (let _118_363 = (let _118_362 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (All.pipe_left (fun _118_361 -> Some (_118_361)) _118_362))
in (x, fname, _118_363, None))
in Binding_fvar (_118_364))
in (_118_365)::env.bindings)
in {bindings = _118_366; depth = _52_295.depth; tcenv = _52_295.tcenv; warn = _52_295.warn; cache = _52_295.cache; nolabels = _52_295.nolabels; use_zfuel_name = _52_295.use_zfuel_name; encode_non_total_function_typ = _52_295.encode_non_total_function_typ}))
in (fname, ftok, _118_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _52_5 -> (match (_52_5) with
| Binding_fvar (b, t1, t2, t3) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _52_307 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _118_378 = (let _118_377 = (Microsoft_FStar_Absyn_Print.sli a)
in (Microsoft_FStar_Util.format1 "Name not found: %s" _118_377))
in (All.failwith _118_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _52_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _52_317.depth; tcenv = _52_317.tcenv; warn = _52_317.warn; cache = _52_317.cache; nolabels = _52_317.nolabels; use_zfuel_name = _52_317.use_zfuel_name; encode_non_total_function_typ = _52_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _52_326 = (lookup_lid env x)
in (match (_52_326) with
| (t1, t2, _52_325) -> begin
(let t3 = (let _118_395 = (let _118_394 = (let _118_393 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_118_393)::[])
in (f, _118_394))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_395))
in (let _52_328 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _52_328.depth; tcenv = _52_328.tcenv; warn = _52_328.warn; cache = _52_328.cache; nolabels = _52_328.nolabels; use_zfuel_name = _52_328.use_zfuel_name; encode_non_total_function_typ = _52_328.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun env a -> (let _52_335 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _52_339 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (_52_343, fuel::[]) -> begin
(match ((let _118_399 = (let _118_398 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (All.pipe_right _118_398 Prims.fst))
in (Microsoft_FStar_Util.starts_with _118_399 "fuel"))) with
| true -> begin
(let _118_400 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _118_400 fuel))
end
| false -> begin
t
end)
end
| _52_349 -> begin
t
end)
end
| _52_351 -> begin
(let _118_402 = (let _118_401 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Util.format1 "Name not found: %s" _118_401))
in (All.failwith _118_402))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _52_359 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_359) with
| (x, _52_356, _52_358) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _52_365 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_365) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App (g, zf); Microsoft_FStar_ToSMT_Term.hash = _52_369; Microsoft_FStar_ToSMT_Term.freevars = _52_367}) when env.use_zfuel_name -> begin
(g, zf)
end
| _52_377 -> begin
(match (sym) with
| None -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _52_387 -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _118_417 = (let _52_392 = env
in (let _118_416 = (let _118_415 = (let _118_414 = (let _118_413 = (let _118_412 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (All.pipe_left (fun _118_411 -> Some (_118_411)) _118_412))
in (x, fname, _118_413))
in Binding_ftvar (_118_414))
in (_118_415)::env.bindings)
in {bindings = _118_416; depth = _52_392.depth; tcenv = _52_392.tcenv; warn = _52_392.warn; cache = _52_392.cache; nolabels = _52_392.nolabels; use_zfuel_name = _52_392.use_zfuel_name; encode_non_total_function_typ = _52_392.encode_non_total_function_typ}))
in (fname, ftok, _118_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _52_6 -> (match (_52_6) with
| Binding_ftvar (b, t1, t2) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _52_403 -> begin
None
end)))) with
| None -> begin
(let _118_424 = (let _118_423 = (Microsoft_FStar_Absyn_Print.sli a)
in (Microsoft_FStar_Util.format1 "Type name not found: %s" _118_423))
in (All.failwith _118_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _52_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _52_411.depth; tcenv = _52_411.tcenv; warn = _52_411.warn; cache = _52_411.cache; nolabels = _52_411.nolabels; use_zfuel_name = _52_411.use_zfuel_name; encode_non_total_function_typ = _52_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _118_435 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (All.pipe_right _118_435 Prims.snd))) with
| None -> begin
(let _118_437 = (let _118_436 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Microsoft_FStar_Util.format1 "Type name not found: %s" _118_436))
in (All.failwith _118_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _118_440 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (All.pipe_right _118_440 Prims.fst)))

let tok_of_name = (fun env nm -> (Microsoft_FStar_Util.find_map env.bindings (fun _52_7 -> (match (_52_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _52_436 -> begin
None
end))))

let mkForall_fuel' = (fun n _52_441 -> (match (_52_441) with
| (pats, vars, body) -> begin
(let fallback = (fun _52_443 -> (match (()) with
| () -> begin
(Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in (match ((ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
(fallback ())
end
| false -> begin
(let _52_446 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_446) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (All.pipe_right tms (Microsoft_FStar_List.map (fun p -> (match (p.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _52_456 -> begin
p
end)))))
in (let pats = (add_fuel pats)
in (let body = (match (body.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.And, guards) -> begin
(let _118_453 = (add_fuel guards)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _118_453))
end
| _52_469 -> begin
(let _118_454 = (add_fuel ((guard)::[]))
in (All.pipe_right _118_454 Microsoft_FStar_List.hd))
end)
in (Microsoft_FStar_ToSMT_Term.mkImp (guard, body')))
end
| _52_472 -> begin
body
end)
in (let vars = ((fsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars
in (Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end))
end))

let mkForall_fuel = (mkForall_fuel' 1)

let head_normal = (fun env t -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (v)) | (Microsoft_FStar_Absyn_Syntax.Typ_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (v); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _118_460 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (All.pipe_right _118_460 Option.isNone))
end
| _52_510 -> begin
false
end)))

let whnf = (fun env t -> (match ((head_normal env t)) with
| true -> begin
t
end
| false -> begin
(Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end))

let whnf_e = (fun env e -> (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))

let norm_t = (fun env t -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env.tcenv t))

let norm_k = (fun env k -> (Microsoft_FStar_Tc_Normalize.normalize_kind env.tcenv k))

let trivial_post = (fun t -> (let _118_482 = (let _118_481 = (let _118_479 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_118_479)::[])
in (let _118_480 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_118_481, _118_480)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _118_482 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (All.pipe_right vars (Microsoft_FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _118_489 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _118_489))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _118_490 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _118_490))
end
| _52_527 -> begin
(let _118_491 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _118_491))
end)) e)))

let mk_ApplyE_args = (fun e args -> (All.pipe_right args (Microsoft_FStar_List.fold_left (fun out arg -> (match (arg) with
| Microsoft_FStar_Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyET out t)
end
| Microsoft_FStar_Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))

let mk_ApplyT = (fun t vars -> (All.pipe_right vars (Microsoft_FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _118_504 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _118_504))
end
| _52_542 -> begin
(let _118_505 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _118_505))
end)) t)))

let mk_ApplyT_args = (fun t args -> (All.pipe_right args (Microsoft_FStar_List.fold_left (fun out arg -> (match (arg) with
| Microsoft_FStar_Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTT out t)
end
| Microsoft_FStar_Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app = (fun _52_8 -> (match (_52_8) with
| (Microsoft_FStar_ToSMT_Term.Var ("ApplyTT")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyTE")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyET")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _52_561 -> begin
false
end))

let is_eta = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.Microsoft_FStar_ToSMT_Term.tm, xs)) with
| (Microsoft_FStar_ToSMT_Term.App (app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _52_572; Microsoft_FStar_ToSMT_Term.freevars = _52_570}::[]), x::xs) when ((is_app app) && (Microsoft_FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.Var (f), args), _52_590) -> begin
(match ((((Microsoft_FStar_List.length args) = (Microsoft_FStar_List.length vars)) && (Microsoft_FStar_List.forall2 (fun a v -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _52_597 -> begin
false
end)) args vars))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_52_599, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in (match ((All.pipe_right fvs (Microsoft_FStar_List.for_all (fun fv -> (not ((Microsoft_FStar_Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars))))))) with
| true -> begin
Some (t)
end
| false -> begin
None
end))
end
| _52_605 -> begin
None
end))
in (aux t (Microsoft_FStar_List.rev vars))))

type label =
(Microsoft_FStar_ToSMT_Term.fv * Prims.string * Microsoft_FStar_Range.range)

type labels =
label Prims.list

type pattern =
{pat_vars : (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (Microsoft_FStar_ToSMT_Term.term * Microsoft_FStar_ToSMT_Term.decls_t); guard : Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term; projections : Microsoft_FStar_ToSMT_Term.term  ->  (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.term) Prims.list}

let is_Mkpattern = (fun _ -> (All.failwith "Not yet implemented:is_Mkpattern"))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const = (fun _52_9 -> (match (_52_9) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
Microsoft_FStar_ToSMT_Term.mk_Term_unit
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (true) -> begin
(Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (false) -> begin
(Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkFalse)
end
| Microsoft_FStar_Absyn_Syntax.Const_char (c) -> begin
(let _118_561 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Microsoft_FStar_Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _118_561))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _118_562 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Microsoft_FStar_Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _118_562))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _118_563 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _118_563))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _118_567 = (let _118_566 = (let _118_565 = (let _118_564 = (Microsoft_FStar_ToSMT_Term.mkInteger32 i)
in (Microsoft_FStar_ToSMT_Term.boxInt _118_564))
in (_118_565)::[])
in ("Int32.Int32", _118_566))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_567))
end
| Microsoft_FStar_Absyn_Syntax.Const_string (bytes, _52_627) -> begin
(let _118_568 = (All.pipe_left Microsoft_FStar_Util.string_of_bytes bytes)
in (varops.string_const _118_568))
end
| c -> begin
(let _118_570 = (let _118_569 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Microsoft_FStar_Util.format1 "Unhandled constant: %s\n" _118_569))
in (All.failwith _118_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_638) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_641) -> begin
(let _118_579 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _118_579))
end
| _52_644 -> begin
(match (norm) with
| true -> begin
(let _118_580 = (whnf env t)
in (aux false _118_580))
end
| false -> begin
(let _118_583 = (let _118_582 = (Microsoft_FStar_Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _118_581 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Microsoft_FStar_Util.format2 "(%s) Expected a function typ; got %s" _118_582 _118_581)))
in (All.failwith _118_583))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _118_619 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _118_619.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (_52_649, k0) -> begin
(let _52_653 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _118_621 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _118_620 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Microsoft_FStar_Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _118_621 _118_620)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar (uv, _52_657) -> begin
(let _118_623 = (let _118_622 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _118_622))
in (_118_623, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _118_624 = (varops.fresh "t")
in (_118_624, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _52_672 = (encode_binders None bs env)
in (match (_52_672) with
| (vars, guards, env', decls, _52_671) -> begin
(let app = (mk_ApplyT t vars)
in (let _52_676 = (encode_knd kbody env' app)
in (match (_52_676) with
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
| _52_695 -> begin
(let _118_633 = (let _118_632 = (let _118_631 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_631))
in (_118_632, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _118_633))
end)
in (let _118_635 = (let _118_634 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _118_634))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_635)))))
end
| _52_698 -> begin
(All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _118_637 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (All.pipe_right _118_637 (Microsoft_FStar_List.filter (fun _52_703 -> (match (_52_703) with
| (x, _52_702) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Microsoft_FStar_Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _52_709) -> begin
(let _118_640 = (let _118_639 = (let _118_638 = (All.pipe_right cvars (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _118_638))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_639))
in (_118_640, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Microsoft_FStar_List.map Prims.snd cvars)
in (let caption = (match ((ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _118_641 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_118_641))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _118_643 = (let _118_642 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _118_642))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_643))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _118_652 = (let _118_651 = (let _118_650 = (let _118_649 = (let _118_648 = (let _118_647 = (let _118_646 = (let _118_645 = (let _118_644 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_644))
in (_118_645, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _118_646))
in (t_has_k, _118_647))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_648))
in ((t_has_k)::[], (tsym)::cvars, _118_649))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_650))
in (_118_651, Some ((Prims.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_118_652))
in (let k_decls = (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _52_721 = (Microsoft_FStar_Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _52_724 -> begin
(let _118_654 = (let _118_653 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Microsoft_FStar_Util.format1 "Unknown kind: %s" _118_653))
in (All.failwith _118_654))
end))
and encode_knd = (fun k env t -> (let _52_730 = (encode_knd_term k env)
in (match (_52_730) with
| (k, decls) -> begin
(let _118_658 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_118_658, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _52_734 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_662 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Microsoft_FStar_Util.fprint1 "Encoding binders %s\n" _118_662))
end
| false -> begin
()
end)
in (let _52_784 = (All.pipe_right bs (Microsoft_FStar_List.fold_left (fun _52_741 b -> (match (_52_741) with
| (vars, guards, env, decls, names) -> begin
(let _52_778 = (match ((Prims.fst b)) with
| Microsoft_FStar_Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _52_744}) -> begin
(let a = (unmangle a)
in (let _52_753 = (gen_typ_var env a)
in (match (_52_753) with
| (aasym, aa, env') -> begin
(let _52_754 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _118_666 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _118_665 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Microsoft_FStar_Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _118_666 aasym _118_665)))
end
| false -> begin
()
end)
in (let _52_758 = (encode_knd k env aa)
in (match (_52_758) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Microsoft_FStar_Util.Inl (a))
end)))
end)))
end
| Microsoft_FStar_Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _52_760}) -> begin
(let x = (unmangle x)
in (let _52_769 = (gen_term_var env x)
in (match (_52_769) with
| (xxsym, xx, env') -> begin
(let _52_772 = (let _118_667 = (norm_t env t)
in (encode_typ_pred fuel_opt _118_667 env xx))
in (match (_52_772) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Microsoft_FStar_Util.Inr (x))
end))
end)))
end)
in (match (_52_778) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Microsoft_FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_52_784) with
| (vars, guards, env, decls, names) -> begin
((Microsoft_FStar_List.rev vars), (Microsoft_FStar_List.rev guards), env, decls, (Microsoft_FStar_List.rev names))
end))))
and encode_typ_pred = (fun fuel_opt t env e -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _52_792 = (encode_typ_term t env)
in (match (_52_792) with
| (t, decls) -> begin
(let _118_672 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_118_672, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _52_800 = (encode_typ_term t env)
in (match (_52_800) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _118_677 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_118_677, decls))
end
| Some (f) -> begin
(let _118_678 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_118_678, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _118_681 = (lookup_typ_var env a)
in (_118_681, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _118_682 = (lookup_free_tvar env fv)
in (_118_682, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _52_821 = (encode_binders None binders env)
in (match (_52_821) with
| (vars, guards, env', decls, _52_820) -> begin
(let fsym = (let _118_683 = (varops.fresh "f")
in (_118_683, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _52_827 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_52_827) with
| (pre_opt, res_t) -> begin
(let _52_830 = (encode_typ_pred None res_t env' app)
in (match (_52_830) with
| (res_pred, decls') -> begin
(let _52_839 = (match (pre_opt) with
| None -> begin
(let _118_684 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_118_684, decls))
end
| Some (pre) -> begin
(let _52_836 = (encode_formula pre env')
in (match (_52_836) with
| (guard, decls0) -> begin
(let _118_685 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_118_685, (Microsoft_FStar_List.append decls decls0)))
end))
end)
in (match (_52_839) with
| (guards, guard_decls) -> begin
(let t_interp = (let _118_687 = (let _118_686 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _118_686))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_687))
in (let cvars = (let _118_689 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (All.pipe_right _118_689 (Microsoft_FStar_List.filter (fun _52_844 -> (match (_52_844) with
| (x, _52_843) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Microsoft_FStar_Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _52_850) -> begin
(let _118_692 = (let _118_691 = (let _118_690 = (All.pipe_right cvars (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _118_690))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_691))
in (_118_692, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Microsoft_FStar_List.map Prims.snd cvars)
in (let caption = (match ((ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _118_693 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_118_693))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _118_695 = (let _118_694 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_694))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_695))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _118_697 = (let _118_696 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_118_696, Some ((Prims.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_118_697))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _118_704 = (let _118_703 = (let _118_702 = (let _118_701 = (let _118_700 = (let _118_699 = (let _118_698 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _118_698))
in (f_has_t, _118_699))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_700))
in ((f_has_t)::[], (fsym)::cvars, _118_701))
in (mkForall_fuel _118_702))
in (_118_703, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_704))
in (let t_interp = (let _118_708 = (let _118_707 = (let _118_706 = (let _118_705 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in ((f_has_t_z)::[], (fsym)::cvars, _118_705))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_706))
in (_118_707, Some ((Prims.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_118_708))
in (let t_decls = (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _52_866 = (Microsoft_FStar_Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end
| false -> begin
(let tsym = (varops.fresh "Non_total_Typ_fun")
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (tsym, []))
in (let t_kinding = (let _118_710 = (let _118_709 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_118_709, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_710))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _118_717 = (let _118_716 = (let _118_715 = (let _118_714 = (let _118_713 = (let _118_712 = (let _118_711 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _118_711))
in (f_has_t, _118_712))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_713))
in ((f_has_t)::[], (fsym)::[], _118_714))
in (mkForall_fuel _118_715))
in (_118_716, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_717))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_877) -> begin
(let _52_896 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine (x, f); Microsoft_FStar_Absyn_Syntax.tk = _52_886; Microsoft_FStar_Absyn_Syntax.pos = _52_884; Microsoft_FStar_Absyn_Syntax.fvs = _52_882; Microsoft_FStar_Absyn_Syntax.uvs = _52_880} -> begin
(x, f)
end
| _52_893 -> begin
(All.failwith "impossible")
end)
in (match (_52_896) with
| (x, f) -> begin
(let _52_899 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_52_899) with
| (base_t, decls) -> begin
(let _52_903 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_903) with
| (x, xtm, env') -> begin
(let _52_906 = (encode_formula f env')
in (match (_52_906) with
| (refinement, decls') -> begin
(let _52_909 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_909) with
| (fsym, fterm) -> begin
(let encoding = (let _118_719 = (let _118_718 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_118_718, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _118_719))
in (let cvars = (let _118_721 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (All.pipe_right _118_721 (Microsoft_FStar_List.filter (fun _52_914 -> (match (_52_914) with
| (y, _52_913) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((Microsoft_FStar_Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some (t, _52_921, _52_923) -> begin
(let _118_724 = (let _118_723 = (let _118_722 = (All.pipe_right cvars (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _118_722))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_723))
in (_118_724, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Microsoft_FStar_List.map Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _118_726 = (let _118_725 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_725))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_726))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _118_728 = (let _118_727 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (ffv)::(xfv)::cvars, _118_727))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_728))
in (let t_decls = (let _118_735 = (let _118_734 = (let _118_733 = (let _118_732 = (let _118_731 = (let _118_730 = (let _118_729 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_118_729))
in (assumption, _118_730))
in Microsoft_FStar_ToSMT_Term.Assume (_118_731))
in (_118_732)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_118_733)
in (tdecl)::_118_734)
in (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls') _118_735))
in (let _52_936 = (Microsoft_FStar_Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _118_736 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _118_736))
in (let _52_945 = (encode_knd k env ttm)
in (match (_52_945) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let is_full_app = (fun _52_952 -> (match (()) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _52_957 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_52_957) with
| (formals, _52_956) -> begin
((Microsoft_FStar_List.length formals) = (Microsoft_FStar_List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _52_964 = (encode_args args env)
in (match (_52_964) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _52_970 = (encode_args args env)
in (match (_52_970) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _118_741 = (let _118_740 = (Microsoft_FStar_List.map (fun _52_10 -> (match (_52_10) with
| (Microsoft_FStar_Util.Inl (t)) | (Microsoft_FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _118_740))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_741))
in (t, decls)))
end
| false -> begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _118_742 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _118_742))
in (let _52_986 = (encode_knd k env ttm)
in (match (_52_986) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _52_989 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(let _52_1001 = (encode_binders None bs env)
in (match (_52_1001) with
| (vars, guards, env, decls, _52_1000) -> begin
(let _52_1004 = (encode_typ_term body env)
in (match (_52_1004) with
| (body, decls') -> begin
(let key_body = (let _118_746 = (let _118_745 = (let _118_744 = (let _118_743 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_118_743, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_744))
in ([], vars, _118_745))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_746))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Microsoft_FStar_Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some (t, _52_1010, _52_1012) -> begin
(let _118_749 = (let _118_748 = (let _118_747 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _118_747))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_748))
in (_118_749, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(let cvar_sorts = (Microsoft_FStar_List.map Prims.snd cvars)
in (let tsym = (varops.fresh "Typ_lam")
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _118_751 = (let _118_750 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_750))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_751))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _118_758 = (let _118_757 = (let _118_756 = (let _118_755 = (let _118_754 = (let _118_753 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _118_752 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_118_753, _118_752)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_754))
in ((app)::[], (Microsoft_FStar_List.append vars cvars), _118_755))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_756))
in (_118_757, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_758))
in (let kinding = (let _52_1027 = (let _118_759 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _118_759 env t))
in (match (_52_1027) with
| (ktm, decls'') -> begin
(let _118_763 = (let _118_762 = (let _118_761 = (let _118_760 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_118_760, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_761))
in (_118_762)::[])
in (Microsoft_FStar_List.append decls'' _118_763))
end))
in (let t_decls = (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _52_1030 = (Microsoft_FStar_Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (t, _52_1034) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_52_1038) -> begin
(let _118_764 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _118_764 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _118_769 = (let _118_768 = (All.pipe_left Microsoft_FStar_Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _118_767 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _118_766 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _118_765 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Microsoft_FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _118_768 _118_767 _118_766 _118_765)))))
in (All.failwith _118_769))
end)))
and encode_exp = (fun e env -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_52_1049) -> begin
(let _118_772 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _118_772 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (v, _52_1056) -> begin
(let _118_773 = (lookup_free_var env v)
in (_118_773, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _118_774 = (encode_const c)
in (_118_774, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (e, t, _52_1064) -> begin
(let _52_1067 = (ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared (e, _52_1071)) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (uv, _52_1077) -> begin
(let e = (let _118_775 = (Microsoft_FStar_Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _118_775))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _52_1086 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _118_778 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_118_778, (decl)::[]))))
end))
in (match ((ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_1090 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _118_779 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (All.pipe_left Prims.op_Negation _118_779))) with
| true -> begin
(fallback ())
end
| false -> begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let nformals = (Microsoft_FStar_List.length bs')
in (match (((nformals < (Microsoft_FStar_List.length bs)) && (Microsoft_FStar_Absyn_Util.is_total_comp c))) with
| true -> begin
(let _52_1102 = (Microsoft_FStar_Util.first_N nformals bs)
in (match (_52_1102) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _52_1106 -> begin
(All.failwith "Impossible")
end)
in (let e = (let _118_781 = (let _118_780 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _118_780))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _118_781 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _52_1115 = (encode_binders None bs env)
in (match (_52_1115) with
| (vars, guards, envbody, decls, _52_1114) -> begin
(let _52_1118 = (encode_exp body envbody)
in (match (_52_1118) with
| (body, decls') -> begin
(let key_body = (let _118_785 = (let _118_784 = (let _118_783 = (let _118_782 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_118_782, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_783))
in ([], vars, _118_784))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_785))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Microsoft_FStar_Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some (t, _52_1124, _52_1126) -> begin
(let _118_788 = (let _118_787 = (let _118_786 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _118_786))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_787))
in (_118_788, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (Microsoft_FStar_List.map Prims.snd cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let f = (let _118_790 = (let _118_789 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _118_789))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_790))
in (let app = (mk_ApplyE f vars)
in (let _52_1140 = (encode_typ_pred None tfun env f)
in (match (_52_1140) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _118_792 = (let _118_791 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_118_791, Some ((Prims.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_118_792))
in (let interp_f = (let _118_799 = (let _118_798 = (let _118_797 = (let _118_796 = (let _118_795 = (let _118_794 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _118_793 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_118_794, _118_793)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_795))
in ((app)::[], (Microsoft_FStar_List.append vars cvars), _118_796))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_797))
in (_118_798, Some ((Prims.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_118_799))
in (let f_decls = (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _52_1144 = (Microsoft_FStar_Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end))
end
| _52_1147 -> begin
(All.failwith "Impossible")
end))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar (l, _52_1158); Microsoft_FStar_Absyn_Syntax.tk = _52_1155; Microsoft_FStar_Absyn_Syntax.pos = _52_1153; Microsoft_FStar_Absyn_Syntax.fvs = _52_1151; Microsoft_FStar_Absyn_Syntax.uvs = _52_1149}, (Microsoft_FStar_Util.Inl (_52_1173), _52_1176)::(Microsoft_FStar_Util.Inr (v1), _52_1170)::(Microsoft_FStar_Util.Inr (v2), _52_1165)::[]) when (Microsoft_FStar_Absyn_Syntax.lid_equals l.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
(let _52_1183 = (encode_exp v1 env)
in (match (_52_1183) with
| (v1, decls1) -> begin
(let _52_1186 = (encode_exp v2 env)
in (match (_52_1186) with
| (v2, decls2) -> begin
(let _118_800 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_118_800, (Microsoft_FStar_List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_1196); Microsoft_FStar_Absyn_Syntax.tk = _52_1194; Microsoft_FStar_Absyn_Syntax.pos = _52_1192; Microsoft_FStar_Absyn_Syntax.fvs = _52_1190; Microsoft_FStar_Absyn_Syntax.uvs = _52_1188}, _52_1200) -> begin
(let _118_801 = (whnf_e env e)
in (encode_exp _118_801 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(let _52_1209 = (encode_args args_e env)
in (match (_52_1209) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _52_1214 = (encode_exp head env)
in (match (_52_1214) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Microsoft_FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _52_1223 = (Microsoft_FStar_Util.first_N (Microsoft_FStar_List.length args_e) formals)
in (match (_52_1223) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _118_804 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (All.pipe_right _118_804 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_1228 = (encode_typ_pred None ty env app_tm)
in (match (_52_1228) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _118_806 = (let _118_805 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_118_805, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_806))
in (app_tm, (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _52_1235 = (lookup_free_var_sym env fv)
in (match (_52_1235) with
| (fname, fuel_args) -> begin
(let tm = (let _118_812 = (let _118_811 = (let _118_810 = (Microsoft_FStar_List.map (fun _52_11 -> (match (_52_11) with
| (Microsoft_FStar_Util.Inl (t)) | (Microsoft_FStar_Util.Inr (t)) -> begin
t
end)) args)
in (Microsoft_FStar_List.append fuel_args _118_810))
in (fname, _118_811))
in (Microsoft_FStar_ToSMT_Term.mkApp' _118_812))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _52_1242 = (match ((All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _118_814 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _118_813 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Microsoft_FStar_Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _118_814 _118_813)))
end
| false -> begin
()
end)
in (let head_type = (let _118_817 = (let _118_816 = (let _118_815 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _118_815))
in (whnf env _118_816))
in (All.pipe_left Microsoft_FStar_Absyn_Util.unrefine _118_817))
in (let _52_1245 = (match ((All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _118_820 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _118_819 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _118_818 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Microsoft_FStar_Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _118_820 _118_819 _118_818))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _118_824 = (let _118_823 = (Microsoft_FStar_Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _118_822 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _118_821 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Microsoft_FStar_Util.format3 "(%s) term is %s; head type is %s\n" _118_823 _118_822 _118_821))))
in (All.failwith _118_824))
end
| Some (formals, c) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (fv, _52_1254) when ((Microsoft_FStar_List.length formals) = (Microsoft_FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _52_1258 -> begin
(match (((Microsoft_FStar_List.length formals) > (Microsoft_FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some ((formals, c))))
end
| false -> begin
(encode_partial_app None)
end)
end)
end)))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((false, {Microsoft_FStar_Absyn_Syntax.lbname = Microsoft_FStar_Util.Inr (_52_1267); Microsoft_FStar_Absyn_Syntax.lbtyp = _52_1265; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1263; Microsoft_FStar_Absyn_Syntax.lbdef = _52_1261}::[]), _52_1273) -> begin
(All.failwith "Impossible: already handled by encoding of Sig_let")
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((false, {Microsoft_FStar_Absyn_Syntax.lbname = Microsoft_FStar_Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = t1; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1279; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _52_1291 = (encode_exp e1 env)
in (match (_52_1291) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _52_1295 = (encode_exp e2 env')
in (match (_52_1295) with
| (ee2, decls2) -> begin
(ee2, (Microsoft_FStar_List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_52_1297) -> begin
(let _52_1299 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _118_825 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_118_825, (decl_e)::[])))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _52_1309 = (encode_exp e env)
in (match (_52_1309) with
| (scr, decls) -> begin
(let _52_1349 = (Microsoft_FStar_List.fold_right (fun _52_1313 _52_1316 -> (match ((_52_1313, _52_1316)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Microsoft_FStar_List.fold_right (fun _52_1320 _52_1323 -> (match ((_52_1320, _52_1323)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (All.pipe_right projections (Microsoft_FStar_List.fold_left (fun env _52_1329 -> (match (_52_1329) with
| (x, t) -> begin
(match (x) with
| Microsoft_FStar_Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Microsoft_FStar_Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _52_1343 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _52_1340 = (encode_exp w env)
in (match (_52_1340) with
| (w, decls2) -> begin
(let _118_836 = (let _118_835 = (let _118_834 = (let _118_833 = (let _118_832 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _118_832))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_833))
in (guard, _118_834))
in (Microsoft_FStar_ToSMT_Term.mkAnd _118_835))
in (_118_836, decls2))
end))
end)
in (match (_52_1343) with
| (guard, decls2) -> begin
(let _52_1346 = (encode_exp br env)
in (match (_52_1346) with
| (br, decls3) -> begin
(let _118_837 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_118_837, (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_52_1349) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_52_1351) -> begin
(let _118_840 = (let _118_839 = (Microsoft_FStar_Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _118_838 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Microsoft_FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _118_839 _118_838)))
in (All.failwith _118_840))
end))))
and encode_pat = (fun env pat -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Microsoft_FStar_List.map (encode_one_pat env) ps)
end
| _52_1358 -> begin
(let _118_843 = (encode_one_pat env pat)
in (_118_843)::[])
end))
and encode_one_pat = (fun env pat -> (let _52_1361 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_846 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Microsoft_FStar_Util.fprint1 "Encoding pattern %s\n" _118_846))
end
| false -> begin
()
end)
in (let _52_1365 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_52_1365) with
| (vars, pat_exp_or_typ) -> begin
(let _52_1386 = (All.pipe_right vars (Microsoft_FStar_List.fold_left (fun _52_1368 v -> (match (_52_1368) with
| (env, vars) -> begin
(match (v) with
| Microsoft_FStar_Util.Inl (a) -> begin
(let _52_1376 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1376) with
| (aa, _52_1374, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Microsoft_FStar_Util.Inr (x) -> begin
(let _52_1383 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1383) with
| (xx, _52_1381, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_52_1386) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1391) -> begin
(All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _118_854 = (let _118_853 = (encode_const c)
in (scrutinee, _118_853))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_854))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons (f, _52_1415, args) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (All.pipe_right args (Microsoft_FStar_List.mapi (fun i _52_1424 -> (match (_52_1424) with
| (arg, _52_1423) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _118_857 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _118_857)))
end))))
in (Microsoft_FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1431) -> begin
(All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((Microsoft_FStar_Util.Inr (x), scrutinee))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((Microsoft_FStar_Util.Inl (a), scrutinee))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_52_1448) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons (f, _52_1452, args) -> begin
(let _118_865 = (All.pipe_right args (Microsoft_FStar_List.mapi (fun i _52_1460 -> (match (_52_1460) with
| (arg, _52_1459) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _118_864 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _118_864)))
end))))
in (All.pipe_right _118_865 Microsoft_FStar_List.flatten))
end))
in (let pat_term = (fun _52_1463 -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| Microsoft_FStar_Util.Inl (t) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args = (fun l env -> (let _52_1493 = (All.pipe_right l (Microsoft_FStar_List.fold_left (fun _52_1473 x -> (match (_52_1473) with
| (tms, decls) -> begin
(match (x) with
| (Microsoft_FStar_Util.Inl (t), _52_1478) -> begin
(let _52_1482 = (encode_typ_term t env)
in (match (_52_1482) with
| (t, decls') -> begin
((Microsoft_FStar_Util.Inl (t))::tms, (Microsoft_FStar_List.append decls decls'))
end))
end
| (Microsoft_FStar_Util.Inr (e), _52_1486) -> begin
(let _52_1490 = (encode_exp e env)
in (match (_52_1490) with
| (t, decls') -> begin
((Microsoft_FStar_Util.Inr (t))::tms, (Microsoft_FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_52_1493) with
| (l, decls) -> begin
((Microsoft_FStar_List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _52_1499 = (encode_formula_with_labels phi env)
in (match (_52_1499) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _52_1502 -> begin
(All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun induction_on t env -> (let v_or_t_pat = (fun p -> (match ((let _118_879 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _118_879.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (_52_1509, (Microsoft_FStar_Util.Inl (_52_1516), _52_1519)::(Microsoft_FStar_Util.Inr (e), _52_1513)::[]) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_52_1525, (Microsoft_FStar_Util.Inl (t), _52_1529)::[]) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _52_1535 -> begin
(All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun p -> (match ((let _118_882 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _118_882.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (_52_1539, _52_1551::(Microsoft_FStar_Util.Inr (hd), _52_1548)::(Microsoft_FStar_Util.Inr (tl), _52_1543)::[]) -> begin
(let _118_884 = (v_or_t_pat hd)
in (let _118_883 = (lemma_pats tl)
in (_118_884)::_118_883))
end
| _52_1556 -> begin
[]
end))
in (let _52_1595 = (match ((let _118_885 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _118_885.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _52_1565; Microsoft_FStar_Absyn_Syntax.pos = _52_1563; Microsoft_FStar_Absyn_Syntax.fvs = _52_1561; Microsoft_FStar_Absyn_Syntax.uvs = _52_1559}) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Microsoft_FStar_Util.Inl (pre), _52_1584)::(Microsoft_FStar_Util.Inl (post), _52_1579)::(Microsoft_FStar_Util.Inr (pats), _52_1574)::[] -> begin
(let _118_886 = (lemma_pats pats)
in (binders, pre, post, _118_886))
end
| _52_1588 -> begin
(All.failwith "impos")
end)
end
| _52_1590 -> begin
(All.failwith "Impos")
end)
in (match (_52_1595) with
| (binders, pre, post, patterns) -> begin
(let _52_1602 = (encode_binders None binders env)
in (match (_52_1602) with
| (vars, guards, env, decls, _52_1601) -> begin
(let _52_1618 = (let _118_888 = (All.pipe_right patterns (Microsoft_FStar_List.map (fun _52_12 -> (match (_52_12) with
| (Microsoft_FStar_Util.Inl (t), _52_1607) -> begin
(encode_formula t env)
end
| (Microsoft_FStar_Util.Inr (e), _52_1612) -> begin
(encode_exp e (let _52_1614 = env
in {bindings = _52_1614.bindings; depth = _52_1614.depth; tcenv = _52_1614.tcenv; warn = _52_1614.warn; cache = _52_1614.cache; nolabels = _52_1614.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1614.encode_non_total_function_typ}))
end))))
in (All.pipe_right _118_888 Microsoft_FStar_List.unzip))
in (match (_52_1618) with
| (pats, decls') -> begin
(let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(let _118_890 = (let _118_889 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _118_889 e))
in (_118_890)::pats)
end
| _52_1626 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(let _118_895 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_118_895)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _118_897 = (let _118_896 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _118_896 tl))
in (aux _118_897 vars))
end
| _52_1637 -> begin
pats
end))
in (let _118_898 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _118_898 vars)))
end)
end)
in (let env = (let _52_1639 = env
in {bindings = _52_1639.bindings; depth = _52_1639.depth; tcenv = _52_1639.tcenv; warn = _52_1639.warn; cache = _52_1639.cache; nolabels = true; use_zfuel_name = _52_1639.use_zfuel_name; encode_non_total_function_typ = _52_1639.encode_non_total_function_typ})
in (let _52_1644 = (let _118_899 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _118_899 env))
in (match (_52_1644) with
| (pre, decls'') -> begin
(let _52_1647 = (let _118_900 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _118_900 env))
in (match (_52_1647) with
| (post, decls''') -> begin
(let decls = (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls (Microsoft_FStar_List.flatten decls')) decls'') decls''')
in (let _118_905 = (let _118_904 = (let _118_903 = (let _118_902 = (let _118_901 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_118_901, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_902))
in (pats, vars, _118_903))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_904))
in (_118_905, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f -> (fun l -> (let _52_1668 = (Microsoft_FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| Microsoft_FStar_Util.Inl (t) -> begin
(let _52_1660 = (encode_typ_term t env)
in (match (_52_1660) with
| (t, decls') -> begin
((Microsoft_FStar_List.append decls decls'), t)
end))
end
| Microsoft_FStar_Util.Inr (e) -> begin
(let _52_1665 = (encode_exp e env)
in (match (_52_1665) with
| (e, decls') -> begin
((Microsoft_FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_52_1668) with
| (decls, args) -> begin
(let _118_923 = (f args)
in (_118_923, [], decls))
end))))
in (let enc_prop_c = (fun f -> (fun l -> (let _52_1688 = (Microsoft_FStar_List.fold_right (fun t _52_1676 -> (match (_52_1676) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| Microsoft_FStar_Util.Inl (t) -> begin
(let _52_1682 = (encode_formula_with_labels t env)
in (match (_52_1682) with
| (phi, labs', decls') -> begin
((phi)::phis, (Microsoft_FStar_List.append labs' labs), (Microsoft_FStar_List.append decls' decls))
end))
end
| _52_1684 -> begin
(All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_52_1688) with
| (phis, labs, decls) -> begin
(let _118_939 = (f phis)
in (_118_939, labs, decls))
end))))
in (let const_op = (fun f _52_1691 -> (f, [], []))
in (let un_op = (fun f l -> (let _118_953 = (Microsoft_FStar_List.hd l)
in (All.pipe_left f _118_953)))
in (let bin_op = (fun f _52_13 -> (match (_52_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _52_1702 -> begin
(All.failwith "Impossible")
end))
in (let eq_op = (fun _52_14 -> (match (_52_14) with
| _52_1710::_52_1708::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _52_15 -> (match (_52_15) with
| (Microsoft_FStar_Util.Inl (lhs), _52_1723)::(Microsoft_FStar_Util.Inl (rhs), _52_1718)::[] -> begin
(let _52_1729 = (encode_formula_with_labels rhs env)
in (match (_52_1729) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.True, _52_1732) -> begin
(l1, labs1, decls1)
end
| _52_1736 -> begin
(let _52_1740 = (encode_formula_with_labels lhs env)
in (match (_52_1740) with
| (l2, labs2, decls2) -> begin
(let _118_967 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_118_967, (Microsoft_FStar_List.append labs1 labs2), (Microsoft_FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _52_1742 -> begin
(All.failwith "impossible")
end))
in (let mk_ite = (fun _52_16 -> (match (_52_16) with
| (Microsoft_FStar_Util.Inl (guard), _52_1758)::(Microsoft_FStar_Util.Inl (_then), _52_1753)::(Microsoft_FStar_Util.Inl (_else), _52_1748)::[] -> begin
(let _52_1764 = (encode_formula_with_labels guard env)
in (match (_52_1764) with
| (g, labs1, decls1) -> begin
(let _52_1768 = (encode_formula_with_labels _then env)
in (match (_52_1768) with
| (t, labs2, decls2) -> begin
(let _52_1772 = (encode_formula_with_labels _else env)
in (match (_52_1772) with
| (e, labs3, decls3) -> begin
(let res = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (Microsoft_FStar_List.append (Microsoft_FStar_List.append labs1 labs2) labs3), (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _52_1775 -> begin
(All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _118_979 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _118_979)))
in (let connectives = (let _118_1040 = (let _118_988 = (All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _118_988))
in (let _118_1039 = (let _118_1038 = (let _118_994 = (All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _118_994))
in (let _118_1037 = (let _118_1036 = (let _118_1035 = (let _118_1003 = (All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _118_1003))
in (let _118_1034 = (let _118_1033 = (let _118_1032 = (let _118_1012 = (All.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _118_1012))
in (let _118_1031 = (let _118_1030 = (let _118_1018 = (All.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _118_1018))
in (_118_1030)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_118_1032)::_118_1031))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_118_1033)
in (_118_1035)::_118_1034))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_118_1036)
in (_118_1038)::_118_1037))
in (_118_1040)::_118_1039))
in (let fallback = (fun phi -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _52_1793 = (encode_formula_with_labels phi' env)
in (match (_52_1793) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _118_1043 = (varops.fresh "label")
in (_118_1043, Microsoft_FStar_ToSMT_Term.Bool_sort))
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _52_1804; Microsoft_FStar_Absyn_Syntax.pos = _52_1802; Microsoft_FStar_Absyn_Syntax.fvs = _52_1800; Microsoft_FStar_Absyn_Syntax.uvs = _52_1798}, _52_1819::(Microsoft_FStar_Util.Inr (l), _52_1816)::(Microsoft_FStar_Util.Inl (phi), _52_1811)::[]) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _52_1825 = (encode_exp l env)
in (match (_52_1825) with
| (e, decls) -> begin
(let _52_1828 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_52_1828) with
| (f, decls') -> begin
(f, [], (Microsoft_FStar_List.append decls decls'))
end))
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _52_1830 -> begin
(let _52_1833 = (encode_typ_term phi env)
in (match (_52_1833) with
| (tt, decls) -> begin
(let _118_1044 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_118_1044, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _52_1845 = (encode_binders None bs env)
in (match (_52_1845) with
| (vars, guards, env, decls, _52_1844) -> begin
(let _52_1861 = (let _118_1054 = (All.pipe_right ps (Microsoft_FStar_List.map (fun _52_17 -> (match (_52_17) with
| (Microsoft_FStar_Util.Inl (t), _52_1850) -> begin
(encode_typ_term t env)
end
| (Microsoft_FStar_Util.Inr (e), _52_1855) -> begin
(encode_exp e (let _52_1857 = env
in {bindings = _52_1857.bindings; depth = _52_1857.depth; tcenv = _52_1857.tcenv; warn = _52_1857.warn; cache = _52_1857.cache; nolabels = _52_1857.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1857.encode_non_total_function_typ}))
end))))
in (All.pipe_right _118_1054 Microsoft_FStar_List.unzip))
in (match (_52_1861) with
| (pats, decls') -> begin
(let _52_1865 = (encode_formula_with_labels body env)
in (match (_52_1865) with
| (body, labs, decls'') -> begin
(let _118_1055 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _118_1055, body, labs, (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls (Microsoft_FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _52_1866 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_1056 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Microsoft_FStar_Util.fprint1 ">>>> Destructing as formula ... %s\n" _118_1056))
end
| false -> begin
()
end)
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((All.pipe_right connectives (Microsoft_FStar_List.tryFind (fun _52_1878 -> (match (_52_1878) with
| (l, _52_1877) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_52_1881, f) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _52_1891 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_1073 = (All.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Microsoft_FStar_Util.fprint1 ">>>> Got QALL [%s]\n" _118_1073))
end
| false -> begin
()
end)
in (let _52_1899 = (encode_q_body env vars pats body)
in (match (_52_1899) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _118_1076 = (let _118_1075 = (let _118_1074 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _118_1074))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1075))
in (_118_1076, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _52_1912 = (encode_q_body env vars pats body)
in (match (_52_1912) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _118_1079 = (let _118_1078 = (let _118_1077 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _118_1077))
in (Microsoft_FStar_ToSMT_Term.mkExists _118_1078))
in (_118_1079, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  Prims.string  ->  Microsoft_FStar_ToSMT_Term.decl Prims.list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  Prims.bool}

let is_Mkprims_t = (fun _ -> (All.failwith "Not yet implemented:is_Mkprims_t"))

let prims = (let _52_1918 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_52_1918) with
| (asym, a) -> begin
(let _52_1921 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1921) with
| (xsym, x) -> begin
(let _52_1924 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1924) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body -> (fun x -> (let t1 = (let _118_1122 = (let _118_1121 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _118_1121))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1122))
in (let vname_decl = (let _118_1124 = (let _118_1123 = (All.pipe_right vars (Microsoft_FStar_List.map Prims.snd))
in (x, _118_1123, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_1124))
in (let _118_1130 = (let _118_1129 = (let _118_1128 = (let _118_1127 = (let _118_1126 = (let _118_1125 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _118_1125))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1126))
in (_118_1127, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1128))
in (_118_1129)::[])
in (vname_decl)::_118_1130)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _118_1290 = (let _118_1139 = (let _118_1138 = (let _118_1137 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1137))
in (quant axy _118_1138))
in (Microsoft_FStar_Absyn_Const.op_Eq, _118_1139))
in (let _118_1289 = (let _118_1288 = (let _118_1146 = (let _118_1145 = (let _118_1144 = (let _118_1143 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _118_1143))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1144))
in (quant axy _118_1145))
in (Microsoft_FStar_Absyn_Const.op_notEq, _118_1146))
in (let _118_1287 = (let _118_1286 = (let _118_1155 = (let _118_1154 = (let _118_1153 = (let _118_1152 = (let _118_1151 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1150 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1151, _118_1150)))
in (Microsoft_FStar_ToSMT_Term.mkLT _118_1152))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1153))
in (quant xy _118_1154))
in (Microsoft_FStar_Absyn_Const.op_LT, _118_1155))
in (let _118_1285 = (let _118_1284 = (let _118_1164 = (let _118_1163 = (let _118_1162 = (let _118_1161 = (let _118_1160 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1159 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1160, _118_1159)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _118_1161))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1162))
in (quant xy _118_1163))
in (Microsoft_FStar_Absyn_Const.op_LTE, _118_1164))
in (let _118_1283 = (let _118_1282 = (let _118_1173 = (let _118_1172 = (let _118_1171 = (let _118_1170 = (let _118_1169 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1168 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1169, _118_1168)))
in (Microsoft_FStar_ToSMT_Term.mkGT _118_1170))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1171))
in (quant xy _118_1172))
in (Microsoft_FStar_Absyn_Const.op_GT, _118_1173))
in (let _118_1281 = (let _118_1280 = (let _118_1182 = (let _118_1181 = (let _118_1180 = (let _118_1179 = (let _118_1178 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1177 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1178, _118_1177)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _118_1179))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1180))
in (quant xy _118_1181))
in (Microsoft_FStar_Absyn_Const.op_GTE, _118_1182))
in (let _118_1279 = (let _118_1278 = (let _118_1191 = (let _118_1190 = (let _118_1189 = (let _118_1188 = (let _118_1187 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1186 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1187, _118_1186)))
in (Microsoft_FStar_ToSMT_Term.mkSub _118_1188))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _118_1189))
in (quant xy _118_1190))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _118_1191))
in (let _118_1277 = (let _118_1276 = (let _118_1198 = (let _118_1197 = (let _118_1196 = (let _118_1195 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _118_1195))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _118_1196))
in (quant qx _118_1197))
in (Microsoft_FStar_Absyn_Const.op_Minus, _118_1198))
in (let _118_1275 = (let _118_1274 = (let _118_1207 = (let _118_1206 = (let _118_1205 = (let _118_1204 = (let _118_1203 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1202 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1203, _118_1202)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _118_1204))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _118_1205))
in (quant xy _118_1206))
in (Microsoft_FStar_Absyn_Const.op_Addition, _118_1207))
in (let _118_1273 = (let _118_1272 = (let _118_1216 = (let _118_1215 = (let _118_1214 = (let _118_1213 = (let _118_1212 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1211 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1212, _118_1211)))
in (Microsoft_FStar_ToSMT_Term.mkMul _118_1213))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _118_1214))
in (quant xy _118_1215))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _118_1216))
in (let _118_1271 = (let _118_1270 = (let _118_1225 = (let _118_1224 = (let _118_1223 = (let _118_1222 = (let _118_1221 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1220 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1221, _118_1220)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _118_1222))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _118_1223))
in (quant xy _118_1224))
in (Microsoft_FStar_Absyn_Const.op_Division, _118_1225))
in (let _118_1269 = (let _118_1268 = (let _118_1234 = (let _118_1233 = (let _118_1232 = (let _118_1231 = (let _118_1230 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1229 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_118_1230, _118_1229)))
in (Microsoft_FStar_ToSMT_Term.mkMod _118_1231))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _118_1232))
in (quant xy _118_1233))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _118_1234))
in (let _118_1267 = (let _118_1266 = (let _118_1243 = (let _118_1242 = (let _118_1241 = (let _118_1240 = (let _118_1239 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _118_1238 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_118_1239, _118_1238)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _118_1240))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1241))
in (quant xy _118_1242))
in (Microsoft_FStar_Absyn_Const.op_And, _118_1243))
in (let _118_1265 = (let _118_1264 = (let _118_1252 = (let _118_1251 = (let _118_1250 = (let _118_1249 = (let _118_1248 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _118_1247 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_118_1248, _118_1247)))
in (Microsoft_FStar_ToSMT_Term.mkOr _118_1249))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1250))
in (quant xy _118_1251))
in (Microsoft_FStar_Absyn_Const.op_Or, _118_1252))
in (let _118_1263 = (let _118_1262 = (let _118_1259 = (let _118_1258 = (let _118_1257 = (let _118_1256 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _118_1256))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_1257))
in (quant qx _118_1258))
in (Microsoft_FStar_Absyn_Const.op_Negation, _118_1259))
in (_118_1262)::[])
in (_118_1264)::_118_1263))
in (_118_1266)::_118_1265))
in (_118_1268)::_118_1267))
in (_118_1270)::_118_1269))
in (_118_1272)::_118_1271))
in (_118_1274)::_118_1273))
in (_118_1276)::_118_1275))
in (_118_1278)::_118_1277))
in (_118_1280)::_118_1279))
in (_118_1282)::_118_1281))
in (_118_1284)::_118_1283))
in (_118_1286)::_118_1285))
in (_118_1288)::_118_1287))
in (_118_1290)::_118_1289))
in (let mk = (fun l v -> (let _118_1322 = (All.pipe_right prims (Microsoft_FStar_List.filter (fun _52_1944 -> (match (_52_1944) with
| (l', _52_1943) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (All.pipe_right _118_1322 (Microsoft_FStar_List.collect (fun _52_1948 -> (match (_52_1948) with
| (_52_1946, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (All.pipe_right prims (Microsoft_FStar_Util.for_some (fun _52_1954 -> (match (_52_1954) with
| (l', _52_1953) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms = (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let mk_unit = (fun _52_1960 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let _118_1354 = (let _118_1345 = (let _118_1344 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_118_1344, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1345))
in (let _118_1353 = (let _118_1352 = (let _118_1351 = (let _118_1350 = (let _118_1349 = (let _118_1348 = (let _118_1347 = (let _118_1346 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _118_1346))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1347))
in ((typing_pred)::[], (xx)::[], _118_1348))
in (mkForall_fuel _118_1349))
in (_118_1350, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1351))
in (_118_1352)::[])
in (_118_1354)::_118_1353))))
in (let mk_bool = (fun _52_1965 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _118_1374 = (let _118_1364 = (let _118_1363 = (let _118_1362 = (let _118_1361 = (let _118_1360 = (let _118_1359 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _118_1359))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1360))
in ((typing_pred)::[], (xx)::[], _118_1361))
in (mkForall_fuel _118_1362))
in (_118_1363, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1364))
in (let _118_1373 = (let _118_1372 = (let _118_1371 = (let _118_1370 = (let _118_1369 = (let _118_1368 = (let _118_1365 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_118_1365)::[])
in (let _118_1367 = (let _118_1366 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _118_1366 tt))
in (_118_1368, (bb)::[], _118_1367)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1369))
in (_118_1370, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1371))
in (_118_1372)::[])
in (_118_1374)::_118_1373))))))
in (let mk_int = (fun _52_1972 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _118_1386 = (let _118_1385 = (let _118_1384 = (let _118_1383 = (let _118_1382 = (let _118_1381 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _118_1380 = (let _118_1379 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_118_1379)::[])
in (_118_1381)::_118_1380))
in (tt)::_118_1382)
in (tt)::_118_1383)
in ("Prims.Precedes", _118_1384))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1385))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _118_1386))
in (let precedes_y_x = (let _118_1387 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _118_1387))
in (let _118_1428 = (let _118_1393 = (let _118_1392 = (let _118_1391 = (let _118_1390 = (let _118_1389 = (let _118_1388 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _118_1388))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1389))
in ((typing_pred)::[], (xx)::[], _118_1390))
in (mkForall_fuel _118_1391))
in (_118_1392, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1393))
in (let _118_1427 = (let _118_1426 = (let _118_1400 = (let _118_1399 = (let _118_1398 = (let _118_1397 = (let _118_1394 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_118_1394)::[])
in (let _118_1396 = (let _118_1395 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _118_1395 tt))
in (_118_1397, (bb)::[], _118_1396)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1398))
in (_118_1399, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1400))
in (let _118_1425 = (let _118_1424 = (let _118_1423 = (let _118_1422 = (let _118_1421 = (let _118_1420 = (let _118_1419 = (let _118_1418 = (let _118_1417 = (let _118_1416 = (let _118_1415 = (let _118_1414 = (let _118_1403 = (let _118_1402 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _118_1401 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_118_1402, _118_1401)))
in (Microsoft_FStar_ToSMT_Term.mkGT _118_1403))
in (let _118_1413 = (let _118_1412 = (let _118_1406 = (let _118_1405 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _118_1404 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_118_1405, _118_1404)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _118_1406))
in (let _118_1411 = (let _118_1410 = (let _118_1409 = (let _118_1408 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _118_1407 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_118_1408, _118_1407)))
in (Microsoft_FStar_ToSMT_Term.mkLT _118_1409))
in (_118_1410)::[])
in (_118_1412)::_118_1411))
in (_118_1414)::_118_1413))
in (typing_pred_y)::_118_1415)
in (typing_pred)::_118_1416)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _118_1417))
in (_118_1418, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1419))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _118_1420))
in (mkForall_fuel _118_1421))
in (_118_1422, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1423))
in (_118_1424)::[])
in (_118_1426)::_118_1425))
in (_118_1428)::_118_1427)))))))))))
in (let mk_int_alias = (fun _52_1984 tt -> (let _118_1437 = (let _118_1436 = (let _118_1435 = (let _118_1434 = (let _118_1433 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _118_1433))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_1434))
in (_118_1435, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1436))
in (_118_1437)::[]))
in (let mk_str = (fun _52_1988 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _118_1457 = (let _118_1447 = (let _118_1446 = (let _118_1445 = (let _118_1444 = (let _118_1443 = (let _118_1442 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _118_1442))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1443))
in ((typing_pred)::[], (xx)::[], _118_1444))
in (mkForall_fuel _118_1445))
in (_118_1446, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1447))
in (let _118_1456 = (let _118_1455 = (let _118_1454 = (let _118_1453 = (let _118_1452 = (let _118_1451 = (let _118_1448 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_118_1448)::[])
in (let _118_1450 = (let _118_1449 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _118_1449 tt))
in (_118_1451, (bb)::[], _118_1450)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1452))
in (_118_1453, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1454))
in (_118_1455)::[])
in (_118_1457)::_118_1456))))))
in (let mk_ref = (fun reft_name _52_1996 -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _118_1464 = (let _118_1463 = (let _118_1462 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_118_1462)::[])
in (reft_name, _118_1463))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1464))
in (let refb = (let _118_1467 = (let _118_1466 = (let _118_1465 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_118_1465)::[])
in (reft_name, _118_1466))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1467))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _118_1486 = (let _118_1473 = (let _118_1472 = (let _118_1471 = (let _118_1470 = (let _118_1469 = (let _118_1468 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _118_1468))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1469))
in ((typing_pred)::[], (xx)::(aa)::[], _118_1470))
in (mkForall_fuel _118_1471))
in (_118_1472, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1473))
in (let _118_1485 = (let _118_1484 = (let _118_1483 = (let _118_1482 = (let _118_1481 = (let _118_1480 = (let _118_1479 = (let _118_1478 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _118_1477 = (let _118_1476 = (let _118_1475 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _118_1474 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_118_1475, _118_1474)))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_1476))
in (_118_1478, _118_1477)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1479))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _118_1480))
in (mkForall_fuel' 2 _118_1481))
in (_118_1482, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1483))
in (_118_1484)::[])
in (_118_1486)::_118_1485))))))))))
in (let mk_false_interp = (fun _52_2006 false_tm -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _118_1493 = (let _118_1492 = (let _118_1491 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_118_1491, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1492))
in (_118_1493)::[])))
in (let mk_and_interp = (fun conj _52_2012 -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1500 = (let _118_1499 = (let _118_1498 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_118_1498)::[])
in ("Valid", _118_1499))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1500))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1507 = (let _118_1506 = (let _118_1505 = (let _118_1504 = (let _118_1503 = (let _118_1502 = (let _118_1501 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_118_1501, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1502))
in ((valid)::[], (aa)::(bb)::[], _118_1503))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1504))
in (_118_1505, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1506))
in (_118_1507)::[])))))))))
in (let mk_or_interp = (fun disj _52_2023 -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1514 = (let _118_1513 = (let _118_1512 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_118_1512)::[])
in ("Valid", _118_1513))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1514))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1521 = (let _118_1520 = (let _118_1519 = (let _118_1518 = (let _118_1517 = (let _118_1516 = (let _118_1515 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_118_1515, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1516))
in ((valid)::[], (aa)::(bb)::[], _118_1517))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1518))
in (_118_1519, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1520))
in (_118_1521)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _118_1528 = (let _118_1527 = (let _118_1526 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_118_1526)::[])
in ("Valid", _118_1527))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1528))
in (let _118_1535 = (let _118_1534 = (let _118_1533 = (let _118_1532 = (let _118_1531 = (let _118_1530 = (let _118_1529 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_118_1529, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1530))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _118_1531))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1532))
in (_118_1533, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1534))
in (_118_1535)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1542 = (let _118_1541 = (let _118_1540 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_118_1540)::[])
in ("Valid", _118_1541))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1542))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1549 = (let _118_1548 = (let _118_1547 = (let _118_1546 = (let _118_1545 = (let _118_1544 = (let _118_1543 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_118_1543, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1544))
in ((valid)::[], (aa)::(bb)::[], _118_1545))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1546))
in (_118_1547, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1548))
in (_118_1549)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1556 = (let _118_1555 = (let _118_1554 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_118_1554)::[])
in ("Valid", _118_1555))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1556))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1563 = (let _118_1562 = (let _118_1561 = (let _118_1560 = (let _118_1559 = (let _118_1558 = (let _118_1557 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_118_1557, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1558))
in ((valid)::[], (aa)::(bb)::[], _118_1559))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1560))
in (_118_1561, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1562))
in (_118_1563)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _118_1570 = (let _118_1569 = (let _118_1568 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_118_1568)::[])
in ("Valid", _118_1569))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1570))
in (let valid_b_x = (let _118_1573 = (let _118_1572 = (let _118_1571 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_118_1571)::[])
in ("Valid", _118_1572))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1573))
in (let _118_1586 = (let _118_1585 = (let _118_1584 = (let _118_1583 = (let _118_1582 = (let _118_1581 = (let _118_1580 = (let _118_1579 = (let _118_1578 = (let _118_1574 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1574)::[])
in (let _118_1577 = (let _118_1576 = (let _118_1575 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1575, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1576))
in (_118_1578, (xx)::[], _118_1577)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1579))
in (_118_1580, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1581))
in ((valid)::[], (aa)::(bb)::[], _118_1582))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1583))
in (_118_1584, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1585))
in (_118_1586)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _118_1593 = (let _118_1592 = (let _118_1591 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_118_1591)::[])
in ("Valid", _118_1592))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1593))
in (let valid_b_x = (let _118_1596 = (let _118_1595 = (let _118_1594 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_118_1594)::[])
in ("Valid", _118_1595))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1596))
in (let _118_1609 = (let _118_1608 = (let _118_1607 = (let _118_1606 = (let _118_1605 = (let _118_1604 = (let _118_1603 = (let _118_1602 = (let _118_1601 = (let _118_1597 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1597)::[])
in (let _118_1600 = (let _118_1599 = (let _118_1598 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1598, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1599))
in (_118_1601, (xx)::[], _118_1600)))
in (Microsoft_FStar_ToSMT_Term.mkExists _118_1602))
in (_118_1603, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1604))
in ((valid)::[], (aa)::(bb)::[], _118_1605))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1606))
in (_118_1607, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1608))
in (_118_1609)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1616 = (let _118_1615 = (let _118_1614 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_118_1614)::[])
in ("Valid", _118_1615))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1616))
in (let valid_a_b = (let _118_1619 = (let _118_1618 = (let _118_1617 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_118_1617)::[])
in ("Valid", _118_1618))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1619))
in (let _118_1632 = (let _118_1631 = (let _118_1630 = (let _118_1629 = (let _118_1628 = (let _118_1627 = (let _118_1626 = (let _118_1625 = (let _118_1624 = (let _118_1620 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1620)::[])
in (let _118_1623 = (let _118_1622 = (let _118_1621 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1621, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1622))
in (_118_1624, (bb)::[], _118_1623)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1625))
in (_118_1626, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1627))
in ((valid)::[], (kk)::(aa)::[], _118_1628))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1629))
in (_118_1630, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1631))
in (_118_1632)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1639 = (let _118_1638 = (let _118_1637 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_118_1637)::[])
in ("Valid", _118_1638))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1639))
in (let valid_a_b = (let _118_1642 = (let _118_1641 = (let _118_1640 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_118_1640)::[])
in ("Valid", _118_1641))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1642))
in (let _118_1655 = (let _118_1654 = (let _118_1653 = (let _118_1652 = (let _118_1651 = (let _118_1650 = (let _118_1649 = (let _118_1648 = (let _118_1647 = (let _118_1643 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1643)::[])
in (let _118_1646 = (let _118_1645 = (let _118_1644 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1644, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1645))
in (_118_1647, (bb)::[], _118_1646)))
in (Microsoft_FStar_ToSMT_Term.mkExists _118_1648))
in (_118_1649, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _118_1650))
in ((valid)::[], (kk)::(aa)::[], _118_1651))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1652))
in (_118_1653, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1654))
in (_118_1655)::[]))))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.false_lid, mk_false_interp))::((Microsoft_FStar_Absyn_Const.and_lid, mk_and_interp))::((Microsoft_FStar_Absyn_Const.or_lid, mk_or_interp))::((Microsoft_FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp_interp))::((Microsoft_FStar_Absyn_Const.iff_lid, mk_iff_interp))::((Microsoft_FStar_Absyn_Const.forall_lid, mk_forall_interp))::((Microsoft_FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((Microsoft_FStar_Util.find_opt (fun _52_2116 -> (match (_52_2116) with
| (l, _52_2115) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_52_2119, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun env se -> (let _52_2125 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_1798 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (All.pipe_left (Microsoft_FStar_Util.fprint1 ">>>>Encoding [%s]\n") _118_1798))
end
| false -> begin
()
end)
in (let nm = (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end)
in (let _52_2133 = (encode_sigelt' env se)
in (match (_52_2133) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _118_1801 = (let _118_1800 = (let _118_1799 = (Microsoft_FStar_Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_118_1799))
in (_118_1800)::[])
in (_118_1801, e))
end
| _52_2136 -> begin
(let _118_1808 = (let _118_1807 = (let _118_1803 = (let _118_1802 = (Microsoft_FStar_Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_118_1802))
in (_118_1803)::g)
in (let _118_1806 = (let _118_1805 = (let _118_1804 = (Microsoft_FStar_Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_118_1804))
in (_118_1805)::[])
in (Microsoft_FStar_List.append _118_1807 _118_1806)))
in (_118_1808, e))
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((Microsoft_FStar_Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.pure_") || (Microsoft_FStar_Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.ex_")) || (Microsoft_FStar_Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.st_")) || (Microsoft_FStar_Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (_52_2142, _52_2144, _52_2146, _52_2148, Microsoft_FStar_Absyn_Syntax.Effect::[], _52_2152) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _52_2157, _52_2159, _52_2161, _52_2163, _52_2165) when (should_skip lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _52_2170, _52_2172, _52_2174, _52_2176, _52_2178) when (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.b2t_lid) -> begin
(let _52_2184 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2184) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _118_1813 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _118_1813))
in (let decls = (let _118_1821 = (let _118_1820 = (let _118_1819 = (let _118_1818 = (let _118_1817 = (let _118_1816 = (let _118_1815 = (let _118_1814 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _118_1814))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_1815))
in ((valid_b2t_x)::[], (xx)::[], _118_1816))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1817))
in (_118_1818, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1819))
in (_118_1820)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_118_1821)
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _52_2192, t, tags, _52_2196) -> begin
(let _52_2202 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2202) with
| (tname, ttok, env) -> begin
(let _52_2211 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((Microsoft_FStar_List.append tps tps'), body)
end
| _52_2208 -> begin
(tps, t)
end)
in (match (_52_2211) with
| (tps, t) -> begin
(let _52_2218 = (encode_binders None tps env)
in (match (_52_2218) with
| (vars, guards, env', binder_decls, _52_2217) -> begin
(let tok_app = (let _118_1822 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _118_1822 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _118_1824 = (let _118_1823 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _118_1823))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1824))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _52_2224 -> begin
(let _118_1826 = (let _118_1825 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _118_1825))
in (_118_1826)::[])
end)
in (let decls = (let _118_1837 = (let _118_1830 = (let _118_1829 = (let _118_1828 = (let _118_1827 = (Microsoft_FStar_List.map Prims.snd vars)
in (tname, _118_1827, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_1828))
in (_118_1829)::(tok_decl)::[])
in (Microsoft_FStar_List.append _118_1830 fresh_tok))
in (let _118_1836 = (let _118_1835 = (let _118_1834 = (let _118_1833 = (let _118_1832 = (let _118_1831 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _118_1831))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1832))
in (_118_1833, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1834))
in (_118_1835)::[])
in (Microsoft_FStar_List.append _118_1837 _118_1836)))
in (let t = (whnf env t)
in (let _52_2236 = (match ((All.pipe_right tags (Microsoft_FStar_Util.for_some (fun _52_18 -> (match (_52_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _52_2231 -> begin
false
end))))) with
| true -> begin
(let _118_1840 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _118_1839 = (encode_formula t env')
in (_118_1840, _118_1839)))
end
| false -> begin
(let _118_1841 = (encode_typ_term t env')
in (app, _118_1841))
end)
in (match (_52_2236) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _118_1848 = (let _118_1847 = (let _118_1846 = (let _118_1845 = (let _118_1844 = (let _118_1843 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _118_1842 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_118_1843, _118_1842)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1844))
in ((def)::[], vars, _118_1845))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1846))
in (_118_1847, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1848))
in (let kindingAx = (let _52_2240 = (let _118_1849 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _118_1849 env' app))
in (match (_52_2240) with
| (k, decls) -> begin
(let _118_1857 = (let _118_1856 = (let _118_1855 = (let _118_1854 = (let _118_1853 = (let _118_1852 = (let _118_1851 = (let _118_1850 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_118_1850, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1851))
in ((app)::[], vars, _118_1852))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1853))
in (_118_1854, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1855))
in (_118_1856)::[])
in (Microsoft_FStar_List.append decls _118_1857))
end))
in (let g = (let _118_1858 = (primitive_type_axioms lid tname app)
in (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _118_1858))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _52_2247) -> begin
(let tt = (whnf env t)
in (let _52_2253 = (encode_free_var env lid t tt quals)
in (match (_52_2253) with
| (decls, env) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && ((All.pipe_right quals (Microsoft_FStar_List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))) with
| true -> begin
(let _118_1860 = (let _118_1859 = (encode_smt_lemma env lid t)
in (Microsoft_FStar_List.append decls _118_1859))
in (_118_1860, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume (l, f, _52_2257, _52_2259) -> begin
(let _52_2264 = (encode_formula f env)
in (match (_52_2264) with
| (f, decls) -> begin
(let g = (let _118_1865 = (let _118_1864 = (let _118_1863 = (let _118_1862 = (let _118_1861 = (Microsoft_FStar_Absyn_Print.sli l)
in (Microsoft_FStar_Util.format1 "Assumption: %s" _118_1861))
in Some (_118_1862))
in (f, _118_1863))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1864))
in (_118_1865)::[])
in ((Microsoft_FStar_List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _52_2270, datas, quals, _52_2274) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _52_2280 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2280) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (t, _52_2283, _52_2285, _52_2287, _52_2289, _52_2291, _52_2293) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let _118_1867 = (let _118_1866 = (primitive_type_axioms t tname tsym)
in (decl)::_118_1866)
in (_118_1867, (push_free_tvar env t tname (Some (tsym))))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _52_2303, datas, quals, _52_2307) -> begin
(let is_logical = (All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _52_19 -> (match (_52_19) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _52_2314 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(let _52_2324 = c
in (match (_52_2324) with
| (name, args, _52_2321, _52_2323) -> begin
(let _118_1873 = (let _118_1872 = (let _118_1871 = (All.pipe_right args (Microsoft_FStar_List.map Prims.snd))
in (name, _118_1871, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_1872))
in (_118_1873)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun tapp vars -> (match ((((Microsoft_FStar_List.length datas) = 0) || (All.pipe_right datas (Microsoft_FStar_Util.for_some (fun l -> (let _118_1879 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (All.pipe_right _118_1879 Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _52_2331 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2331) with
| (xxsym, xx) -> begin
(let _52_2374 = (All.pipe_right datas (Microsoft_FStar_List.fold_left (fun _52_2334 l -> (match (_52_2334) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _52_2344 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_52_2344) with
| (args, res) -> begin
(let indices = (match ((let _118_1882 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _118_1882.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (_52_2346, indices) -> begin
indices
end
| _52_2351 -> begin
[]
end)
in (let env = (All.pipe_right args (Microsoft_FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| Microsoft_FStar_Util.Inl (a) -> begin
(let _118_1887 = (let _118_1886 = (let _118_1885 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_118_1885, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1886))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _118_1887))
end
| Microsoft_FStar_Util.Inr (x) -> begin
(let _118_1890 = (let _118_1889 = (let _118_1888 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_118_1888, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1889))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _118_1890))
end)) env))
in (let _52_2362 = (encode_args indices env)
in (match (_52_2362) with
| (indices, decls') -> begin
(let _52_2363 = (match (((Microsoft_FStar_List.length indices) <> (Microsoft_FStar_List.length vars))) with
| true -> begin
(All.failwith "Impossible")
end
| false -> begin
()
end)
in (let eqs = (let _118_1897 = (Microsoft_FStar_List.map2 (fun v a -> (match (a) with
| Microsoft_FStar_Util.Inl (a) -> begin
(let _118_1894 = (let _118_1893 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_118_1893, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_1894))
end
| Microsoft_FStar_Util.Inr (a) -> begin
(let _118_1896 = (let _118_1895 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_118_1895, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_1896))
end)) vars indices)
in (All.pipe_right _118_1897 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _118_1902 = (let _118_1901 = (let _118_1900 = (let _118_1899 = (let _118_1898 = (mk_data_tester env l xx)
in (_118_1898, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _118_1899))
in (out, _118_1900))
in (Microsoft_FStar_ToSMT_Term.mkOr _118_1901))
in (_118_1902, (Microsoft_FStar_List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_52_2374) with
| (data_ax, decls) -> begin
(let _52_2377 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2377) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _118_1903 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _118_1903 xx tapp))
in (let _118_1910 = (let _118_1909 = (let _118_1908 = (let _118_1907 = (let _118_1906 = (let _118_1905 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _118_1904 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _118_1905, _118_1904)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1906))
in (_118_1907, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1908))
in (_118_1909)::[])
in (Microsoft_FStar_List.append decls _118_1910)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _52_2389 = (match ((let _118_1911 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _118_1911.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _52_2385 -> begin
(false, [], k)
end)
in (match (_52_2389) with
| (is_kind_arrow, formals, res) -> begin
(let _52_2396 = (encode_binders None formals env)
in (match (_52_2396) with
| (vars, guards, env', binder_decls, _52_2395) -> begin
(let projection_axioms = (fun tapp vars -> (match ((All.pipe_right quals (Microsoft_FStar_Util.find_opt (fun _52_20 -> (match (_52_20) with
| Microsoft_FStar_Absyn_Syntax.Projector (_52_2402) -> begin
true
end
| _52_2405 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector (d, Microsoft_FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _52_21 -> (match (_52_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| Microsoft_FStar_Util.Inl (_52_2420) -> begin
(projectee (i + 1) tl)
end
| Microsoft_FStar_Util.Inr (x) -> begin
(match ((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = "projectee")) with
| true -> begin
i
end
| false -> begin
(projectee (i + 1) tl)
end)
end)
end))
in (let projectee_pos = (projectee 0 formals)
in (let _52_2435 = (match ((Microsoft_FStar_Util.first_N projectee_pos vars)) with
| (_52_2426, xx::suffix) -> begin
(xx, suffix)
end
| _52_2432 -> begin
(All.failwith "impossible")
end)
in (match (_52_2435) with
| (xx, suffix) -> begin
(let dproj_app = (let _118_1925 = (let _118_1924 = (let _118_1923 = (mk_typ_projector_name d a)
in (let _118_1922 = (let _118_1921 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_118_1921)::[])
in (_118_1923, _118_1922)))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1924))
in (mk_ApplyT _118_1925 suffix))
in (let _118_1930 = (let _118_1929 = (let _118_1928 = (let _118_1927 = (let _118_1926 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _118_1926))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1927))
in (_118_1928, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1929))
in (_118_1930)::[]))
end))))
end
| _52_2438 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _52_2444 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2444) with
| (xxsym, xx) -> begin
(let _52_2447 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2447) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _118_1943 = (let _118_1942 = (let _118_1941 = (let _118_1940 = (let _118_1939 = (let _118_1938 = (let _118_1937 = (let _118_1936 = (let _118_1935 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _118_1935))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_1936))
in (xx_has_type, _118_1937))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1938))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _118_1939))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1940))
in (_118_1941, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1942))
in (_118_1943)::[]))
end))
end)))
in (let _52_2452 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2452) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _118_1945 = (let _118_1944 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _118_1944))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_1945))
in (let _52_2477 = (let tname_decl = (let _118_1949 = (let _118_1948 = (All.pipe_right vars (Microsoft_FStar_List.map (fun _52_2458 -> (match (_52_2458) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _118_1947 = (varops.next_id ())
in (tname, _118_1948, Microsoft_FStar_ToSMT_Term.Type_sort, _118_1947)))
in (constructor_or_logic_type_decl _118_1949))
in (let _52_2474 = (match (vars) with
| [] -> begin
(let _118_1953 = (let _118_1952 = (let _118_1951 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (All.pipe_left (fun _118_1950 -> Some (_118_1950)) _118_1951))
in (push_free_tvar env t tname _118_1952))
in ([], _118_1953))
end
| _52_2462 -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _118_1954 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _118_1954))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _52_22 -> (match (_52_22) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2469 -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _118_1959 = (let _118_1958 = (let _118_1957 = (let _118_1956 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _118_1956))
in (Microsoft_FStar_ToSMT_Term.mkForall' _118_1957))
in (_118_1958, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1959))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_52_2474) with
| (tok_decls, env) -> begin
((Microsoft_FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_52_2477) with
| (decls, env) -> begin
(let kindingAx = (let _52_2480 = (encode_knd res env' tapp)
in (match (_52_2480) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _118_1963 = (let _118_1962 = (let _118_1961 = (let _118_1960 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_1960))
in (_118_1961, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1962))
in (_118_1963)::[])
end
| false -> begin
[]
end)
in (let _118_1969 = (let _118_1968 = (let _118_1967 = (let _118_1966 = (let _118_1965 = (let _118_1964 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _118_1964))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_1965))
in (_118_1966, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_1967))
in (_118_1968)::[])
in (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls karr) _118_1969)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _118_1970 = (projection_axioms tapp vars)
in (Microsoft_FStar_List.append kindingAx _118_1970))
end
| false -> begin
(let _118_1977 = (let _118_1975 = (let _118_1973 = (let _118_1971 = (primitive_type_axioms t tname tapp)
in (Microsoft_FStar_List.append kindingAx _118_1971))
in (let _118_1972 = (inversion_axioms tapp vars)
in (Microsoft_FStar_List.append _118_1973 _118_1972)))
in (let _118_1974 = (projection_axioms tapp vars)
in (Microsoft_FStar_List.append _118_1975 _118_1974)))
in (let _118_1976 = (pretype_axioms tapp vars)
in (Microsoft_FStar_List.append _118_1977 _118_1976)))
end)
in (let g = (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (d, _52_2487, _52_2489, _52_2491, _52_2493, _52_2495) when (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon (d, t, _52_2501, quals, _52_2504, drange) -> begin
(let _52_2511 = (new_term_constant_and_tok_from_lid env d)
in (match (_52_2511) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _52_2520 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_52_2520) with
| (formals, t_res) -> begin
(let _52_2523 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2523) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _52_2530 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_52_2530) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (All.pipe_right names (Microsoft_FStar_List.map (fun _52_23 -> (match (_52_23) with
| Microsoft_FStar_Util.Inl (a) -> begin
(let _118_1979 = (mk_typ_projector_name d a)
in (_118_1979, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Microsoft_FStar_Util.Inr (x) -> begin
(let _118_1980 = (mk_term_projector_name d x)
in (_118_1980, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _118_1982 = (let _118_1981 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _118_1981))
in (All.pipe_right _118_1982 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _52_2544 = (encode_typ_pred None t env ddtok_tm)
in (match (_52_2544) with
| (tok_typing, decls3) -> begin
(let _52_2551 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_52_2551) with
| (vars', guards', env'', decls_formals, _52_2550) -> begin
(let _52_2556 = (let xvars = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_52_2556) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _52_2560 -> begin
(let _118_1984 = (let _118_1983 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _118_1983))
in (_118_1984)::[])
end)
in (let encode_elim = (fun _52_2563 -> (match (()) with
| () -> begin
(let _52_2566 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_52_2566) with
| (head, args) -> begin
(match ((let _118_1987 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _118_1987.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _52_2572 = (encode_args args env')
in (match (_52_2572) with
| (encoded_args, arg_decls) -> begin
(let _52_2596 = (Microsoft_FStar_List.fold_left (fun _52_2576 arg -> (match (_52_2576) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Microsoft_FStar_Util.Inl (targ) -> begin
(let _52_2584 = (let _118_1990 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _118_1990))
in (match (_52_2584) with
| (_52_2581, tv, env) -> begin
(let _118_1992 = (let _118_1991 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_118_1991)::eqns)
in (env, (tv)::arg_vars, _118_1992))
end))
end
| Microsoft_FStar_Util.Inr (varg) -> begin
(let _52_2591 = (let _118_1993 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _118_1993))
in (match (_52_2591) with
| (_52_2588, xv, env) -> begin
(let _118_1995 = (let _118_1994 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_118_1994)::eqns)
in (env, (xv)::arg_vars, _118_1995))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_52_2596) with
| (_52_2593, arg_vars, eqns) -> begin
(let arg_vars = (Microsoft_FStar_List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _118_2002 = (let _118_2001 = (let _118_2000 = (let _118_1999 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Microsoft_FStar_List.append vars arg_binders))
in (let _118_1998 = (let _118_1997 = (let _118_1996 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Microsoft_FStar_List.append eqns guards))
in (ty_pred, _118_1996))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_1997))
in ((ty_pred)::[], _118_1999, _118_1998)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2000))
in (_118_2001, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2002))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _118_2003 = (varops.fresh "x")
in (_118_2003, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _118_2012 = (let _118_2011 = (let _118_2010 = (let _118_2009 = (let _118_2004 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_118_2004)::[])
in (let _118_2008 = (let _118_2007 = (let _118_2006 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _118_2005 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_118_2006, _118_2005)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_2007))
in (_118_2009, (x)::[], _118_2008)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2010))
in (_118_2011, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2012))))
end
| false -> begin
(let prec = (All.pipe_right vars (Microsoft_FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _118_2015 = (let _118_2014 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _118_2014 dapp))
in (_118_2015)::[])
end
| _52_2611 -> begin
(All.failwith "unexpected sort")
end))))
in (let _118_2022 = (let _118_2021 = (let _118_2020 = (let _118_2019 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Microsoft_FStar_List.append vars arg_binders))
in (let _118_2018 = (let _118_2017 = (let _118_2016 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _118_2016))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_2017))
in ((ty_pred)::[], _118_2019, _118_2018)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2020))
in (_118_2021, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2022)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _52_2615 -> begin
(let _52_2616 = (let _118_2025 = (let _118_2024 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _118_2023 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Microsoft_FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _118_2024 _118_2023)))
in (Microsoft_FStar_Tc_Errors.warn drange _118_2025))
in ([], []))
end)
end))
end))
in (let _52_2620 = (encode_elim ())
in (match (_52_2620) with
| (decls2, elim) -> begin
(let g = (let _118_2050 = (let _118_2049 = (let _118_2034 = (let _118_2033 = (let _118_2032 = (let _118_2031 = (let _118_2030 = (let _118_2029 = (let _118_2028 = (let _118_2027 = (let _118_2026 = (Microsoft_FStar_Absyn_Print.sli d)
in (Microsoft_FStar_Util.format1 "data constructor proxy: %s" _118_2026))
in Some (_118_2027))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _118_2028))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_2029))
in (_118_2030)::[])
in (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append binder_decls decls2) decls3) _118_2031))
in (Microsoft_FStar_List.append _118_2032 proxy_fresh))
in (Microsoft_FStar_List.append _118_2033 decls_formals))
in (Microsoft_FStar_List.append _118_2034 decls_pred))
in (let _118_2048 = (let _118_2047 = (let _118_2046 = (let _118_2038 = (let _118_2037 = (let _118_2036 = (let _118_2035 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _118_2035))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2036))
in (_118_2037, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2038))
in (let _118_2045 = (let _118_2044 = (let _118_2043 = (let _118_2042 = (let _118_2041 = (let _118_2040 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _118_2039 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _118_2040, _118_2039)))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2041))
in (_118_2042, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2043))
in (_118_2044)::[])
in (_118_2046)::_118_2045))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_118_2047)
in (Microsoft_FStar_List.append _118_2049 _118_2048)))
in (Microsoft_FStar_List.append _118_2050 elim))
in ((Microsoft_FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle (ses, _52_2624, _52_2626, _52_2628) -> begin
(let _52_2633 = (encode_signature env ses)
in (match (_52_2633) with
| (g, env) -> begin
(let _52_2645 = (All.pipe_right g (Microsoft_FStar_List.partition (fun _52_24 -> (match (_52_24) with
| Microsoft_FStar_ToSMT_Term.Assume (_52_2636, Some ("inversion axiom")) -> begin
false
end
| _52_2642 -> begin
true
end))))
in (match (_52_2645) with
| (g', inversions) -> begin
(let _52_2654 = (All.pipe_right g' (Microsoft_FStar_List.partition (fun _52_25 -> (match (_52_25) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2648) -> begin
true
end
| _52_2651 -> begin
false
end))))
in (match (_52_2654) with
| (decls, rest) -> begin
((Microsoft_FStar_List.append (Microsoft_FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (_52_2656, _52_2658, _52_2660, quals) when (All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _52_26 -> (match (_52_26) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _52_2672 -> begin
false
end)))) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _52_2677, _52_2679, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (Microsoft_FStar_List.length binders)
in (let _52_2691 = (Microsoft_FStar_Util.first_N nbinders formals)
in (match (_52_2691) with
| (formals, extra_formals) -> begin
(let subst = (Microsoft_FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (Microsoft_FStar_Util.Inl (a), Microsoft_FStar_Util.Inl (b)) -> begin
(let _118_2065 = (let _118_2064 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _118_2064))
in Microsoft_FStar_Util.Inl (_118_2065))
end
| (Microsoft_FStar_Util.Inr (x), Microsoft_FStar_Util.Inr (y)) -> begin
(let _118_2067 = (let _118_2066 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _118_2066))
in Microsoft_FStar_Util.Inr (_118_2067))
end
| _52_2705 -> begin
(All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _118_2068 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (All.pipe_right _118_2068 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _118_2074 = (let _118_2070 = (let _118_2069 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (All.pipe_left Prims.snd _118_2069))
in (body, _118_2070))
in (let _118_2073 = (let _118_2072 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (All.pipe_left (fun _118_2071 -> Some (_118_2071)) _118_2072))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _118_2074 _118_2073 body.Microsoft_FStar_Absyn_Syntax.pos)))
in ((Microsoft_FStar_List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun flid t_norm e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (binders, body); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _, _)) | (Microsoft_FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let nformals = (Microsoft_FStar_List.length formals)
in (let nbinders = (Microsoft_FStar_List.length binders)
in (let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (match (((nformals < nbinders) && (Microsoft_FStar_Absyn_Util.is_total_comp c))) with
| true -> begin
(let _52_2743 = (Microsoft_FStar_Util.first_N nformals binders)
in (match (_52_2743) with
| (bs0, rest) -> begin
(let tres = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tres)
end
| _52_2747 -> begin
(All.failwith "impossible")
end)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _52_2752 = (eta_expand binders formals body tres)
in (match (_52_2752) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _52_2754 -> begin
(let _118_2083 = (let _118_2082 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _118_2081 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Microsoft_FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _118_2082 _118_2081)))
in (All.failwith _118_2083))
end)
end
| _52_2756 -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _52_2764 = (eta_expand [] formals e tres)
in (match (_52_2764) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _52_2766 -> begin
([], e, [], t_norm)
end)
end))
in (All.try_with (fun _52_2768 -> (match (()) with
| () -> begin
(match ((All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _52_27 -> (match (_52_27) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2779 -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((All.pipe_right bindings (Microsoft_FStar_Util.for_some (fun lb -> (Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _118_2089 = (All.pipe_right bindings (Microsoft_FStar_List.collect (fun lb -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _118_2088 = (Microsoft_FStar_Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _118_2088 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(Prims.raise Let_rec_unencodeable)
end))))
in (_118_2089, env))
end
| false -> begin
(let _52_2799 = (All.pipe_right bindings (Microsoft_FStar_List.fold_left (fun _52_2786 lb -> (match (_52_2786) with
| (toks, typs, decls, env) -> begin
(let _52_2788 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| false -> begin
()
end)
in (let t_norm = (let _118_2092 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (All.pipe_right _118_2092 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _52_2794 = (let _118_2093 = (Microsoft_FStar_Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _118_2093 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_52_2794) with
| (tok, decl, env) -> begin
(let _118_2096 = (let _118_2095 = (let _118_2094 = (Microsoft_FStar_Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_118_2094, tok))
in (_118_2095)::toks)
in (_118_2096, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_52_2799) with
| (toks, typs, decls, env) -> begin
(let toks = (Microsoft_FStar_List.rev toks)
in (let decls = (All.pipe_right (Microsoft_FStar_List.rev decls) Microsoft_FStar_List.flatten)
in (let typs = (Microsoft_FStar_List.rev typs)
in (match (((All.pipe_right quals (Microsoft_FStar_Util.for_some (fun _52_28 -> (match (_52_28) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _52_2806 -> begin
false
end)))) || (All.pipe_right typs (Microsoft_FStar_Util.for_some (fun t -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _118_2099 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (All.pipe_left Prims.op_Negation _118_2099)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({Microsoft_FStar_Absyn_Syntax.lbname = _52_2814; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2812; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2810; Microsoft_FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _52_2830 = (destruct_bound_function flid t_norm e)
in (match (_52_2830) with
| (binders, body, formals, tres) -> begin
(let _52_2837 = (encode_binders None binders env)
in (match (_52_2837) with
| (vars, guards, env', binder_decls, _52_2836) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_2840 -> begin
(let _118_2101 = (let _118_2100 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _118_2100))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_2101))
end)
in (let _52_2844 = (encode_exp body env')
in (match (_52_2844) with
| (body, decls2) -> begin
(let eqn = (let _118_2110 = (let _118_2109 = (let _118_2106 = (let _118_2105 = (let _118_2104 = (let _118_2103 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _118_2102 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_118_2103, _118_2102)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_2104))
in ((app)::[], vars, _118_2105))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2106))
in (let _118_2108 = (let _118_2107 = (Microsoft_FStar_Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_118_2107))
in (_118_2109, _118_2108)))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2110))
in ((Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _52_2847 -> begin
(All.failwith "Impossible")
end)
end
| false -> begin
(let fuel = (let _118_2111 = (varops.fresh "fuel")
in (_118_2111, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _52_2864 = (All.pipe_right toks (Microsoft_FStar_List.fold_left (fun _52_2853 _52_2858 -> (match ((_52_2853, _52_2858)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _118_2116 = (let _118_2115 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (All.pipe_left (fun _118_2114 -> Some (_118_2114)) _118_2115))
in (push_free_var env flid gtok _118_2116))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_52_2864) with
| (gtoks, env) -> begin
(let gtoks = (Microsoft_FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _52_2873 t_norm _52_2882 -> (match ((_52_2873, _52_2882)) with
| ((flid, f, ftok, g, gtok), {Microsoft_FStar_Absyn_Syntax.lbname = _52_2881; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2879; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2877; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _52_2887 = (destruct_bound_function flid t_norm e)
in (match (_52_2887) with
| (binders, body, formals, tres) -> begin
(let _52_2894 = (encode_binders None binders env)
in (match (_52_2894) with
| (vars, guards, env', binder_decls, _52_2893) -> begin
(let decl_g = (let _118_2127 = (let _118_2126 = (let _118_2125 = (Microsoft_FStar_List.map Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_118_2125)
in (g, _118_2126, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_2127))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _118_2130 = (let _118_2129 = (let _118_2128 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_118_2128)::vars_tm)
in (g, _118_2129))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_2130))
in (let gmax = (let _118_2133 = (let _118_2132 = (let _118_2131 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_118_2131)::vars_tm)
in (g, _118_2132))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_2133))
in (let _52_2904 = (encode_exp body env')
in (match (_52_2904) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _118_2142 = (let _118_2141 = (let _118_2138 = (let _118_2137 = (let _118_2136 = (let _118_2135 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _118_2134 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_118_2135, _118_2134)))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_2136))
in ((gsapp)::[], (fuel)::vars, _118_2137))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2138))
in (let _118_2140 = (let _118_2139 = (Microsoft_FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_118_2139))
in (_118_2141, _118_2140)))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2142))
in (let eqn_f = (let _118_2146 = (let _118_2145 = (let _118_2144 = (let _118_2143 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _118_2143))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2144))
in (_118_2145, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2146))
in (let eqn_g' = (let _118_2155 = (let _118_2154 = (let _118_2153 = (let _118_2152 = (let _118_2151 = (let _118_2150 = (let _118_2149 = (let _118_2148 = (let _118_2147 = (Microsoft_FStar_ToSMT_Term.n_fuel 0)
in (_118_2147)::vars_tm)
in (g, _118_2148))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_2149))
in (gsapp, _118_2150))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_2151))
in ((gsapp)::[], (fuel)::vars, _118_2152))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2153))
in (_118_2154, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2155))
in (let _52_2927 = (let _52_2914 = (encode_binders None formals env0)
in (match (_52_2914) with
| (vars, v_guards, env, binder_decls, _52_2913) -> begin
(let vars_tm = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _118_2156 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _118_2156 ((fuel)::vars)))
in (let _118_2160 = (let _118_2159 = (let _118_2158 = (let _118_2157 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _118_2157))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2158))
in (_118_2159, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2160)))
in (let _52_2924 = (let _52_2921 = (encode_typ_pred None tres env gapp)
in (match (_52_2921) with
| (g_typing, d3) -> begin
(let _118_2168 = (let _118_2167 = (let _118_2166 = (let _118_2165 = (let _118_2164 = (let _118_2163 = (let _118_2162 = (let _118_2161 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_118_2161, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _118_2162))
in ((gapp)::[], (fuel)::vars, _118_2163))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2164))
in (_118_2165, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2166))
in (_118_2167)::[])
in (d3, _118_2168))
end))
in (match (_52_2924) with
| (aux_decls, typing_corr) -> begin
((Microsoft_FStar_List.append binder_decls aux_decls), (Microsoft_FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_52_2927) with
| (aux_decls, g_typing) -> begin
((Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Microsoft_FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _52_2943 = (let _118_2171 = (Microsoft_FStar_List.zip3 gtoks typs bindings)
in (Microsoft_FStar_List.fold_left (fun _52_2931 _52_2935 -> (match ((_52_2931, _52_2935)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _52_2939 = (encode_one_binding env0 gtok ty bs)
in (match (_52_2939) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Microsoft_FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _118_2171))
in (match (_52_2943) with
| (decls, eqns, env0) -> begin
(let _52_2952 = (let _118_2173 = (All.pipe_right decls Microsoft_FStar_List.flatten)
in (All.pipe_right _118_2173 (Microsoft_FStar_List.partition (fun _52_29 -> (match (_52_29) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2946) -> begin
true
end
| _52_2949 -> begin
false
end)))))
in (match (_52_2952) with
| (prefix_decls, rest) -> begin
(let eqns = (Microsoft_FStar_List.rev eqns)
in ((Microsoft_FStar_List.append (Microsoft_FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end)
end))))
end))
end)
end)
end)) (fun _52_2767 -> (match (_52_2767) with
| Let_rec_unencodeable -> begin
(let msg = (let _118_2176 = (All.pipe_right bindings (Microsoft_FStar_List.map (fun lb -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (All.pipe_right _118_2176 (Microsoft_FStar_String.concat " and ")))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _52_2979 = (encode_free_var env x t t_norm [])
in (match (_52_2979) with
| (decls, env) -> begin
(let _52_2984 = (lookup_lid env x)
in (match (_52_2984) with
| (n, x', _52_2983) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _52_2988) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _52_2996 = (encode_function_type_as_formula None t env)
in (match (_52_2996) with
| (form, decls) -> begin
(Microsoft_FStar_List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> (match (((let _118_2189 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (All.pipe_left Prims.op_Negation _118_2189)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _52_3005 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_3005) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (binders, _52_3008) -> begin
(All.pipe_right binders (Microsoft_FStar_List.map (fun _52_30 -> (match (_52_30) with
| (Microsoft_FStar_Util.Inl (_52_3013), _52_3016) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3019 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
end
| _52_3021 -> begin
[]
end)
in (let d = Microsoft_FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end
| false -> begin
(match ((prims.is lid)) with
| true -> begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end
| false -> begin
(let encode_non_total_function_typ = (lid.Microsoft_FStar_Absyn_Syntax.nsstr <> "Prims")
in (let _52_3038 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _118_2191 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _118_2191))
end
| false -> begin
(args, (None, (Microsoft_FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_52_3038) with
| (formals, (pre_opt, res_t)) -> begin
(let _52_3042 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_3042) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_3045 -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (All.pipe_right quals (Microsoft_FStar_List.collect (fun _52_31 -> (match (_52_31) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _52_3061 = (Microsoft_FStar_Util.prefix vars)
in (match (_52_3061) with
| (_52_3056, (xxsym, _52_3059)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _118_2208 = (let _118_2207 = (let _118_2206 = (let _118_2205 = (let _118_2204 = (let _118_2203 = (let _118_2202 = (let _118_2201 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _118_2201))
in (vapp, _118_2202))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_2203))
in ((vapp)::[], vars, _118_2204))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2205))
in (_118_2206, Some ("Discriminator equation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2207))
in (_118_2208)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector (d, Microsoft_FStar_Util.Inr (f)) -> begin
(let _52_3074 = (Microsoft_FStar_Util.prefix vars)
in (match (_52_3074) with
| (_52_3069, (xxsym, _52_3072)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _118_2210 = (let _118_2209 = (mk_term_projector_name d f)
in (_118_2209, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_2210))
in (let _118_2215 = (let _118_2214 = (let _118_2213 = (let _118_2212 = (let _118_2211 = (Microsoft_FStar_ToSMT_Term.mkEq (vapp, prim_app))
in ((vapp)::[], vars, _118_2211))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2212))
in (_118_2213, Some ("Projector equation")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2214))
in (_118_2215)::[])))
end))
end
| _52_3078 -> begin
[]
end)))))
in (let _52_3085 = (encode_binders None formals env)
in (match (_52_3085) with
| (vars, guards, env', decls1, _52_3084) -> begin
(let _52_3094 = (match (pre_opt) with
| None -> begin
(let _118_2216 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_118_2216, decls1))
end
| Some (p) -> begin
(let _52_3091 = (encode_formula p env')
in (match (_52_3091) with
| (g, ds) -> begin
(let _118_2217 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_118_2217, (Microsoft_FStar_List.append decls1 ds)))
end))
end)
in (match (_52_3094) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _118_2219 = (let _118_2218 = (Microsoft_FStar_List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _118_2218))
in (Microsoft_FStar_ToSMT_Term.mkApp _118_2219))
in (let _52_3125 = (let vname_decl = (let _118_2222 = (let _118_2221 = (All.pipe_right formals (Microsoft_FStar_List.map (fun _52_32 -> (match (_52_32) with
| (Microsoft_FStar_Util.Inl (_52_3099), _52_3102) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3105 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _118_2221, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_2222))
in (let _52_3112 = (let env = (let _52_3107 = env
in {bindings = _52_3107.bindings; depth = _52_3107.depth; tcenv = _52_3107.tcenv; warn = _52_3107.warn; cache = _52_3107.cache; nolabels = _52_3107.nolabels; use_zfuel_name = _52_3107.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred None t_norm env vtok_tm)
end))
in (match (_52_3112) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _52_3122 = (match (formals) with
| [] -> begin
(let _118_2226 = (let _118_2225 = (let _118_2224 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (All.pipe_left (fun _118_2223 -> Some (_118_2223)) _118_2224))
in (push_free_var env lid vname _118_2225))
in ((Microsoft_FStar_List.append decls2 ((tok_typing)::[])), _118_2226))
end
| _52_3116 -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _118_2227 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _118_2227))
in (let name_tok_corr = (let _118_2231 = (let _118_2230 = (let _118_2229 = (let _118_2228 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _118_2228))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2229))
in (_118_2230, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2231))
in ((Microsoft_FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_52_3122) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_52_3125) with
| (decls2, env) -> begin
(let _52_3133 = (let res_t = (Microsoft_FStar_Absyn_Util.compress_typ res_t)
in (let _52_3129 = (encode_typ_term res_t env')
in (match (_52_3129) with
| (encoded_res_t, decls) -> begin
(let _118_2232 = (Microsoft_FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _118_2232, decls))
end)))
in (match (_52_3133) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _118_2236 = (let _118_2235 = (let _118_2234 = (let _118_2233 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _118_2233))
in (Microsoft_FStar_ToSMT_Term.mkForall _118_2234))
in (_118_2235, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2236))
in (let g = (let _118_2238 = (let _118_2237 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_118_2237)
in (Microsoft_FStar_List.append (Microsoft_FStar_List.append (Microsoft_FStar_List.append decls1 decls2) decls3) _118_2238))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun env ses -> (All.pipe_right ses (Microsoft_FStar_List.fold_left (fun _52_3140 se -> (match (_52_3140) with
| (g, env) -> begin
(let _52_3144 = (encode_sigelt env se)
in (match (_52_3144) with
| (g', env) -> begin
((Microsoft_FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _52_3151 -> (match (_52_3151) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _52_3159 = (new_term_constant env x)
in (match (_52_3159) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.EtaArgs)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _52_3161 = (match ((All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _118_2253 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _118_2252 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _118_2251 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Microsoft_FStar_Util.fprint3 "Normalized %s : %s to %s\n" _118_2253 _118_2252 _118_2251))))
end
| false -> begin
()
end)
in (let _52_3165 = (encode_typ_pred None t1 env xx)
in (match (_52_3165) with
| (t, decls') -> begin
(let caption = (match ((ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _118_2257 = (let _118_2256 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _118_2255 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _118_2254 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Microsoft_FStar_Util.format3 "%s : %s (%s)" _118_2256 _118_2255 _118_2254))))
in Some (_118_2257))
end
| false -> begin
None
end)
in (let g = (Microsoft_FStar_List.append (Microsoft_FStar_List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((xxsym, [], Microsoft_FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((Microsoft_FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((Microsoft_FStar_List.append decls g), env')))
end))))
end))
end
| Microsoft_FStar_Tc_Env.Binding_typ (a, k) -> begin
(let _52_3175 = (new_typ_constant env a)
in (match (_52_3175) with
| (aasym, aa, env') -> begin
(let _52_3178 = (encode_knd k env aa)
in (match (_52_3178) with
| (k, decls') -> begin
(let g = (let _118_2263 = (let _118_2262 = (let _118_2261 = (let _118_2260 = (let _118_2259 = (let _118_2258 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_118_2258))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _118_2259))
in Microsoft_FStar_ToSMT_Term.DeclFun (_118_2260))
in (_118_2261)::[])
in (Microsoft_FStar_List.append _118_2262 decls'))
in (Microsoft_FStar_List.append _118_2263 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Microsoft_FStar_List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _52_3187 = (encode_free_var env x t t_norm [])
in (match (_52_3187) with
| (g, env') -> begin
((Microsoft_FStar_List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _52_3192 = (encode_sigelt env se)
in (match (_52_3192) with
| (g, env') -> begin
((Microsoft_FStar_List.append decls g), env')
end))
end)
end))
in (Microsoft_FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (All.pipe_right labs (Microsoft_FStar_List.map (fun _52_3199 -> (match (_52_3199) with
| (l, _52_3196, _52_3198) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (All.pipe_right labs (Microsoft_FStar_List.collect (fun _52_3206 -> (match (_52_3206) with
| (l, _52_3203, _52_3205) -> begin
(let _118_2271 = (All.pipe_left (fun _118_2267 -> Microsoft_FStar_ToSMT_Term.Echo (_118_2267)) (Prims.fst l))
in (let _118_2270 = (let _118_2269 = (let _118_2268 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_118_2268))
in (_118_2269)::[])
in (_118_2271)::_118_2270))
end))))
in (prefix, suffix))))

let last_env = (Microsoft_FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _118_2276 = (let _118_2275 = (let _118_2274 = (Microsoft_FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _118_2274; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_118_2275)::[])
in (ST.op_Colon_Equals last_env _118_2276)))

let get_env = (fun tcenv -> (match ((ST.read last_env)) with
| [] -> begin
(All.failwith "No env; call init first!")
end
| e::_52_3212 -> begin
(let _52_3215 = e
in {bindings = _52_3215.bindings; depth = _52_3215.depth; tcenv = tcenv; warn = _52_3215.warn; cache = _52_3215.cache; nolabels = _52_3215.nolabels; use_zfuel_name = _52_3215.use_zfuel_name; encode_non_total_function_typ = _52_3215.encode_non_total_function_typ})
end))

let set_env = (fun env -> (match ((ST.read last_env)) with
| [] -> begin
(All.failwith "Empty env stack")
end
| _52_3221::tl -> begin
(ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun _52_3223 -> (match (()) with
| () -> begin
(match ((ST.read last_env)) with
| [] -> begin
(All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (Microsoft_FStar_Util.smap_copy hd.cache)
in (let top = (let _52_3229 = hd
in {bindings = _52_3229.bindings; depth = _52_3229.depth; tcenv = _52_3229.tcenv; warn = _52_3229.warn; cache = refs; nolabels = _52_3229.nolabels; use_zfuel_name = _52_3229.use_zfuel_name; encode_non_total_function_typ = _52_3229.encode_non_total_function_typ})
in (ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun _52_3232 -> (match (()) with
| () -> begin
(match ((ST.read last_env)) with
| [] -> begin
(All.failwith "Popping an empty stack")
end
| _52_3236::tl -> begin
(ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun _52_3238 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _52_3239 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _52_3240 -> (match (()) with
| () -> begin
(match ((ST.read last_env)) with
| hd::_52_3243::tl -> begin
(ST.op_Colon_Equals last_env ((hd)::tl))
end
| _52_3248 -> begin
(All.failwith "Impossible")
end)
end))

let init = (fun tcenv -> (let _52_3250 = (init_env tcenv)
in (let _52_3252 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _52_3255 = (push_env ())
in (let _52_3257 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _52_3260 = (let _118_2297 = (pop_env ())
in (All.pipe_left Prims.ignore _118_2297))
in (let _52_3262 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _52_3265 = (mark_env ())
in (let _52_3267 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _52_3270 = (reset_mark_env ())
in (let _52_3272 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _52_3275 = (commit_mark_env ())
in (let _52_3277 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> (match ((ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _118_2311 = (let _118_2310 = (let _118_2309 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _118_2309))
in Microsoft_FStar_ToSMT_Term.Caption (_118_2310))
in (_118_2311)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _52_3286 = (encode_sigelt env se)
in (match (_52_3286) with
| (decls, env) -> begin
(let _52_3287 = (set_env env)
in (let _118_2312 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _118_2312)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (Microsoft_FStar_Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_3292 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_2317 = (All.pipe_right (Microsoft_FStar_List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Microsoft_FStar_Util.string_of_int)
in (Microsoft_FStar_Util.fprint2 "Encoding externals for %s ... %s exports\n" name _118_2317))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _52_3299 = (encode_signature (let _52_3295 = env
in {bindings = _52_3295.bindings; depth = _52_3295.depth; tcenv = _52_3295.tcenv; warn = false; cache = _52_3295.cache; nolabels = _52_3295.nolabels; use_zfuel_name = _52_3295.use_zfuel_name; encode_non_total_function_typ = _52_3295.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_52_3299) with
| (decls, env) -> begin
(let caption = (fun decls -> (match ((ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Prims.strcat "Externals for " name)
in (Microsoft_FStar_List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _52_3305 = (set_env (let _52_3303 = env
in {bindings = _52_3303.bindings; depth = _52_3303.depth; tcenv = _52_3303.tcenv; warn = true; cache = _52_3303.cache; nolabels = _52_3303.nolabels; use_zfuel_name = _52_3303.use_zfuel_name; encode_non_total_function_typ = _52_3303.encode_non_total_function_typ}))
in (let _52_3307 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Microsoft_FStar_Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _52_3312 = (let _118_2326 = (let _118_2325 = (let _118_2324 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (All.pipe_left Microsoft_FStar_Range.string_of_range _118_2324))
in (Microsoft_FStar_Util.format1 "Starting query at %s" _118_2325))
in (push _118_2326))
in (let pop = (fun _52_3315 -> (match (()) with
| () -> begin
(let _118_2331 = (let _118_2330 = (let _118_2329 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (All.pipe_left Microsoft_FStar_Range.string_of_range _118_2329))
in (Microsoft_FStar_Util.format1 "Ending query at %s" _118_2330))
in (pop _118_2331))
end))
in (let _52_3345 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _52_3328 = (let _118_2335 = (Microsoft_FStar_List.filter (fun _52_33 -> (match (_52_33) with
| Microsoft_FStar_Tc_Env.Binding_sig (_52_3322) -> begin
false
end
| _52_3325 -> begin
true
end)) bindings)
in (encode_env_bindings env _118_2335))
in (match (_52_3328) with
| (env_decls, env) -> begin
(let _52_3329 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _118_2336 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Microsoft_FStar_Util.fprint1 "Encoding query formula: %s\n" _118_2336))
end
| false -> begin
()
end)
in (let _52_3334 = (encode_formula_with_labels q env)
in (match (_52_3334) with
| (phi, labels, qdecls) -> begin
(let _52_3337 = (encode_labels labels)
in (match (_52_3337) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Microsoft_FStar_List.append (Microsoft_FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _118_2338 = (let _118_2337 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_118_2337, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2338))
in (let suffix = (Microsoft_FStar_List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_52_3345) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume ({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.False, _52_3352); Microsoft_FStar_ToSMT_Term.hash = _52_3349; Microsoft_FStar_ToSMT_Term.freevars = _52_3347}, _52_3357) -> begin
(let _52_3360 = (pop ())
in ())
end
| _52_3363 when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _52_3364 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume (q, _52_3368) -> begin
(let fresh = ((Microsoft_FStar_String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _52_3372 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _52_3378 -> (match (_52_3378) with
| (n, i) -> begin
(let _118_2361 = (let _118_2360 = (let _118_2345 = (let _118_2344 = (Microsoft_FStar_Util.string_of_int n)
in (let _118_2343 = (Microsoft_FStar_Util.string_of_int i)
in (Microsoft_FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _118_2344 _118_2343)))
in Microsoft_FStar_ToSMT_Term.Caption (_118_2345))
in (let _118_2359 = (let _118_2358 = (let _118_2350 = (let _118_2349 = (let _118_2348 = (let _118_2347 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _118_2346 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_118_2347, _118_2346)))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_2348))
in (_118_2349, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2350))
in (let _118_2357 = (let _118_2356 = (let _118_2355 = (let _118_2354 = (let _118_2353 = (let _118_2352 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _118_2351 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_118_2352, _118_2351)))
in (Microsoft_FStar_ToSMT_Term.mkEq _118_2353))
in (_118_2354, None))
in Microsoft_FStar_ToSMT_Term.Assume (_118_2355))
in (_118_2356)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_118_2358)::_118_2357))
in (_118_2360)::_118_2359))
in (Microsoft_FStar_List.append _118_2361 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _118_2365 = (ST.read Microsoft_FStar_Options.initial_fuel)
in (let _118_2364 = (ST.read Microsoft_FStar_Options.initial_ifuel)
in (_118_2365, _118_2364)))
in (let alt_configs = (let _118_2384 = (let _118_2383 = (match (((ST.read Microsoft_FStar_Options.max_ifuel) > (ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _118_2368 = (let _118_2367 = (ST.read Microsoft_FStar_Options.initial_fuel)
in (let _118_2366 = (ST.read Microsoft_FStar_Options.max_ifuel)
in (_118_2367, _118_2366)))
in (_118_2368)::[])
end
| false -> begin
[]
end)
in (let _118_2382 = (let _118_2381 = (match ((((ST.read Microsoft_FStar_Options.max_fuel) / 2) > (ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _118_2371 = (let _118_2370 = ((ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _118_2369 = (ST.read Microsoft_FStar_Options.max_ifuel)
in (_118_2370, _118_2369)))
in (_118_2371)::[])
end
| false -> begin
[]
end)
in (let _118_2380 = (let _118_2379 = (match ((((ST.read Microsoft_FStar_Options.max_fuel) > (ST.read Microsoft_FStar_Options.initial_fuel)) && ((ST.read Microsoft_FStar_Options.max_ifuel) > (ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _118_2374 = (let _118_2373 = (ST.read Microsoft_FStar_Options.max_fuel)
in (let _118_2372 = (ST.read Microsoft_FStar_Options.max_ifuel)
in (_118_2373, _118_2372)))
in (_118_2374)::[])
end
| false -> begin
[]
end)
in (let _118_2378 = (let _118_2377 = (match (((ST.read Microsoft_FStar_Options.min_fuel) < (ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _118_2376 = (let _118_2375 = (ST.read Microsoft_FStar_Options.min_fuel)
in (_118_2375, 1))
in (_118_2376)::[])
end
| false -> begin
[]
end)
in (_118_2377)::[])
in (_118_2379)::_118_2378))
in (_118_2381)::_118_2380))
in (_118_2383)::_118_2382))
in (Microsoft_FStar_List.flatten _118_2384))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", Microsoft_FStar_Absyn_Syntax.dummyRange))::[]
end
| _52_3387 -> begin
errs
end)
in (let _52_3389 = (match ((ST.read Microsoft_FStar_Options.print_fuels)) with
| true -> begin
(let _118_2392 = (let _118_2387 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Microsoft_FStar_Range.string_of_range _118_2387))
in (let _118_2391 = (let _118_2388 = (ST.read Microsoft_FStar_Options.max_fuel)
in (All.pipe_right _118_2388 Microsoft_FStar_Util.string_of_int))
in (let _118_2390 = (let _118_2389 = (ST.read Microsoft_FStar_Options.max_ifuel)
in (All.pipe_right _118_2389 Microsoft_FStar_Util.string_of_int))
in (Microsoft_FStar_Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _118_2392 _118_2391 _118_2390))))
end
| false -> begin
()
end)
in (Microsoft_FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _52_34 -> (match (_52_34) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _118_2403 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _118_2403 (cb mi p [])))
end
| _52_3401 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _118_2405 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _118_2405 (fun _52_3407 -> (match (_52_3407) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _52_3410 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _52_3413 p alt _52_3418 -> (match ((_52_3413, _52_3418)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
(match (ok) with
| true -> begin
(match ((ST.read Microsoft_FStar_Options.print_fuels)) with
| true -> begin
(let _118_2413 = (let _118_2410 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Microsoft_FStar_Range.string_of_range _118_2410))
in (let _118_2412 = (Microsoft_FStar_Util.string_of_int prev_fuel)
in (let _118_2411 = (Microsoft_FStar_Util.string_of_int prev_ifuel)
in (Microsoft_FStar_Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _118_2413 _118_2412 _118_2411))))
end
| false -> begin
()
end)
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _118_2414 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _118_2414 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> (match (((ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _52_3423 = (let _118_2420 = (ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _118_2420 q))
in (match (_52_3423) with
| (b, cb) -> begin
(match (b) with
| true -> begin
(Microsoft_FStar_ToSMT_SplitQueryCases.handle_query cb check)
end
| false -> begin
(check q)
end)
end))
end
| false -> begin
(check q)
end))
in (let _52_3424 = (match ((ST.read Microsoft_FStar_Options.admit_smt_queries)) with
| true -> begin
()
end
| false -> begin
(process_query qry)
end)
in (pop ())))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _52_3429 = (push "query")
in (let _52_3436 = (encode_formula_with_labels q env)
in (match (_52_3436) with
| (f, _52_3433, _52_3435) -> begin
(let _52_3437 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App (Microsoft_FStar_ToSMT_Term.True, _52_3441) -> begin
true
end
| _52_3445 -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun _52_3446 -> ()); Microsoft_FStar_Tc_Env.push = (fun _52_3448 -> ()); Microsoft_FStar_Tc_Env.pop = (fun _52_3450 -> ()); Microsoft_FStar_Tc_Env.mark = (fun _52_3452 -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun _52_3454 -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun _52_3456 -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun _52_3458 _52_3460 -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun _52_3462 _52_3464 -> ()); Microsoft_FStar_Tc_Env.solve = (fun _52_3466 _52_3468 -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun _52_3470 _52_3472 -> false); Microsoft_FStar_Tc_Env.finish = (fun _52_3474 -> ()); Microsoft_FStar_Tc_Env.refresh = (fun _52_3475 -> ())}




